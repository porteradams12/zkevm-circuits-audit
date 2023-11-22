use super::*;

use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;

use arrayvec::ArrayVec;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::curves::sw_projective::SWProjectivePoint;

use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;

use boojum::gadgets::u160::UInt160;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

use crate::ecrecover::baseline::convert_uint256_to_field_element;
use crate::ecrecover::baseline::convert_uint256_to_field_element_masked;

#[derive(Derivative, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct Secp256r1VerifyPrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_offset: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_offset: UInt32<F>,
}

impl<F: SmallField> Secp256r1VerifyPrecompileCallParams<F> {
    pub fn from_encoding<CS: ConstraintSystem<F>>(_cs: &mut CS, encoding: UInt256<F>) -> Self {
        let input_offset = encoding.inner[0];
        let output_offset = encoding.inner[2];
        let input_page = encoding.inner[4];
        let output_page = encoding.inner[5];

        let new = Self {
            input_page,
            input_offset,
            output_page,
            output_offset,
        };

        new
    }
}

const NUM_WORDS: usize = 17;
const EXCEPTION_FLAGS_ARR_LEN: usize = 8;

fn secp256r1_verify_function_inner<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    r: &UInt256<F>,
    s: &UInt256<F>,
    message_hash: &UInt256<F>,
    x: &UInt256<F>,
    y: &UInt256<F>,
    base_field_params: &Arc<Secp256BaseNNFieldParams>,
    scalar_field_params: &Arc<Secp256ScalarNNFieldParams>,
) -> (Boolean<F>, UInt256<F>) {
    use boojum::pairing::GenericCurveAffine;
    let curve_a = Secp256Affine::a_coeff();
    let curve_b = Secp256Affine::b_coeff();

    let mut curve_a_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, curve_a, &base_field_params);
    let mut curve_b_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, curve_b, &base_field_params);

    let generator = Secp256Affine::one();
    let (gen_x, gen_y) = generator.into_xy_unchecked();
    let gen_x_nn = Secp256BaseNNField::allocated_constant(cs, gen_x, base_field_params);
    let gen_y_nn = Secp256BaseNNField::allocated_constant(cs, gen_y, base_field_params);

    let secp_n_u256 = U256([
        scalar_field_params.modulus_u1024.as_ref().as_words()[0],
        scalar_field_params.modulus_u1024.as_ref().as_words()[1],
        scalar_field_params.modulus_u1024.as_ref().as_words()[2],
        scalar_field_params.modulus_u1024.as_ref().as_words()[3],
    ]);
    let secp_n_u256 = UInt256::allocated_constant(cs, secp_n_u256);

    let secp_p_u256 = U256([
        base_field_params.modulus_u1024.as_ref().as_words()[0],
        base_field_params.modulus_u1024.as_ref().as_words()[1],
        base_field_params.modulus_u1024.as_ref().as_words()[2],
        base_field_params.modulus_u1024.as_ref().as_words()[3],
    ]);
    let secp_p_u256 = UInt256::allocated_constant(cs, secp_p_u256);

    let mut exception_flags = ArrayVec::<_, EXCEPTION_FLAGS_ARR_LEN>::new();

    // we use non-compressed point, so we:
    // - check that public key is on curve (no special handling of zeroes)
    // - check verification equation

    // we check ranges upfront. We only need to check <modulus, and conversion functions will perform masking internally for values that are >= 1

    let mut r_as_u256 = *r;
    let mut s_as_u256 = *s;
    let mut x_as_u256 = *x;
    let mut y_as_u256 = *y;

    let (_res, is_in_range) = r_as_u256.overflowing_sub(cs, &secp_n_u256);
    r_as_u256 = r_as_u256.mask(cs, is_in_range);
    let r_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(r_is_not_in_range);

    let (_res, is_in_range) = s_as_u256.overflowing_sub(cs, &secp_n_u256);
    s_as_u256 = s_as_u256.mask(cs, is_in_range);
    let s_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(s_is_not_in_range);

    let (_res, is_in_range) = x_as_u256.overflowing_sub(cs, &secp_p_u256);
    x_as_u256 = x_as_u256.mask(cs, is_in_range);
    let x_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(x_is_not_in_range);

    let (_res, is_in_range) = y_as_u256.overflowing_sub(cs, &secp_p_u256);
    y_as_u256 = y_as_u256.mask(cs, is_in_range);
    let y_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(y_is_not_in_range);

    let mut x_fe = convert_uint256_to_field_element(cs, &x_as_u256, &base_field_params);
    let mut y_fe = convert_uint256_to_field_element(cs, &y_as_u256, &base_field_params);

    let (mut r_fe, r_is_zero) =
        convert_uint256_to_field_element_masked(cs, &r_as_u256, &scalar_field_params);
    exception_flags.push(r_is_zero);
    let (mut s_fe, s_is_zero) =
        convert_uint256_to_field_element_masked(cs, &s_as_u256, &scalar_field_params);
    exception_flags.push(s_is_zero);

    let mut message_hash_fe =
        convert_uint256_to_field_element(cs, &message_hash, &scalar_field_params);

    // perform on-curve check
    let mut lhs = y_fe.clone();
    let mut lhs = lhs.mul(cs, &mut y_fe);
    lhs.normalize(cs);

    let mut rhs = x_fe.clone();
    let mut rhs = rhs.mul(cs, &mut x_fe);
    let mut rhs = rhs.add(cs, &mut curve_a_nn);
    let mut rhs = rhs.mul(cs, &mut x_fe);
    let mut rhs = rhs.add(cs, &mut curve_b_nn);
    rhs.normalize(cs);

    let is_on_curve = NonNativeFieldOverU16::equals(cs, &mut lhs, &mut rhs);
    let not_on_curve = is_on_curve.negated(cs);
    exception_flags.push(not_on_curve);

    // we can mask point to ensure that our arithmetic formulas work
    let x_fe: NonNativeFieldOverU16<F, Secp256Fq, 17> =
        NonNativeFieldOverU16::conditionally_select(cs, is_on_curve, &x_fe, &gen_x_nn);
    let y_fe = NonNativeFieldOverU16::conditionally_select(cs, is_on_curve, &y_fe, &gen_y_nn);

    // this always exists (0 was an exception and was masked)
    let mut s_fe_inversed = s_fe.inverse_unchecked(cs);
    let mut r_by_s_inv = r_fe.mul(cs, &mut s_fe_inversed);
    let mut message_hash_by_s_inv = message_hash_fe.mul(cs, &mut s_fe_inversed);

    r_by_s_inv.normalize(cs);
    message_hash_by_s_inv.normalize(cs);

    let r_by_s_inv_normalized_lsb_bits: Vec<_> = r_by_s_inv
        .limbs
        .iter()
        .map(|el| Num::<F>::from_variable(*el).spread_into_bits::<_, 16>(cs))
        .flatten()
        .collect();
    let message_hash_by_s_inv_lsb_bits: Vec<_> = message_hash_by_s_inv
        .limbs
        .iter()
        .map(|el| Num::<F>::from_variable(*el).spread_into_bits::<_, 16>(cs))
        .flatten()
        .collect();

    let mut public_key = (x_fe, y_fe);
    let mut generator_point = (gen_x_nn, gen_y_nn);
    // now we do multiexponentiation
    let mut q_acc =
        SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::zero(cs, base_field_params);

    // we should start from MSB, double the accumulator, then conditionally add
    for (cycle, (x_bit, hash_bit)) in r_by_s_inv_normalized_lsb_bits
        .into_iter()
        .rev()
        .zip(message_hash_by_s_inv_lsb_bits.into_iter().rev())
        .enumerate()
    {
        if cycle != 0 {
            q_acc = q_acc.double(cs);
        }
        let q_plus_x = q_acc.add_mixed(cs, &mut public_key);
        let mut q_0: SWProjectivePoint<F, Secp256Affine, NonNativeFieldOverU16<F, Secp256Fq, 17>> =
            Selectable::conditionally_select(cs, x_bit, &q_plus_x, &q_acc);

        let q_plux_gen = q_0.add_mixed(cs, &mut generator_point);
        let q_1 = Selectable::conditionally_select(cs, hash_bit, &q_plux_gen, &q_0);

        q_acc = q_1;
    }

    let ((mut q_x, _q_y), is_infinity) =
        q_acc.convert_to_affine_or_default(cs, Secp256Affine::one());
    exception_flags.push(is_infinity);
    let any_exception = Boolean::multi_or(cs, &exception_flags[..]);

    q_x.normalize(cs);

    // now compare mod n. For that we go out of limbs and back
    let limbs = q_x.limbs;
    let mut q_x_mod_n = NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 2 }, // |Fr|*2 < |Fq|
        form: RepresentationForm::Normalized,
        params: scalar_field_params.clone(),
        _marker: std::marker::PhantomData,
    };
    q_x_mod_n.normalize(cs);

    let signature_equality = NonNativeFieldOverU16::equals(cs, &mut q_x_mod_n, &mut r_fe);
    let written_value_bool = signature_equality.mask_negated(cs, any_exception);
    let all_ok = any_exception.negated(cs);

    let mut written_value = UInt256::zero(cs);
    written_value.inner[0] =
        unsafe { UInt32::from_variable_unchecked(written_value_bool.get_variable()) };

    (all_ok, written_value)
}

pub fn secp256r1_verify_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: Secp256r1VerifyCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    assert!(limit <= u32::MAX as usize);

    let Secp256r1VerifyCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;

    let memory_reads_witness: VecDeque<_> = memory_reads_witness.into_iter().flatten().collect();

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::SECP256R1_VERIFY_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS,
    );
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    let scalar_params = Arc::new(secp256r1_scalar_field_params());
    let base_params = Arc::new(secp256r1_base_field_params());

    let mut structured_input =
        Secp256r1VerifyCircuitInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
    let start_flag = structured_input.start_flag;

    let requests_queue_state_from_input = structured_input.observable_input.initial_log_queue_state;

    // it must be trivial
    requests_queue_state_from_input.enforce_trivial_head(cs);

    let requests_queue_state_from_fsm = structured_input.hidden_fsm_input.log_queue_state;

    let requests_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &requests_queue_state_from_input,
        &requests_queue_state_from_fsm,
    );

    let memory_queue_state_from_input =
        structured_input.observable_input.initial_memory_queue_state;

    // it must be trivial
    memory_queue_state_from_input.enforce_trivial_head(cs);

    let memory_queue_state_from_fsm = structured_input.hidden_fsm_input.memory_queue_state;

    let memory_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &memory_queue_state_from_input,
        &memory_queue_state_from_fsm,
    );

    let mut requests_queue = StorageLogQueue::<F, R>::from_state(cs, requests_queue_state);
    let queue_witness = CircuitQueueWitness::from_inner_witness(requests_queue_witness);
    requests_queue.witness = Arc::new(queue_witness);

    let mut memory_queue = MemoryQueue::<F, R>::from_state(cs, memory_queue_state);

    let one_u32 = UInt32::allocated_constant(cs, 1u32);
    let zero_u256 = UInt256::zero(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);

    use crate::storage_application::ConditionalWitnessAllocator;
    let read_queries_allocator = ConditionalWitnessAllocator::<F, UInt256<F>> {
        witness_source: Arc::new(RwLock::new(memory_reads_witness)),
    };

    for _cycle in 0..limit {
        let is_empty = requests_queue.is_empty(cs);
        let should_process = is_empty.negated(cs);
        let (request, _) = requests_queue.pop_front(cs, should_process);

        let mut precompile_call_params =
            Secp256r1VerifyPrecompileCallParams::from_encoding(cs, request.key);

        let timestamp_to_use_for_read = request.timestamp;
        let timestamp_to_use_for_write = timestamp_to_use_for_read.add_no_overflow(cs, one_u32);

        Num::conditionally_enforce_equal(
            cs,
            should_process,
            &Num::from_variable(request.aux_byte.get_variable()),
            &Num::from_variable(aux_byte_for_precompile.get_variable()),
        );
        for (a, b) in request
            .address
            .inner
            .iter()
            .zip(precompile_address.inner.iter())
        {
            Num::conditionally_enforce_equal(
                cs,
                should_process,
                &Num::from_variable(a.get_variable()),
                &Num::from_variable(b.get_variable()),
            );
        }

        let mut read_values = [zero_u256; MEMORY_QUERIES_PER_CALL];
        let mut bias_variable = should_process.get_variable();
        for dst in read_values.iter_mut() {
            let read_query_value: UInt256<F> = read_queries_allocator
                .conditionally_allocate_biased(cs, should_process, bias_variable);
            bias_variable = read_query_value.inner[0].get_variable();

            *dst = read_query_value;

            let read_query = MemoryQuery {
                timestamp: timestamp_to_use_for_read,
                memory_page: precompile_call_params.input_page,
                index: precompile_call_params.input_offset,
                rw_flag: boolean_false,
                is_ptr: boolean_false,
                value: read_query_value,
            };

            let _ = memory_queue.push(cs, read_query, should_process);

            precompile_call_params.input_offset = precompile_call_params
                .input_offset
                .add_no_overflow(cs, one_u32);
        }

        let [message_hash_as_u256, r_as_u256, s_as_u256, x_as_u256, y_as_u256] = read_values;

        let (success, written_value) = secp256r1_verify_function_inner(
            cs,
            &r_as_u256,
            &s_as_u256,
            &message_hash_as_u256,
            &x_as_u256,
            &y_as_u256,
            &base_params,
            &scalar_params,
        );

        let success_as_u32 = unsafe { UInt32::from_variable_unchecked(success.get_variable()) };
        let mut success_as_u256 = zero_u256;
        success_as_u256.inner[0] = success_as_u32;

        let success_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            index: precompile_call_params.output_offset,
            rw_flag: boolean_true,
            value: success_as_u256,
            is_ptr: boolean_false,
        };

        precompile_call_params.output_offset = precompile_call_params
            .output_offset
            .add_no_overflow(cs, one_u32);

        let _ = memory_queue.push(cs, success_query, should_process);

        let value_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            index: precompile_call_params.output_offset,
            rw_flag: boolean_true,
            value: written_value,
            is_ptr: boolean_false,
        };

        let _ = memory_queue.push(cs, value_query, should_process);
    }

    requests_queue.enforce_consistency(cs);

    // form the final state
    let done = requests_queue.is_empty(cs);
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::placeholder(cs);

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();

    structured_input.observable_output.final_memory_state = QueueState::conditionally_select(
        cs,
        structured_input.completion_flag,
        &final_memory_state,
        &structured_input.observable_output.final_memory_state,
    );

    structured_input.hidden_fsm_output.log_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    use boojum::cs::gates::PublicInputGate;

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);
    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}

#[cfg(test)]
mod test {
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::traits::allocatable::CSAllocatable;
    use boojum::pairing::ff::{Field, PrimeField};
    use boojum::worker::Worker;

    use super::*;

    type F = GoldilocksField;
    type P = GoldilocksField;

    use boojum::config::DevCSConfig;

    use boojum::pairing::ff::PrimeFieldRepr;
    use boojum::pairing::{GenericCurveAffine, GenericCurveProjective};
    use rand::Rng;
    use rand::SeedableRng;
    use rand::XorShiftRng;

    pub fn deterministic_rng() -> XorShiftRng {
        XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654])
    }

    fn simulate_signature() -> (Secp256Fr, Secp256Fr, Secp256Affine, Secp256Fr) {
        let mut rng = deterministic_rng();
        let sk: Secp256Fr = rng.gen();

        simulate_signature_for_sk(sk)
    }

    fn transmute_representation<T: PrimeFieldRepr, U: PrimeFieldRepr>(repr: T) -> U {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<U>());

        unsafe { std::mem::transmute_copy::<T, U>(&repr) }
    }

    fn simulate_signature_for_sk(
        sk: Secp256Fr,
    ) -> (Secp256Fr, Secp256Fr, Secp256Affine, Secp256Fr) {
        let mut rng = deterministic_rng();
        let pk = Secp256Affine::one().mul(sk.into_repr()).into_affine();
        let digest: Secp256Fr = rng.gen();
        let k: Secp256Fr = rng.gen();
        let r_point = Secp256Affine::one().mul(k.into_repr()).into_affine();

        let r_x = r_point.into_xy_unchecked().0;
        let r = transmute_representation::<_, <Secp256Fr as PrimeField>::Repr>(r_x.into_repr());
        let r = Secp256Fr::from_repr(r).unwrap();

        let k_inv = k.inverse().unwrap();
        let mut s = r;
        s.mul_assign(&sk);
        s.add_assign(&digest);
        s.mul_assign(&k_inv);

        {
            let mut mul_by_generator = digest;
            mul_by_generator.mul_assign(&r.inverse().unwrap());
            mul_by_generator.negate();

            let mut mul_by_r = s;
            mul_by_r.mul_assign(&r.inverse().unwrap());

            let res_1 = Secp256Affine::one().mul(mul_by_generator.into_repr());
            let res_2 = r_point.mul(mul_by_r.into_repr());

            let mut tmp = res_1;
            tmp.add_assign(&res_2);

            let tmp = tmp.into_affine();

            let x = tmp.into_xy_unchecked().0;
            assert_eq!(x, pk.into_xy_unchecked().0);
        }

        (r, s, pk, digest)
    }

    fn repr_into_u256<T: PrimeFieldRepr>(repr: T) -> U256 {
        let mut u256 = U256::zero();
        u256.0.copy_from_slice(&repr.as_ref()[..4]);

        u256
    }

    use boojum::cs::cs_builder::*;
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::*;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::CSGeometry;
    use boojum::cs::*;
    use boojum::gadgets::tables::byte_split::ByteSplitTable;
    use boojum::gadgets::tables::*;

    #[test]
    fn test_signature_for_address_verification() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 100,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
        };
        let max_variables = 1 << 26;
        let max_trace_len = 1 << 20;

        fn configure<
            F: SmallField,
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: 8,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // let owned_cs = ReductionGate::<F, 4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 8, share_constants: true });
            let builder = BooleanConstraintGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<32>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<16>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = SelectionGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );
            let builder = DotProductGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // let owned_cs = DotProductGate::<4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 1, share_constants: true });
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl = CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(
            geometry,
            max_variables,
            max_trace_len,
        );
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let cs = &mut owned_cs;

        let sk = crate::ff::from_hex::<Secp256Fr>(
            "b5b1870957d373ef0eeffecc6e4812c0fd08f554b37b233526acc331bf1544f7",
        )
        .unwrap();
        let eth_address = hex::decode("12890d2cce102216644c59dae5baed380d84830c").unwrap();
        let (r, s, _pk, digest) = simulate_signature_for_sk(sk);

        let scalar_params = secp256r1_scalar_field_params();
        let base_params = secp256r1_base_field_params();

        let digest_u256 = repr_into_u256(digest.into_repr());
        let r_u256 = repr_into_u256(r.into_repr());
        let s_u256 = repr_into_u256(s.into_repr());

        let rec_id = UInt8::allocate_checked(cs, 0);
        let r = UInt256::allocate(cs, r_u256);
        let s = UInt256::allocate(cs, s_u256);
        let digest = UInt256::allocate(cs, digest_u256);

        let scalar_params = Arc::new(scalar_params);
        let base_params = Arc::new(base_params);

        let valid_x_in_external_field = Secp256BaseNNField::allocated_constant(
            cs,
            Secp256Fq::from_str("9").unwrap(),
            &base_params,
        );
        let valid_t_in_external_field = Secp256BaseNNField::allocated_constant(
            cs,
            Secp256Fq::from_str("16").unwrap(),
            &base_params,
        );
        let valid_y_in_external_field = Secp256BaseNNField::allocated_constant(
            cs,
            Secp256Fq::from_str("4").unwrap(),
            &base_params,
        );

        let (no_error, digest) = secp25(
            cs,
            &rec_id,
            &r,
            &s,
            &digest,
            valid_x_in_external_field.clone(),
            valid_y_in_external_field.clone(),
            valid_t_in_external_field.clone(),
            &base_params,
            &scalar_params,
        );

        assert!(no_error.witness_hook(&*cs)().unwrap() == true);
        let recovered_address = digest.to_be_bytes(cs);
        let recovered_address = recovered_address.witness_hook(cs)().unwrap();
        assert_eq!(&recovered_address[12..], &eth_address[..]);

        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
