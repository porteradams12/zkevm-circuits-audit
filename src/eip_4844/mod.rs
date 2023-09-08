use std::collections::VecDeque;
use std::mem::MaybeUninit;

use crate::base_structures::state_diff_record::StateDiffRecord;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::keccak256_round_function::keccak256_absorb_and_run_permutation;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::config::*;
use boojum::crypto_bigint::{Zero, U1024};
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::cs::traits::cs::{ConstraintSystem, DstBuffer};
use boojum::cs::{Place, Variable};
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::keccak256;
use boojum::gadgets::non_native_field::implementations::*;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueue;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatable, CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::castable::WitnessCastable;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::u16::UInt16;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::pairing::ff::Field;
use std::sync::{Arc, RwLock};
use zkevm_opcode_defs::system_params::STORAGE_AUX_BYTE;

use super::*;

pub mod input;
use self::input::*;

use boojum::pairing::bls12_381::fq::Fq as Bls12_381Fq;
use boojum::pairing::bls12_381::fr::Fr as Bls12_381Fr;
use boojum::pairing::bls12_381::G1Affine as Bls12_381G1Affine;
use boojum::pairing::bls12_381::G2Affine as Bls12_381G2Affine;

const NUM_WORDS_FR: usize = 17;
const NUM_WORDS_FQ: usize = 25;

type Bls12_381BaseNNFieldParams = NonNativeFieldOverU16Params<Bls12_381Fq, NUM_WORDS_FQ>;
type Bls12_381ScalarNNFieldParams = NonNativeFieldOverU16Params<Bls12_381Fr, NUM_WORDS_FR>;

type Bls12_381BaseNNField<F> = NonNativeFieldOverU16<F, Bls12_381Fq, 25>;
type Bls12_381ScalarNNField<F> = NonNativeFieldOverU16<F, Bls12_381Fr, 17>;

// turns 128 bits into a Bls12 field element.
fn convert_keccak_digest_to_field_element<
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: boojum::pairing::ff::PrimeField,
    const N: usize,
>(
    cs: &mut CS,
    input: [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE / 2],
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    for (dst, src) in limbs.iter_mut().zip(input.array_chunks::<2>()) {
        *dst = UInt16::from_le_bytes(cs, *src).get_variable();
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);
    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    }
}

fn convert_blob_chunk_to_field_element<
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: boojum::pairing::ff::PrimeField,
    const N: usize,
>(
    cs: &mut CS,
    input: &[UInt8<F>],
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    for (dst, src) in limbs.iter_mut().zip(input.array_chunks::<2>()) {
        *dst = UInt16::from_le_bytes(cs, *src).get_variable();
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);
    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    }
}

pub fn eip_4844_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    const N: usize,
>(
    cs: &mut CS,
    witness: EIP4844CircuitInstanceWitness<F>,
    round_function: &R,
    params: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
    [(); N + 1]:,
{
    let limit = params;

    assert!(limit <= 4096); // max blob length eip4844

    let EIP4844CircuitInstanceWitness { closed_form_input } = witness;

    let mut structured_input =
        EIP4844InputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
    let start_flag = structured_input.start_flag;

    let zero_u8: UInt8<F> = UInt8::zero(cs);
    let boolean_true = Boolean::allocated_constant(cs, true);

    // only 1 instance of the circuit here for now
    Boolean::enforce_equal(cs, &start_flag, &boolean_true);

    let hash = structured_input.observable_input.hash;
    let kzg_x = structured_input.observable_input.kzg_commitment_x;
    let kzg_y = structured_input.observable_input.kzg_commitment_y;
    let blob = structured_input.observable_input.blob;
    let input_bytes = hash
        .into_iter()
        .chain(kzg_x)
        .chain(kzg_y)
        .collect::<Vec<UInt8<F>>>();

    // create a field element out of the hash of the input hash and the kzg commitment
    let challenge_hash = boojum::gadgets::keccak256::keccak256(cs, &input_bytes);
    // truncate hash to 128 bits
    // NOTE: it is safe to draw a random scalar at max 128 bits because of the schwartz zippel
    // lemma
    let mut truncated_hash = [UInt8::zero(cs); 16];
    truncated_hash.copy_from_slice(&challenge_hash[..16]);
    let params = Arc::new(Bls12_381ScalarNNFieldParams::create());
    let mut z = convert_keccak_digest_to_field_element(cs, truncated_hash, &params);

    // Recompute the hash and check equality, and form blob polynomial simultaneously.
    let keccak_accumulator_state =
        [[[zero_u8; keccak256::BYTES_PER_WORD]; keccak256::LANE_WIDTH]; keccak256::LANE_WIDTH];

    let mut keccak_accumulator_state =
        keccak_accumulator_state.map(|el| el.map(|el| el.map(|el| el.get_variable())));

    use crate::base_structures::log_query::L2_TO_L1_MESSAGE_BYTE_LENGTH;
    // we do not serialize length because it's recalculatable in L1

    let empty_hash = {
        use zkevm_opcode_defs::sha3::*;

        let mut result = [0u8; 32];
        let digest = Keccak256::digest(&[]);
        result.copy_from_slice(digest.as_slice());

        result.map(|el| UInt8::allocated_constant(cs, el))
    };

    let mut buffer = vec![];

    use crate::storage_application::keccak256_conditionally_absorb_and_run_permutation;

    let no_work = Boolean::allocate_constant(cs, limit == 0);
    let mut y = Bls12_381ScalarNNField::<F>::allocated_constant(cs, Bls12_381Fr::zero(), &params);

    // fill up the buffer. since eip4844 blobs are always same size we can do this
    // without needing to account for variable lengths
    if limit != 0 {
        // XXX: fix structure
        for cycle in 0..(limit - 1) {
            // polynomial evaluations via horners rule
            let el = blob[cycle];
            let mut fe = convert_blob_chunk_to_field_element(cs, &el.el, &params);
            // horner's rule is defined as evaluating a polynomial a_0 + a_1x + a_2x^2 + ... + a_nx^n
            // in the form of a_0 + x(a_1 + x(a_2 + x(a_3 + ... + x(a_{n-1} + xa_n))))
            // since the blob is considered to be a polynomial in lagrange form, we essentially
            // 'work backwards' and start with the highest degree coefficients first. so we can
            // add and multiply and at the last step we just add the coefficient.
            y = y.add(cs, &mut fe);
            y = y.mul(cs, &mut z);

            // hash
            let buffer_for_round: [UInt8<F>; 136] = buffer[..136].try_into().unwrap();
            let buffer_for_round = buffer_for_round.map(|el| el.get_variable());
            let carry_on = buffer[136..].to_vec();

            buffer = carry_on;

            // absorb if we are not done yet
            keccak256_conditionally_absorb_and_run_permutation(
                cs,
                boolean_true,
                &mut keccak_accumulator_state,
                &buffer_for_round,
            );
        }

        // last round
        let el = blob[limit - 1];
        let mut fe = convert_blob_chunk_to_field_element(cs, &el.el, &params);
        y = y.add(cs, &mut fe); // as previously mentioned, last step only needs addition.

        let mut last_round_buffer = [zero_u8; 136];
        let tail_len = buffer.len();
        last_round_buffer[..tail_len].copy_from_slice(&buffer);
        last_round_buffer[tail_len] = UInt8::allocated_constant(cs, 0x01);
        last_round_buffer[136 - 1] = UInt8::allocated_constant(cs, 0x80);

        let last_round_buffer = last_round_buffer.map(|el| el.get_variable());

        // absorb if it's the last round
        keccak256_conditionally_absorb_and_run_permutation(
            cs,
            boolean_true,
            &mut keccak_accumulator_state,
            &last_round_buffer,
        );

        y.normalize(cs);
    }

    structured_input.completion_flag = boolean_true;

    let fsm_output = ();
    structured_input.hidden_fsm_output = fsm_output;

    // squeeze
    let mut keccak256_hash = [MaybeUninit::<UInt8<F>>::uninit(); keccak256::KECCAK256_DIGEST_SIZE];
    for (i, dst) in keccak256_hash.array_chunks_mut::<8>().enumerate() {
        for (dst, src) in dst.iter_mut().zip(keccak_accumulator_state[i][0].iter()) {
            let tmp = unsafe { UInt8::from_variable_unchecked(*src) };
            dst.write(tmp);
        }
    }

    let keccak256_hash = unsafe { keccak256_hash.map(|el| el.assume_init()) };

    let keccak256_hash =
        <[UInt8<F>; 32]>::conditionally_select(cs, no_work, &empty_hash, &keccak256_hash);

    // hash equality check
    for (input_byte, hash_byte) in hash.iter().zip(keccak256_hash) {
        let is_equal = UInt8::equals(cs, input_byte, &hash_byte);
        Boolean::enforce_equal(cs, &is_equal, &boolean_true);
    }

    let mut observable_output = EIP4844OutputData::placeholder(cs);
    observable_output.z = unsafe {
        let mut arr = [UInt16::allocate_constant(cs, 0); NUM_WORDS_FR];
        z.limbs
            .iter()
            .enumerate()
            .for_each(|(i, v)| arr[i] = UInt16::from_variable_unchecked(*v));
        arr
    };
    observable_output.y = unsafe {
        let mut arr = [UInt16::allocate_constant(cs, 0); NUM_WORDS_FR];
        y.limbs
            .iter()
            .enumerate()
            .for_each(|(i, v)| arr[i] = UInt16::from_variable_unchecked(*v));
        arr
    };
    structured_input.observable_output = observable_output;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    use crate::fsm_input_output::commit_variable_length_encodable_item;
    use crate::fsm_input_output::ClosedFormInputCompactForm;
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
mod tests {
    use super::*;
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::*;
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::*;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::CSGeometry;
    use boojum::cs::*;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::field::traits::field_like::PrimeFieldLike;
    use boojum::field::Field;
    use boojum::field::SmallField;
    use boojum::gadgets::queue::CircuitQueueRawWitness;
    use boojum::gadgets::tables::byte_split::ByteSplitTable;
    use boojum::gadgets::tables::*;
    use boojum::implementations::poseidon2::Poseidon2Goldilocks;
    use boojum::pairing::ff::{Field as PairingField, PrimeField, SqrtField};
    use boojum::worker::Worker;
    use rand::{Rand, Rng};

    type F = GoldilocksField;
    type P = GoldilocksField;

    #[test]
    fn test_eip4844() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 100,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
        };
        let max_variables = 1 << 28;
        let max_trace_len = 1 << 22;

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
            let builder = PublicInputGate::configure_builder(
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

        let round_function = Poseidon2Goldilocks;

        let blobs = vec![[0u8; 32]; 4096];
        let mut rng = rand::thread_rng();
        let blobs = blobs
            .into_iter()
            .map(|_| {
                let el = Bls12_381Fr::rand(&mut rng);
                let repr = el.into_repr();
                let mut bytes = vec![];
                for limb in repr.0 {
                    bytes.push((limb & 0xff) as u8);
                    bytes.push((limb >> 8 & 0xff) as u8);
                    bytes.push((limb >> 16 & 0xff) as u8);
                    bytes.push((limb >> 24 & 0xff) as u8);
                    bytes.push((limb >> 32 & 0xff) as u8);
                    bytes.push((limb >> 40 & 0xff) as u8);
                    bytes.push((limb >> 48 & 0xff) as u8);
                    bytes.push((limb >> 56 & 0xff) as u8);
                }
                let mut arr = [0u8; 32];
                arr.copy_from_slice(bytes.as_slice());
                arr
            })
            .collect::<Vec<[u8; 32]>>();

        use zkevm_opcode_defs::sha3::*;
        let mut observable_input = EIP4844InputData::placeholder_witness();
        observable_input.hash = {
            let mut result = [0u8; 32];
            let digest =
                Keccak256::digest(blobs.clone().into_iter().flatten().collect::<Vec<u8>>());
            result.copy_from_slice(digest.as_slice());
            result
        };
        observable_input.kzg_commitment_x = [0u8; NUM_WORDS_FQ];
        observable_input.kzg_commitment_y = [0u8; NUM_WORDS_FQ];
        observable_input.queue_state.tail.length = 4096;
        use boojum::field::U64Representable;
        // NOTE: this fails consistency check, need to figure out how to generate this properly
        observable_input.queue_state.tail.tail = [F::from_u64_unchecked(1u64); 4];

        let mut observable_output = EIP4844OutputData::placeholder_witness();
        let z = Keccak256::digest(
            observable_input
                .hash
                .into_iter()
                .chain(observable_input.kzg_commitment_x.into_iter())
                .chain(observable_input.kzg_commitment_y.into_iter())
                .collect::<Vec<u8>>(),
        );
        observable_output.z = [0u16; NUM_WORDS_FR];
        let z_u16 = z
            .chunks(2)
            .map(|els| {
                let mut r = els[0] as u16;
                r += (els[1] as u16) << 8;
                r
            })
            .collect::<Vec<u16>>();
        observable_output.z[..8].copy_from_slice(&z_u16[..8]);

        let z_repr = z
            .chunks(8)
            .map(|els| {
                let mut r = els[0] as u64;
                r += (els[1] as u64) << 8;
                r += (els[2] as u64) << 16;
                r += (els[3] as u64) << 24;
                r += (els[4] as u64) << 32;
                r += (els[5] as u64) << 40;
                r += (els[6] as u64) << 48;
                r += (els[7] as u64) << 56;
                r
            })
            .collect::<Vec<u64>>();
        let mut z_arr = [0u64; 4];
        z_arr[..2].copy_from_slice(&z_repr[..2]);

        let blob_arrs = blobs
            .clone()
            .iter()
            .map(|bytes| {
                let limbs = bytes
                    .chunks(8)
                    .map(|els| {
                        let mut r = els[0] as u64;
                        r += (els[1] as u64) << 8;
                        r += (els[2] as u64) << 16;
                        r += (els[3] as u64) << 24;
                        r += (els[4] as u64) << 32;
                        r += (els[5] as u64) << 40;
                        r += (els[6] as u64) << 48;
                        r += (els[7] as u64) << 56;
                        r
                    })
                    .collect::<Vec<u64>>();
                let mut limb_arr = [0u64; 4];
                limb_arr.copy_from_slice(&limbs);
                limb_arr
            })
            .collect::<Vec<[u64; 4]>>();

        use boojum::pairing::bls12_381::FrRepr;
        // evaluate polynomial
        let z_fr = Bls12_381Fr::from_repr(FrRepr(z_arr)).unwrap();
        let mut base = Bls12_381Fr::from_repr(FrRepr(*blob_arrs.last().unwrap())).unwrap();
        base.mul_assign(&z_fr);
        let y = blob_arrs
            .clone()
            .into_iter()
            .enumerate()
            .rev()
            .skip(1)
            .fold(base, |mut acc, (i, coeff)| {
                let coeff = Bls12_381Fr::from_repr(FrRepr(coeff)).unwrap();
                acc.add_assign(&coeff);
                if i != 0 {
                    acc.mul_assign(&z_fr);
                }
                acc
            });

        let y_limbs = {
            let repr = y.into_repr();
            let mut bytes = vec![];
            for limb in repr.0 {
                bytes.push((limb & 0xffff) as u16);
                bytes.push((limb >> 16 & 0xffff) as u16);
                bytes.push((limb >> 32 & 0xffff) as u16);
                bytes.push((limb >> 48 & 0xffff) as u16);
            }
            let mut arr = [0u16; NUM_WORDS_FR];
            arr[..16].copy_from_slice(bytes.as_slice());
            arr
        };
        observable_output.y.copy_from_slice(&y_limbs);

        let chunks = blobs
            .into_iter()
            .map(|el| {
                (
                    BlobChunkWitness {
                        el: U256::from_little_endian(&el),
                    },
                    [F::ZERO, F::ZERO, F::ZERO, F::ZERO],
                )
            })
            .collect::<Vec<(BlobChunkWitness<F>, [_; 4])>>();

        let witness = EIP4844CircuitInstanceWitness {
            closed_form_input: EIP4844InputOutputWitness {
                start_flag: true,
                completion_flag: true,
                observable_input,
                observable_output,
                hidden_fsm_input: (),
                hidden_fsm_output: (),
            },
            queue_witness: CircuitQueueRawWitness {
                elements: chunks.into(),
            },
        };

        eip_4844_entry_point(cs, witness, &round_function, 4096);

        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
