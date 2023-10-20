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

// TODO: check all endianness
// turns 128 bits into a Bls12 field element.
fn convert_keccak_digest_to_field_element<
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: boojum::pairing::ff::PrimeField,
    const N: usize,
>(
    cs: &mut CS,
    input: [UInt8<F>; 16],
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    // since the value would be interpreted as big endian in the L1 we need to reverse our bytes to
    // get the correct value
    for (dst, src) in limbs.iter_mut().zip(input.array_chunks::<2>()).rev() {
        *dst = UInt16::from_le_bytes(cs, *src).get_variable();
    }

    // Note: we do not need to check for overflows because the max value is 2^128 which is less
    // than the field modulus.
    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 1 },
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
    input: &[UInt8<F>; 31],
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    let input_chunks = input.array_chunks::<2>();
    let remainder = input_chunks.remainder();
    for (dst, src) in limbs.iter_mut().zip(input_chunks) {
        *dst = UInt16::from_le_bytes(cs, *src).get_variable();
    }

    // since array_chunks drops any remaining elements that don't fit in the size requirement,
    // we need to manually set the last byte in limbs
    limbs[15] = remainder[0].get_variable();

    // Note: we do not need to check for overflows because the max value is 2^248 which is less
    // than the field modulus.
    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 1 },
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

    assert!(limit == 4096); // max blob length eip4844

    let EIP4844CircuitInstanceWitness {
        versioned_hash,
        linear_hash_output,
        data_chunks,
    } = witness;

    let versioned_hash = <[UInt8<F>; 32]>::allocate(cs, versioned_hash);
    let linear_hash_output = <[UInt8<F>; 32]>::allocate(cs, linear_hash_output);

    let data_chunks = data_chunks
        .into_iter()
        .map(|chunk| BlobChunk::<F>::allocate(cs, chunk))
        .collect::<Vec<BlobChunk<F>>>();

    let boolean_true = Boolean::allocated_constant(cs, true);
    let mut structured_input = EIP4844InputOutput::<F> {
        start_flag: boolean_true,
        completion_flag: boolean_true,
        observable_input: (),
        observable_output: EIP4844OutputData {
            output_hash: [UInt8::<F>::zero(cs); keccak256::KECCAK256_DIGEST_SIZE],
        },
        hidden_fsm_input: (),
        hidden_fsm_output: (),
    };

    let zero_u8: UInt8<F> = UInt8::zero(cs);

    // create a field element out of the hash of the input hash and the kzg commitment
    let challenge_hash = boojum::gadgets::keccak256::keccak256(
        cs,
        linear_hash_output
            .into_iter()
            .chain(versioned_hash.into_iter())
            .collect::<Vec<UInt8<F>>>()
            .as_slice(),
    );
    // truncate hash to 128 bits
    // NOTE: it is safe to draw a random scalar at max 128 bits because of the schwartz zippel
    // lemma
    let mut truncated_hash = [UInt8::zero(cs); 16];
    truncated_hash.copy_from_slice(&challenge_hash[16..]); // take last 16 bytes to get max 2^128
                                                           // in big endian scenario
    let params = Arc::new(Bls12_381ScalarNNFieldParams::create());
    let mut evaluation_point = convert_keccak_digest_to_field_element(cs, truncated_hash, &params);

    //
    // Recompute the hash and check equality, and form blob polynomial simultaneously.
    //
    let keccak_accumulator_state =
        [[[zero_u8; keccak256::BYTES_PER_WORD]; keccak256::LANE_WIDTH]; keccak256::LANE_WIDTH];

    let mut keccak_accumulator_state =
        keccak_accumulator_state.map(|el| el.map(|el| el.map(|el| el.get_variable())));

    use crate::base_structures::log_query::L2_TO_L1_MESSAGE_BYTE_LENGTH;
    // we do not serialize length because it's recalculatable in L1

    let mut buffer = vec![];

    use crate::storage_application::keccak256_conditionally_absorb_and_run_permutation;
    use boojum::gadgets::keccak256::KECCAK_RATE_BYTES;

    let mut opening_value =
        Bls12_381ScalarNNField::<F>::allocated_constant(cs, Bls12_381Fr::zero(), &params);

    for cycle in 0..(limit - 1) {
        let el = data_chunks[cycle];
        // polynomial evaluations via horner's rule
        let mut fe = convert_blob_chunk_to_field_element(cs, &el.el, &params);
        // horner's rule is defined as evaluating a polynomial a_0 + a_1x + a_2x^2 + ... + a_nx^n
        // in the form of a_0 + x(a_1 + x(a_2 + x(a_3 + ... + x(a_{n-1} + xa_n))))
        // since the blob is considered to be a polynomial in lagrange form, we essentially
        // 'work backwards' and start with the highest degree coefficients first. so we can
        // add and multiply and at the last step we just add the coefficient.
        opening_value = opening_value.add(cs, &mut fe);
        opening_value = opening_value.mul(cs, &mut evaluation_point);

        assert!(buffer.len() < 136);

        buffer.extend(el.el);

        // hash
        if buffer.len() >= 136 {
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

        assert!(buffer.len() < 136);
    }

    // last round
    let el = data_chunks[limit - 1];
    let mut fe = convert_blob_chunk_to_field_element(cs, &el.el, &params);
    opening_value = opening_value.add(cs, &mut fe); // as previously mentioned, last step only needs addition.

    buffer.extend(el.el);

    let mut last_round_buffer = [zero_u8; 136];
    let tail_len = buffer.len();
    last_round_buffer[..tail_len].copy_from_slice(&buffer);

    if tail_len == KECCAK_RATE_BYTES - 1 {
        last_round_buffer[tail_len] = UInt8::allocated_constant(cs, 0x81);
    } else {
        last_round_buffer[tail_len] = UInt8::allocated_constant(cs, 0x01);
        last_round_buffer[KECCAK_RATE_BYTES - 1] = UInt8::allocated_constant(cs, 0x80);
    }

    let last_round_buffer = last_round_buffer.map(|el| el.get_variable());

    keccak256_conditionally_absorb_and_run_permutation(
        cs,
        boolean_true,
        &mut keccak_accumulator_state,
        &last_round_buffer,
    );

    opening_value.normalize(cs);

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

    // hash equality check
    for (input_byte, hash_byte) in linear_hash_output.iter().zip(keccak256_hash) {
        Num::enforce_equal(cs, &input_byte.into_num(), &hash_byte.into_num());
    }

    use boojum::gadgets::keccak256::keccak256;
    opening_value.enforce_reduced(cs);
    let opening_bytes = opening_value.limbs[..16]
        .iter()
        .rev()
        .flat_map(|v| unsafe {
            let n = UInt16::from_variable_unchecked(*v).to_be_bytes(cs);
            [n[0], n[1]]
        })
        .collect::<Vec<UInt8<F>>>();

    let output_hash = keccak256(
        cs,
        versioned_hash
            .into_iter()
            .chain(truncated_hash.into_iter())
            .chain(opening_bytes.into_iter())
            .collect::<Vec<UInt8<F>>>()
            .as_slice(),
    );

    let mut observable_output = EIP4844OutputData::placeholder(cs);
    observable_output.output_hash = output_hash;
    structured_input.observable_output = observable_output;

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
        let max_variables = 1 << 26;
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

        let data_chunks = vec![[0u8; 31]; 4096];
        let mut rng = rand::thread_rng();
        let data_chunks = data_chunks
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
                let mut arr = [0u8; 31];
                arr.copy_from_slice(&bytes.as_slice()[..31]);
                arr
            })
            .collect::<Vec<[u8; 31]>>();

        use zkevm_opcode_defs::sha3::*;
        let mut linear_hash_output = [0u8; 32];
        let digest = Keccak256::digest(
            data_chunks
                .clone()
                .into_iter()
                .flatten()
                .collect::<Vec<u8>>(),
        );
        linear_hash_output.copy_from_slice(digest.as_slice());
        let kzg_commitment_x = [0u8; NUM_WORDS_FQ];
        let kzg_commitment_y = [0u8; NUM_WORDS_FQ];
        let mut versioned_hash = [0u8; 32];
        let digest = Keccak256::digest(
            kzg_commitment_x
                .into_iter()
                .chain(kzg_commitment_y.into_iter())
                .collect::<Vec<u8>>(),
        );
        versioned_hash.copy_from_slice(digest.as_slice());
        versioned_hash[0] = 0x01;

        let evaluation_point = Keccak256::digest(
            linear_hash_output
                .into_iter()
                .chain(versioned_hash.into_iter())
                .collect::<Vec<u8>>(),
        )[..16]
            .to_vec();

        let evaluation_point_repr = evaluation_point
            .chunks(8)
            .map(|els| {
                els.iter()
                    .enumerate()
                    .fold(0u64, |acc, (i, el)| acc + ((*el as u64) << (8 * i)))
            })
            .collect::<Vec<u64>>();
        let mut evaluation_point_arr = [0u64; 4];
        evaluation_point_arr[..2].copy_from_slice(&evaluation_point_repr[..2]);

        let blob_arrs = data_chunks
            .clone()
            .iter()
            .map(|bytes| {
                let limbs = bytes
                    .chunks(8)
                    .map(|els| {
                        els.iter()
                            .enumerate()
                            .fold(0u64, |acc, (i, el)| acc + ((*el as u64) << (8 * i)))
                    })
                    .collect::<Vec<u64>>();
                let mut limb_arr = [0u64; 4];
                limb_arr.copy_from_slice(&limbs);
                limb_arr
            })
            .collect::<Vec<[u64; 4]>>();

        use boojum::pairing::bls12_381::FrRepr;
        // evaluate polynomial
        let evaluation_point_fr = Bls12_381Fr::from_repr(FrRepr(evaluation_point_arr)).unwrap();
        let opening_value = blob_arrs.clone().into_iter().enumerate().fold(
            Bls12_381Fr::zero(),
            |mut acc, (i, coeff)| {
                let coeff = Bls12_381Fr::from_repr(FrRepr(coeff)).unwrap();
                acc.add_assign(&coeff);
                if i != blob_arrs.len() - 1 {
                    acc.mul_assign(&evaluation_point_fr);
                }
                acc
            },
        );

        let opening_value_bytes = {
            let repr = opening_value.into_repr();
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
            arr[..32].copy_from_slice(bytes.as_slice());
            arr
        };

        let mut observable_output = EIP4844OutputData::<F>::placeholder_witness();
        observable_output.output_hash = Keccak256::digest(
            versioned_hash
                .into_iter()
                .chain(evaluation_point.into_iter())
                .chain(opening_value_bytes.into_iter())
                .collect::<Vec<u8>>(),
        )
        .into();

        let witness = EIP4844CircuitInstanceWitness {
            versioned_hash,
            linear_hash_output,
            data_chunks: data_chunks
                .into_iter()
                .map(|el| BlobChunkWitness { el })
                .collect::<Vec<BlobChunkWitness<F>>>(),
        };

        eip_4844_entry_point::<_, _, _, 17>(cs, witness, &round_function, 4096);

        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
