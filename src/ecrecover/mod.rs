use super::*;
use arrayvec::ArrayVec;
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::field::SmallField;
use boojum::gadgets::curves::sw_projective::SWProjectivePoint;
use boojum::gadgets::keccak256::keccak256;
use boojum::gadgets::u16::UInt16;
use cs_derive::*;
use boojum::gadgets::u32::UInt32;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::non_native_field::implementations::*;
use ethereum_types::U256;
use boojum::crypto_bigint::{U1024, Zero};
use boojum::gadgets::num::Num;
use std::sync::Arc;
use boojum::pairing::CurveAffine;
use boojum::gadgets::u8::UInt8;

pub mod input;
pub use self::input::*;

mod secp256k1;



#[derive(
    Derivative,
    CSSelectable,
)]
#[derivative(Clone, Debug)]
pub struct EcrecoverPrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_offset: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_offset: UInt32<F>,
}

impl<F: SmallField> EcrecoverPrecompileCallParams<F> {
    // pub fn empty() -> Self {
    //     Self {
    //         input_page: UInt32::<E>::zero(),
    //         input_offset: UInt32::<E>::zero(),
    //         output_page: UInt32::<E>::zero(),
    //         output_offset: UInt32::<E>::zero(),
    //     }
    // }

    pub fn from_encoding<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        encoding: UInt256<F>,
    ) -> Self {
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

// characteristics of the base field for secp curve
use self::secp256k1::fq::Fq as Secp256Fq;
// order of group of points for secp curve
use self::secp256k1::fr::Fr as Secp256Fr;
// some affine point
use self::secp256k1::PointAffine as Secp256Affine;

const NUM_WORDS: usize = 17;

const CHUNK_BITLEN: usize = 64;
const SECP_B_COEF: u64 = 7;
const EXCEPTION_FLAGS_ARR_LEN: usize = 5;
const NUM_MEMORY_READS_PER_CYCLE: usize = 3;
const X_POWERS_ARR_LEN: usize = 256;
const UNPADDED_KECCAK_INPUT_WORDS_LEN: usize = 8;
const KECCAK_DIGEST_WORDS_SIZE: usize = 3;

type Secp256BaseNNFieldParams = NonNativeFieldOverU16Params<Secp256Fq, 17>;
type Secp256ScalarNNFieldParams = NonNativeFieldOverU16Params<Secp256Fr, 17>;

type Secp256BaseNNField<F> = NonNativeFieldOverU16<F, Secp256Fq, 17>;
type Secp256ScalarNNField<F> = NonNativeFieldOverU16<F, Secp256Fr, 17>;

// assume that constructed field element is not zero
// if this is not satisfied - set the result to be F::one
fn convert_uint256_to_field_element_masked<
    F: SmallField, 
    CS: ConstraintSystem<F>, 
    P: boojum::pairing::ff::PrimeField, 
    const N: usize,
>(
    cs: &mut CS,
    elem: &UInt256<F>,
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> (NonNativeFieldOverU16<F, P, N>, Boolean<F>) where [(); N+1]: {
    let is_zero = elem.is_zero(cs);
    let one_nn = NonNativeFieldOverU16::<F, P, N>::allocated_constant(cs, P::one(), params);
    // we still have to decompose it into u16 words
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    assert!(N >= 16);
    for (dst, src) in limbs.array_chunks_mut::<2>().zip(elem.inner.iter()) {
        let [b0, b1, b2, b3] = src.to_le_bytes(cs);
        let low = UInt16::from_le_bytes(cs, [b0, b1]);
        let high = UInt16::from_le_bytes(cs, [b2, b3]);

        *dst = [low.get_variable(), high.get_variable()];
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);

    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 0 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs: limbs,
        tracker: OverflowTracker {
            max_moduluses,
        },
        form: RepresentationForm::Lazy,
        params: params.clone(),
        _marker: std::marker::PhantomData
    };

    let selected = Selectable::conditionally_select(cs, is_zero, &one_nn, &element);

    (selected, is_zero)
}

fn convert_uint256_to_field_element<
    F: SmallField, 
    CS: ConstraintSystem<F>, 
    P: boojum::pairing::ff::PrimeField, 
    const N: usize,
>(
    cs: &mut CS,
    elem: &UInt256<F>,
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N> {
    // we still have to decompose it into u16 words
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; N];
    assert!(N >= 16);
    for (dst, src) in limbs.array_chunks_mut::<2>().zip(elem.inner.iter()) {
        let [b0, b1, b2, b3] = src.to_le_bytes(cs);
        let low = UInt16::from_le_bytes(cs, [b0, b1]);
        let high = UInt16::from_le_bytes(cs, [b2, b3]);

        *dst = [low.get_variable(), high.get_variable()];
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);
    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 0 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs: limbs,
        tracker: OverflowTracker {
            max_moduluses,
        },
        form: RepresentationForm::Lazy,
        params: params.clone(),
        _marker: std::marker::PhantomData
    };

    element
}

fn ecrecover_precompile_inner_routine<
    F: SmallField,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    recid: &UInt8<F>,
    r: &UInt256<F>,
    s: &UInt256<F>,
    message_hash: &UInt256<F>,
    valid_x_in_external_field: Secp256BaseNNField<F>,
    valid_y_in_external_field: Secp256BaseNNField<F>,
    valid_t_in_external_field: Secp256BaseNNField<F>,
    base_field_params: &Arc<Secp256BaseNNFieldParams>,
    scalar_field_params: &Arc<Secp256ScalarNNFieldParams>,
) -> (Boolean<F>, UInt256<F>) {
    use boojum::pairing::ff::Field;
    let curve_b = Secp256Affine::b_coeff();

    let mut minus_one = Secp256Fq::one();
    minus_one.negate();

    let mut curve_b_nn = Secp256BaseNNField::<F>::allocated_constant(cs, curve_b, &base_field_params);
    let mut minus_one_nn = Secp256BaseNNField::<F>::allocated_constant(cs, minus_one, &base_field_params);

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

    // recid = (x_overflow ? 2 : 0) | (secp256k1_fe_is_odd(&r.y) ? 1 : 0)
    // The point X = (x, y) we are going to recover is not known at the start, but it is strongly related to r.
    // This is because x = r + kn for some integer k, where x is an element of the field F_q . In other words, x < q.
    // (here n is the order of group of points on elleptic curve)
    // For secp256k1 curve values of q and n are relatively close, that is,
    // the probability of a random element of Fq being greater than n is about 1/{2^128}.
    // This in turn means that the overwhelming majority of r determine a unique x, however some of them determine
    // two: x = r and x = r + n. If x_overflow flag is set than x = r + n

    let [y_is_odd, x_overflow, ..] = Num::<F>::from_variable(recid.get_variable()).spread_into_bits::<_, 8>(cs);

    let (r_plus_n, of) = r.overflowing_add(cs, &secp_n_u256);
    let mut x_as_u256 =
        UInt256::conditionally_select(cs, x_overflow, &r_plus_n, &r);
    let error = Boolean::multi_and(cs, &[x_overflow, of]);
    exception_flags.push(error);

    // we handle x separately as it is the only element of base field of a curve (not a scalar field element!)
    // check that x < q - order of base point on Secp256 curve
    // if it is not actually the case - mask x to be zero
    let (_res, is_in_range) = x_as_u256.overflowing_sub(cs, &secp_p_u256);
    x_as_u256 = x_as_u256.mask(cs, is_in_range);
    let exception = is_in_range.negated(cs);
    exception_flags.push(exception);

    let mut x_fe = convert_uint256_to_field_element(cs, &x_as_u256, &base_field_params);

    let (mut r_fe, r_is_zero) = convert_uint256_to_field_element_masked(
        cs,
        &r,
        &scalar_field_params,
    );
    exception_flags.push(r_is_zero);
    let (mut s_fe, s_is_zero) = convert_uint256_to_field_element_masked(
        cs,
        &s,
        &scalar_field_params,
    );
    exception_flags.push(s_is_zero);

    // NB: although it is not strictly an exception we also assume that hash is never zero as field element
    let (mut message_hash_fe, message_hash_is_zero) = convert_uint256_to_field_element_masked(
        cs,
        &message_hash,
        &scalar_field_params,
    );
    exception_flags.push(s_is_zero);

    // curve equation is y^2 = x^3 + b
    // we compute t = r^3 + b and check if t is a quadratic residue or not.
    // we do this by computing Legendre symbol (t, p) = t^[(p-1)/2] (mod p)
    // p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
    // n = (p-1)/2 = 2^255 - 2^31 - 2^8 - 2^7 - 2^6 - 2^5 - 2^3 - 1
    // we have to compute t^b = t^{2^255} / ( t^{2^31} * t^{2^8} * t^{2^7} * t^{2^6} * t^{2^5} * t^{2^3} * t)
    // if t is not a quadratic residue we return error and replace x by another value that will make
    // t = x^3 + b a quadratic residue

    let mut t = x_fe.square(cs);
    t = t.mul(cs, &mut x_fe);
    t = t.add(
        cs,
        &mut curve_b_nn,
    );

    let t_is_zero = x_fe.is_zero( cs);
    exception_flags.push(t_is_zero);

    // if t is zero then just mask
    let t = Selectable::conditionally_select(
        cs,
        t_is_zero,
        &valid_t_in_external_field,
        &t,
    );

    // array of powers of t of the form t^{2^i} starting from i = 0 to 255
    let mut t_powers = Vec::with_capacity(X_POWERS_ARR_LEN);
    t_powers.push(t);

    for _ in 1..X_POWERS_ARR_LEN {
        let mut prev = t_powers.last_mut().unwrap();
        let next = prev.square(cs);
        drop(prev);
        t_powers.push(next);
    }

    let mut acc = t_powers[0].clone();
    for idx in [3, 5, 6, 7, 8, 31].into_iter() {
        let mut other = &mut t_powers[idx];
        acc = acc.mul(cs, other);
    }
    let mut legendre_symbol = t_powers[255].div_unchecked(cs, &mut acc);

    // we can also reuse the same values to compute square root in case of p = 3 mod 4
    //           p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
    // n = (p+1)/4 = 2^254 - 2^30 - 2^7 - 2^6 - 2^5 - 2^4 - 2^2

    let mut acc_2 = t_powers[2].clone();
    for idx in [4, 5, 6, 7, 30].into_iter() {
        let other = &mut t_powers[idx];
        acc_2 = acc_2.mul(cs, other);
    }
    let mut may_be_recovered_y = t_powers[254].div_unchecked(cs, &mut acc_2);
    let may_be_recovered_y_negated = may_be_recovered_y.negated(cs);

    may_be_recovered_y.normalize(cs);
    let [lowest_bit, ..] = Num::<F>::from_variable(may_be_recovered_y.limbs[0]).spread_into_bits::<_, 8>(cs);

    // if lowest bit != parity bit, then we need conditionally select
    let should_swap = lowest_bit.xor(cs, y_is_odd);
    let may_be_recovered_y = Selectable::conditionally_select(
        cs, 
        should_swap, 
        &may_be_recovered_y_negated, 
        &may_be_recovered_y,
    );

    let t_is_nonresidue =
        Secp256BaseNNField::<F>::equals(cs, &mut legendre_symbol, &mut minus_one_nn);
    exception_flags.push(t_is_nonresidue);
    // unfortunately, if t is found to be a quadratic nonresidue, we can't simply let x to be zero,
    // because then t_new = 7 is again a quadratic nonresidue. So, in this case we let x to be 9, then
    // t = 16 is a quadratic residue
    let x = Selectable::conditionally_select(
        cs,
        t_is_nonresidue,
        &valid_x_in_external_field,
        &x_fe,
    );
    let y = Selectable::conditionally_select(
        cs,
        t_is_nonresidue,
        &valid_y_in_external_field,
        &may_be_recovered_y,
    );

    // we recovered (x, y) using curve equation, so it's on curve (or was masked)
    let mut r_fe_inversed = r_fe.inverse_unchecked(cs);
    let mut s_by_r_inv = s_fe.mul(cs, &mut r_fe_inversed);
    let mut message_hash_by_r_inv = message_hash_fe.mul(cs, &mut r_fe_inversed);

    s_by_r_inv.normalize(cs);
    message_hash_by_r_inv.normalize(cs);

    let (gen_x, gen_y) = Secp256Affine::one().into_xy_unchecked();
    let gen_x = Secp256BaseNNField::allocated_constant(cs, gen_x, base_field_params);
    let gen_y = Secp256BaseNNField::allocated_constant(cs, gen_y, base_field_params);

    let s_by_r_inv_normalized_lsb_bits: Vec<_> = s_by_r_inv.limbs.iter().map(|el| {
        Num::<F>::from_variable(*el).spread_into_bits::<_, 16>(cs)
    }).flatten().collect();
    let message_hash_by_r_inv_lsb_bits: Vec<_> = message_hash_by_r_inv.limbs.iter().map(|el| {
        Num::<F>::from_variable(*el).spread_into_bits::<_, 16>(cs)
    }).flatten().collect();

    // now we are going to compute the public key Q = (x, y) determined by the formula:
    // Q = (s * X - hash * G) / r which is equivalent to r * Q = s * X - hash * G
    // current implementation of point by scalar multiplications doesn't support multiplication by zero
    // so we check that all s, r, hash are not zero (as FieldElements):
    // if any of them is zero we reject the signature and in circuit itself replace all zero variables by ones

    // now we do multiexponentiation
    let mut q = SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::zero(cs, base_field_params);
    for (x_bit, hash_bit) in s_by_r_inv_normalized_lsb_bits.into_iter().zip(message_hash_by_r_inv_lsb_bits.into_iter()) {
        todo!();

        q = q.double(cs);
    }

    use boojum::pairing::GenericCurveAffine;
    let ((mut x, mut y), is_infinity) = q.convert_to_affine_or_default(cs, Secp256Affine::one());
    exception_flags.push(is_infinity);
    let any_exception = Boolean::multi_or(cs, &exception_flags[..]);

    x.normalize(cs);
    y.normalize(cs);

    let zero_u8 = UInt8::zero(cs);

    let mut bytes_to_hash = [zero_u8; 64];
    let it = x.limbs[..16].iter().rev().chain(
        y.limbs[..16].iter().rev()
    );
    
    for (dst, src) in bytes_to_hash.array_chunks_mut::<2>().zip(it) {
        let limb = unsafe { UInt16::from_variable_unchecked(*src) };
        *dst = limb.to_be_bytes(cs);
    }

    
    let mut digest_bytes = keccak256(cs, &bytes_to_hash);

    // digest is 32 bytes, but we need only 20 to recover address
    digest_bytes[0..12].copy_from_slice(&[zero_u8; 12]); // empty out top bytes
    let written_value_unmasked: UInt256<F> = todo!();
    // let written_value_unmasked = UInt256::from_be_bytes(cs, &digest_bytes);

    let written_value = written_value_unmasked.mask_negated(cs, any_exception);
    let all_ok = any_exception.negated(cs);

    (all_ok, written_value)
}

// use crate::glue::aux_byte_markers::aux_byte_for_precompile_call;

// pub fn ecrecover_function_entry_point<
//     E: Engine,
//     CS: ConstraintSystem<E>,
//     R: CircuitArithmeticRoundFunction<E, 2, 3, StateElement = Num<E>>,
// >(
//     cs: &mut CS,
//     witness: Option<EcrecoverCircuitInstanceWitness<E>>,
//     round_function: &R,
//     limit: usize,
// ) -> Result<AllocatedNum<E>, SynthesisError> {
//     use crate::bellman::plonk::better_better_cs::cs::LookupTableApplication;
//     use crate::bellman::plonk::better_better_cs::data_structures::PolyIdentifier;
//     use crate::vm::tables::BitwiseLogicTable;
//     use crate::vm::VM_BITWISE_LOGICAL_OPS_TABLE_NAME;

//     let columns3 = vec![
//         PolyIdentifier::VariablesPolynomial(0),
//         PolyIdentifier::VariablesPolynomial(1),
//         PolyIdentifier::VariablesPolynomial(2),
//     ];

//     if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
//         let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
//         let bitwise_logic_table = LookupTableApplication::new(
//             name,
//             BitwiseLogicTable::new(&name, 8),
//             columns3.clone(),
//             None,
//             true,
//         );
//         cs.add_table(bitwise_logic_table)?;
//     };

//     inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

//     type G = crate::secp256k1::PointAffine;

//     assert!(limit <= u32::MAX as usize);
//     let keccak_gadget = Keccak256Gadget::new(cs, None, None, None, None, false, "")?;

//     let precompile_address = UInt160::<E>::from_uint(u160::from_u64(
//         zkevm_opcode_defs::system_params::ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS as u64,
//     ));
//     let aux_byte_for_precompile = aux_byte_for_precompile_call::<E>();

//     let secp_p_as_u64x4 = UInt256::<E>::constant(
//         franklin_crypto::plonk::circuit::bigint_new::bigint::repr_to_biguint::<Secp256Fq>(
//             &Secp256Fq::char(),
//         ),
//     );
//     let secp_n_as_u64x4 = UInt256::<E>::constant(
//         franklin_crypto::plonk::circuit::bigint_new::bigint::repr_to_biguint::<Secp256Fr>(
//             &Secp256Fr::char(),
//         ),
//     );
//     assert_eq!(CHUNK_BITLEN, 64);
//     let rns_strategy_for_base_field =
//         RnsParameters::<E, <G as GenericCurveAffine>::Base>::new_optimal(cs, CHUNK_BITLEN);
//     let rns_strategy_for_scalar_field =
//         RnsParameters::<E, <G as GenericCurveAffine>::Scalar>::new_optimal(cs, CHUNK_BITLEN);

//     let one_in_external_field =
//         FieldElement::<E, <G as GenericCurveAffine>::Base>::one(&rns_strategy_for_base_field);
//     let mut minus_one_in_external_field = one_in_external_field.negate(cs)?;
//     let b_coef_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
//         u64_to_fe::<<G as GenericCurveAffine>::Base>(SECP_B_COEF),
//         &rns_strategy_for_base_field,
//     );
//     let valid_x_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
//         u64_to_fe::<<G as GenericCurveAffine>::Base>(9),
//         &rns_strategy_for_base_field,
//     );
//     let valid_t_in_external_field = FieldElement::<E, <G as GenericCurveAffine>::Base>::constant(
//         u64_to_fe::<<G as GenericCurveAffine>::Base>(9 + SECP_B_COEF),
//         &rns_strategy_for_base_field,
//     );

//     let structured_input_witness = project_ref!(witness, closed_form_input).cloned();
//     let requests_queue_witness = project_ref!(witness, requests_queue_witness).cloned();
//     let mut memory_reads_witness = project_ref!(witness, memory_reads_witness).cloned();

//     let mut structured_input =
//         EcrecoverCircuitInputOutput::alloc_ignoring_outputs(cs, structured_input_witness.clone())?;

//     let requests_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
//         cs,
//         structured_input.hidden_fsm_input.log_queue_state.head_state,
//         structured_input.hidden_fsm_input.log_queue_state.tail_state,
//         structured_input.hidden_fsm_input.log_queue_state.num_items,
//     )?;

//     let requests_queue_from_passthrough = StorageLogQueue::from_raw_parts(
//         cs,
//         structured_input
//             .observable_input
//             .initial_log_queue_state
//             .head_state,
//         structured_input
//             .observable_input
//             .initial_log_queue_state
//             .tail_state,
//         structured_input
//             .observable_input
//             .initial_log_queue_state
//             .num_items,
//     )?;

//     let mut requests_queue = StorageLogQueue::conditionally_select(
//         cs,
//         &structured_input.start_flag,
//         &requests_queue_from_passthrough,
//         &requests_queue_from_fsm_input,
//     )?;

//     if let Some(wit) = requests_queue_witness {
//         requests_queue.witness = wit;
//     }

//     let memory_queue_from_fsm_input = MemoryQueriesQueue::from_raw_parts(
//         cs,
//         structured_input.hidden_fsm_input.memory_queue_state.head,
//         structured_input.hidden_fsm_input.memory_queue_state.tail,
//         structured_input.hidden_fsm_input.memory_queue_state.length,
//     )?;

//     let memory_queue_from_passthrough = MemoryQueriesQueue::from_raw_parts(
//         cs,
//         structured_input.observable_input.initial_memory_state.head,
//         structured_input.observable_input.initial_memory_state.tail,
//         structured_input
//             .observable_input
//             .initial_memory_state
//             .length,
//     )?;

//     let mut memory_queue = MemoryQueriesQueue::conditionally_select(
//         cs,
//         &structured_input.start_flag,
//         &memory_queue_from_passthrough,
//         &memory_queue_from_fsm_input,
//     )?;

//     for _cycle in 0..limit {
//         let is_empty = requests_queue.is_empty(cs)?;
//         let request = requests_queue.pop_first(cs, &is_empty.not(), round_function)?;
//         let mut precompile_call_params =
//             EcrecoverPrecompileCallParams::from_encoding(cs, request.key)?;
//         let timestamp_to_use_for_read = request.timestamp;
//         let (timestamp_to_use_for_write, of) = timestamp_to_use_for_read.increment_checked(cs)?;
//         Boolean::enforce_equal(cs, &of, &Boolean::constant(false))?;

//         use crate::glue::code_unpacker_sha256::memory_query_updated::MemoryQuery;

//         Num::conditionally_enforce_equal(
//             cs,
//             &is_empty.not(),
//             &request.aux_byte.inner,
//             &aux_byte_for_precompile.inner,
//         )?;
//         Num::conditionally_enforce_equal(
//             cs,
//             &is_empty.not(),
//             &request.address.inner,
//             &precompile_address.inner,
//         )?;

//         let mut read_values = [UInt256::zero(); 4];
//         let mut read_values_le_bytes = [[Num::zero(); 32]; 4];

//         for idx in 0..4 {
//             let (memory_query_witness, _) = get_vec_vec_witness_raw_with_hint_on_more_in_subset(
//                 &mut memory_reads_witness,
//                 BigUint::from(0u64),
//             );
//             let (u256_value, le_bytes) =
//                 UInt256::alloc_from_biguint_and_return_u8_chunks(cs, memory_query_witness)?;
//             let mut memory_query = MemoryQuery::<E>::empty();
//             memory_query.timestamp = timestamp_to_use_for_read;
//             memory_query.memory_page = precompile_call_params.input_page;
//             memory_query.memory_index = precompile_call_params.input_offset;
//             memory_query.rw_flag = Boolean::constant(false);
//             memory_query.value = u256_value;

//             read_values[idx] = u256_value;
//             read_values_le_bytes[idx] = le_bytes;

//             let memory_query = memory_query.into_raw_query(cs)?;
//             let _ = memory_queue.push(cs, &memory_query, &is_empty.not(), round_function)?;

//             precompile_call_params.input_offset = precompile_call_params
//                 .input_offset
//                 .increment_unchecked(cs)?;
//         }

//         let [message_hash_as_u64x4, _v, r_as_u64x4, s_as_u64x4] = read_values;
//         let [_, v_bytes, _, _] = read_values_le_bytes;
//         let recid = UInt32::from_num_unchecked(v_bytes[0]);

//         let (success, written_value) = ecrecover_precompile_inner_routine::<E, CS, G>(
//             cs,
//             &recid,
//             &r_as_u64x4,
//             &s_as_u64x4,
//             &message_hash_as_u64x4,
//             &secp_p_as_u64x4,
//             &secp_n_as_u64x4,
//             &b_coef_in_external_field,
//             &valid_x_in_external_field,
//             &valid_t_in_external_field,
//             &mut minus_one_in_external_field,
//             &rns_strategy_for_base_field,
//             &rns_strategy_for_scalar_field,
//             &keccak_gadget,
//         )?;

//         let mut success_as_u256 = UInt256::zero();
//         let mut lc = LinearCombination::zero();
//         lc.add_assign_boolean_with_coeff(&success, E::Fr::one());
//         success_as_u256.inner[0] = UInt64::from_num_unchecked(lc.into_num(cs)?);

//         let success_query = MemoryQuery {
//             timestamp: timestamp_to_use_for_write,
//             memory_page: precompile_call_params.output_page,
//             memory_index: precompile_call_params.output_offset,
//             rw_flag: Boolean::constant(true),
//             value: success_as_u256,
//             value_is_ptr: Boolean::constant(false),
//         };
//         let success_query = success_query.into_raw_query(cs)?;

//         precompile_call_params.output_offset = precompile_call_params
//             .output_offset
//             .increment_unchecked(cs)?;
//         let _ = memory_queue.push(cs, &success_query, &is_empty.not(), round_function)?;
//         let value_query = MemoryQuery {
//             timestamp: timestamp_to_use_for_write,
//             memory_page: precompile_call_params.output_page,
//             memory_index: precompile_call_params.output_offset,
//             rw_flag: Boolean::constant(true),
//             value: written_value,
//             value_is_ptr: Boolean::constant(false),
//         };
//         let value_query = value_query.into_raw_query(cs)?;

//         precompile_call_params.output_offset = precompile_call_params
//             .output_offset
//             .increment_unchecked(cs)?;
//         let _ = memory_queue.push(cs, &value_query, &is_empty.not(), round_function)?;
//     }

//     // form the final state
//     let done = requests_queue.is_empty(cs)?;
//     structured_input.completion_flag = done;
//     structured_input.observable_output = PrecompileFunctionOutputData::empty();

//     let final_memory_state = memory_queue.into_state();
//     let final_requets_state = requests_queue.into_state();

//     structured_input.observable_output.final_memory_state =
//         FullSpongeLikeQueueState::conditionally_select(
//             cs,
//             &structured_input.completion_flag,
//             &final_memory_state,
//             &structured_input.observable_output.final_memory_state,
//         )?;

//     structured_input.hidden_fsm_output.log_queue_state = final_requets_state;
//     structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

//     if let Some(circuit_result) = structured_input.create_witness() {
//         if let Some(passed_input) = structured_input_witness {
//             assert_eq!(circuit_result, passed_input);
//         }
//     }

//     use crate::inputs::ClosedFormInputCompactForm;
//     let compact_form =
//         ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

//     // dbg!(compact_form.create_witness());
//     use crate::glue::optimizable_queue::commit_encodable_item;
//     let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
//     let input_committment_value = input_committment.get_value();
//     let public_input = AllocatedNum::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
//     public_input.enforce_equal(cs, &input_committment.get_variable())?;

//     Ok(public_input)
// }
