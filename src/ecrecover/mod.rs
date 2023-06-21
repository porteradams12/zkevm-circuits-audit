use super::*;
use crate::base_structures::log_query::*;
use crate::base_structures::memory_query::*;
use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::demux_log_queue::StorageLogQueue;
use crate::ecrecover::secp256k1::fixed_base_mul_table::FixedBaseMulTable;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::fsm_input_output::*;
use arrayvec::ArrayVec;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::crypto_bigint::{Zero, U1024};
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::curves::sw_projective::SWProjectivePoint;
use boojum::gadgets::curves::zeroable_affine::ZeroableAffinePoint;
use boojum::gadgets::keccak256::keccak256;
use boojum::gadgets::non_native_field::implementations::*;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::tables::And8Table;
use boojum::gadgets::traits::allocatable::{CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::gadgets::u16::UInt16;
use boojum::gadgets::u160::UInt160;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u512::UInt512;
use boojum::gadgets::u8::UInt8;
use boojum::pairing::GenericCurveAffine;
use boojum::pairing::{CurveAffine, GenericCurveProjective};
use boojum::sha3::digest::typenum::private::IsGreaterPrivate;
use cs_derive::*;
use ethereum_types::U256;
use std::collections::VecDeque;
use std::str::FromStr;
use std::sync::{Arc, RwLock};
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

pub mod input;
pub use self::input::*;

mod secp256k1;

pub const MEMORY_QUERIES_PER_CALL: usize = 4;

#[derive(Derivative, CSSelectable)]
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

// characteristics of the base field for secp curve
use self::secp256k1::fq::Fq as Secp256Fq;
// order of group of points for secp curve
use self::secp256k1::fr::Fr as Secp256Fr;
// some affine point
use self::secp256k1::PointAffine as Secp256Affine;

const NUM_WORDS: usize = 17;
const SECP_B_COEF: u64 = 7;
const EXCEPTION_FLAGS_ARR_LEN: usize = 8;
const NUM_MEMORY_READS_PER_CYCLE: usize = 4;
const X_POWERS_ARR_LEN: usize = 256;
const VALID_Y_IN_EXTERNAL_FIELD: u64 = 4;
const VALID_X_CUBED_IN_EXTERNAL_FIELD: u64 = 9;

type Secp256BaseNNFieldParams = NonNativeFieldOverU16Params<Secp256Fq, 17>;
type Secp256ScalarNNFieldParams = NonNativeFieldOverU16Params<Secp256Fr, 17>;

type Secp256BaseNNField<F> = NonNativeFieldOverU16<F, Secp256Fq, 17>;
type Secp256ScalarNNField<F> = NonNativeFieldOverU16<F, Secp256Fr, 17>;

pub fn secp256k1_base_field_params() -> Secp256BaseNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

pub fn secp256k1_scalar_field_params() -> Secp256ScalarNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

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
) -> (NonNativeFieldOverU16<F, P, N>, Boolean<F>)
where
    [(); N + 1]:,
{
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
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
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
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    };

    element
}

fn convert_field_element_to_uint256<
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: boojum::pairing::ff::PrimeField,
    const N: usize,
>(
    cs: &mut CS,
    mut elem: NonNativeFieldOverU16<F, P, N>,
) -> UInt256<F> {
    let mut limbs = [UInt32::<F>::zero(cs); 8];
    unsafe {
        for (dst, src) in limbs.iter_mut().zip(elem.limbs.array_chunks_mut::<2>()) {
            let low = UInt16::from_variable_unchecked(src[0]).to_le_bytes(cs);
            let high = UInt16::from_variable_unchecked(src[1]).to_le_bytes(cs);
            let mut bytes = [UInt8::<F>::zero(cs); 4];
            [low, high]
                .iter()
                .flatten()
                .enumerate()
                .for_each(|(i, el)| bytes[i] = *el);
            *dst = UInt32::from_le_bytes(cs, bytes);
        }
    }

    UInt256 { inner: limbs }
}

fn wnaf_scalar_mul<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut point: SWProjectivePoint<F, Secp256Affine, Secp256BaseNNField<F>>,
    mut scalar: Secp256ScalarNNField<F>,
) -> SWProjectivePoint<F, Secp256Affine, Secp256BaseNNField<F>> {
    let scalar_params = Arc::new(secp256k1_scalar_field_params());
    let pow_2_128 = U256::from_dec_str("340282366920938463463374607431768211456").unwrap();
    let pow_2_128 = UInt512::allocated_constant(cs, (pow_2_128, U256::zero()));
    let base_params = Arc::new(secp256k1_base_field_params());

    let beta = U256::from_str_radix(
        "7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee",
        16,
    )
    .unwrap();
    let v = UInt256::allocated_constant(cs, beta);
    let mut beta = convert_uint256_to_field_element(cs, &v, &base_params);

    let bigint_from_hex_str = |cs: &mut CS, s: &str| -> UInt512<F> {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt512::allocated_constant(cs, (v, U256::zero()))
    };

    let mut modulus_minus_one_div_two = bigint_from_hex_str(
        cs,
        "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0",
    );

    // Scalar decomposition
    let (k1_neg, mut k1, k2_neg, mut k2) = {
        let u256_from_hex_str = |cs: &mut CS, s: &str| -> UInt256<F> {
            let v = U256::from_str_radix(s, 16).unwrap();
            UInt256::allocated_constant(cs, v)
        };

        let a1 = u256_from_hex_str(cs, "0x3086d221a7d46bcde86c90e49284eb15");
        let b1 = u256_from_hex_str(cs, "0xe4437ed6010e88286f547fa90abfe4c3");
        let a2 = u256_from_hex_str(cs, "0x114ca50f7a8e2f3f657c1108d9d44cfd8");
        let b2 = a1.clone();

        let k = convert_field_element_to_uint256(cs, scalar.clone());

        let b2_times_k = k.widening_mul::<_, 8, 6>(cs, &b2);
        let b2_times_k = b2_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        let c1 = b2_times_k.0.to_high();

        let b1_times_k = k.widening_mul::<_, 8, 6>(cs, &b1);
        let b1_times_k = b1_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        let c2 = b1_times_k.0.to_high();

        let mut a1 = convert_uint256_to_field_element(cs, &a1, &scalar_params);
        let mut b1 = convert_uint256_to_field_element(cs, &b1, &scalar_params);
        let mut a2 = convert_uint256_to_field_element(cs, &a2, &scalar_params);
        let mut b2 = a1.clone();
        let mut c1 = convert_uint256_to_field_element(cs, &c1, &scalar_params);
        let mut c2 = convert_uint256_to_field_element(cs, &c2, &scalar_params);

        let mut c1_times_a1 = c1.mul(cs, &mut a1);
        let mut c2_times_a2 = c2.mul(cs, &mut a2);
        let mut k1 = scalar.sub(cs, &mut c1_times_a1).sub(cs, &mut c2_times_a2);
        k1.normalize(cs);
        let mut c2_times_b2 = c2.mul(cs, &mut b2);
        let mut k2 = c1.mul(cs, &mut b1).sub(cs, &mut c2_times_b2);
        k2.normalize(cs);

        let k1_u256 = convert_field_element_to_uint256(cs, k1.clone());
        let k2_u256 = convert_field_element_to_uint256(cs, k2.clone());
        let low_pow_2_128 = pow_2_128.to_low();
        let (_res, mut k1_neg) = k1_u256.overflowing_sub(cs, &low_pow_2_128);
        let k1_negated = k1.negated(cs);
        let k1 = <Secp256ScalarNNField<F> as NonNativeField<F, Secp256Fr>>::conditionally_select(
            cs,
            k1_neg,
            &k1,
            &k1_negated,
        );
        let (_res, mut k2_neg) = k2_u256.overflowing_sub(cs, &low_pow_2_128);
        let k2_negated = k2.negated(cs);
        let k2 = <Secp256ScalarNNField<F> as NonNativeField<F, Secp256Fr>>::conditionally_select(
            cs,
            k2_neg,
            &k2,
            &k2_negated,
        );

        (k1_neg, k1, k2_neg, k2)
    };

    // WNAF
    // The scalar multiplication window size.
    const GLV_WINDOW_SIZE: usize = 2;

    // The table size, used for w-ary NAF recoding.
    const TABLE_SIZE: u8 = 1 << (GLV_WINDOW_SIZE + 1);
    let table_size = UInt8::allocated_constant(cs, TABLE_SIZE);
    let half_table_size = UInt8::allocated_constant(cs, 1 << GLV_WINDOW_SIZE);
    let mask_for_mod_table_size = UInt8::allocated_constant(cs, TABLE_SIZE - 1);
    // The GLV table length.
    const L: usize = 1 << (GLV_WINDOW_SIZE - 1);

    let mut t1 = Vec::with_capacity(L);
    let (mut double, _) = point
        .double(cs)
        .convert_to_affine_or_default(cs, Secp256Affine::one());
    t1.push(point.clone());
    for i in 1..L {
        let next = t1[i - 1].add_mixed(cs, &mut double);
        t1.push(next);
    }

    let t1 = t1
        .iter_mut()
        .map(|el| el.convert_to_affine_or_default(cs, Secp256Affine::one()).0)
        .collect::<Vec<_>>();

    let t2 = t1
        .clone()
        .into_iter()
        .map(|mut el| (el.0.mul(cs, &mut beta), el.1))
        .collect::<Vec<_>>();

    let and_table_id = cs
        .get_table_id_for_marker::<And8Table>()
        .expect("table must exist");

    let mod_signed = |cs: &mut CS, d_byte: UInt8<F>| {
        let d_mod_window_size = unsafe {
            UInt8::from_variable_unchecked(
                cs.perform_lookup::<2, 1>(
                    and_table_id,
                    &[
                        d_byte.get_variable(),
                        mask_for_mod_table_size.get_variable(),
                    ],
                )[0],
            )
        };
        let (d_mod_window_size_minus_table, _) = d_mod_window_size.overflowing_sub(cs, &table_size);
        let (_, overflow) = d_mod_window_size.overflowing_sub(cs, &half_table_size);
        Selectable::conditionally_select(
            cs,
            overflow,
            &d_mod_window_size,
            &d_mod_window_size_minus_table,
        )
    };
    let zero = UInt8::zero(cs);
    let overflow_checker = UInt8::allocated_constant(cs, 2u8.pow(7));
    let to_wnaf = |cs: &mut CS, e: Secp256ScalarNNField<F>, neg: Boolean<F>| -> Vec<UInt8<F>> {
        let mut naf = vec![];
        let mut e = convert_field_element_to_uint256(cs, e);
        // Loop for max amount of bits in e to ensure homogenous circuit
        for _ in 0..129 {
            let is_odd = e.is_odd(cs);
            let first_byte = e.inner[0].to_le_bytes(cs)[0];
            let naf_sign = mod_signed(cs, first_byte);
            let (_, naf_sign_is_positive) = naf_sign.overflowing_sub(cs, &overflow_checker);
            let neg_naf_sign = naf_sign.negate(cs);
            let naf_value = Selectable::conditionally_select(
                cs,
                naf_sign_is_positive,
                &naf_sign,
                &neg_naf_sign,
            );
            let naf_value_u32 =
                unsafe { UInt32::from_variable_unchecked(naf_value.get_variable()) };
            let (added, _) = e.inner[0].overflowing_add(cs, naf_value_u32);
            let (subbed, _) = e.inner[0].overflowing_sub(cs, naf_value_u32);
            let e_inner_value =
                Selectable::conditionally_select(cs, naf_sign_is_positive, &subbed, &added);
            e.inner[0] = Selectable::conditionally_select(cs, is_odd, &e_inner_value, &e.inner[0]);
            let next = Selectable::conditionally_select(cs, is_odd, &naf_sign, &zero);

            let next_neg = next.negate(cs);
            let next = Selectable::conditionally_select(cs, neg, &next, &next_neg);
            naf.push(next);

            e = e.div2(cs);
        }

        naf
    };

    let naf_add =
        |cs: &mut CS,
         table: &[(Secp256BaseNNField<F>, Secp256BaseNNField<F>)],
         naf: UInt8<F>,
         acc: &mut SWProjectivePoint<F, Secp256Affine, Secp256BaseNNField<F>>| {
            let is_zero = naf.is_zero(cs);
            let mut coords = &table[(naf.abs(cs).div2(cs)).witness_hook(cs)().unwrap() as usize];
            let mut p_1 =
                SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::from_xy_unchecked(
                    cs,
                    coords.0.clone(),
                    coords.1.clone(),
                );
            let (_, naf_is_positive) = naf.overflowing_sub(cs, &overflow_checker);
            let p_1_neg = p_1.negated(cs);
            p_1 = Selectable::conditionally_select(cs, naf_is_positive, &p_1, &p_1_neg);
            let acc_added = acc.add_mixed(cs, &mut (p_1.x, p_1.y));
            *acc = Selectable::conditionally_select(cs, is_zero, &acc, &acc_added);
        };

    let naf1 = to_wnaf(cs, k1, k1_neg);
    let naf2 = to_wnaf(cs, k2, k2_neg);
    let mut acc =
        SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::zero(cs, &base_params);
    for i in (0..129).rev() {
        naf_add(cs, &t1, naf1[i], &mut acc);
        naf_add(cs, &t2, naf2[i], &mut acc);
        if i != 0 {
            acc = acc.double(cs);
        }
    }

    acc
}

fn ecrecover_precompile_inner_routine<F: SmallField, CS: ConstraintSystem<F>>(
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

    let mut curve_b_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, curve_b, &base_field_params);
    let mut minus_one_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, minus_one, &base_field_params);

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

    let [y_is_odd, x_overflow, ..] =
        Num::<F>::from_variable(recid.get_variable()).spread_into_bits::<_, 8>(cs);

    let (r_plus_n, of) = r.overflowing_add(cs, &secp_n_u256);
    let mut x_as_u256 = UInt256::conditionally_select(cs, x_overflow, &r_plus_n, &r);
    let error = Boolean::multi_and(cs, &[x_overflow, of]);
    exception_flags.push(error);

    // we handle x separately as it is the only element of base field of a curve (not a scalar field element!)
    // check that x < q - order of base point on Secp256 curve
    // if it is not actually the case - mask x to be zero
    let (_res, is_in_range) = x_as_u256.overflowing_sub(cs, &secp_p_u256);
    x_as_u256 = x_as_u256.mask(cs, is_in_range);
    let x_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(x_is_not_in_range);

    let mut x_fe = convert_uint256_to_field_element(cs, &x_as_u256, &base_field_params);

    let (mut r_fe, r_is_zero) =
        convert_uint256_to_field_element_masked(cs, &r, &scalar_field_params);
    exception_flags.push(r_is_zero);
    let (mut s_fe, s_is_zero) =
        convert_uint256_to_field_element_masked(cs, &s, &scalar_field_params);
    exception_flags.push(s_is_zero);

    // NB: although it is not strictly an exception we also assume that hash is never zero as field element
    let (mut message_hash_fe, message_hash_is_zero) =
        convert_uint256_to_field_element_masked(cs, &message_hash, &scalar_field_params);
    exception_flags.push(message_hash_is_zero);

    // curve equation is y^2 = x^3 + b
    // we compute t = r^3 + b and check if t is a quadratic residue or not.
    // we do this by computing Legendre symbol (t, p) = t^[(p-1)/2] (mod p)
    //           p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
    // n = (p-1)/2 = 2^255 - 2^31 - 2^8 - 2^7 - 2^6 - 2^5 - 2^3 - 1
    // we have to compute t^b = t^{2^255} / ( t^{2^31} * t^{2^8} * t^{2^7} * t^{2^6} * t^{2^5} * t^{2^3} * t)
    // if t is not a quadratic residue we return error and replace x by another value that will make
    // t = x^3 + b a quadratic residue

    let mut t = x_fe.square(cs);
    t = t.mul(cs, &mut x_fe);
    t = t.lazy_add(cs, &mut curve_b_nn);

    let t_is_zero = t.is_zero(cs);
    exception_flags.push(t_is_zero);

    // if t is zero then just mask
    let t = Selectable::conditionally_select(cs, t_is_zero, &valid_t_in_external_field, &t);

    // array of powers of t of the form t^{2^i} starting from i = 0 to 255
    let mut t_powers = Vec::with_capacity(X_POWERS_ARR_LEN);
    t_powers.push(t);

    for _ in 1..X_POWERS_ARR_LEN {
        let prev = t_powers.last_mut().unwrap();
        let next = prev.square(cs);
        t_powers.push(next);
    }

    let mut acc = t_powers[0].clone();
    for idx in [3, 5, 6, 7, 8, 31].into_iter() {
        let other = &mut t_powers[idx];
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
    may_be_recovered_y.normalize(cs);
    let mut may_be_recovered_y_negated = may_be_recovered_y.negated(cs);

    let [lowest_bit, ..] =
        Num::<F>::from_variable(may_be_recovered_y.limbs[0]).spread_into_bits::<_, 16>(cs);

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
    let x =
        Selectable::conditionally_select(cs, t_is_nonresidue, &valid_x_in_external_field, &x_fe);
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

    // now we are going to compute the public key Q = (x, y) determined by the formula:
    // Q = (s * X - hash * G) / r which is equivalent to r * Q = s * X - hash * G

    let mut recovered_point =
        SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::from_xy_unchecked(cs, x, y);
    // now we do multiplication
    let mut s_times_x = wnaf_scalar_mul(cs, recovered_point.clone(), s_by_r_inv.clone());
    let (mut s_times_x_affine, _) =
        s_times_x.convert_to_affine_or_default(cs, Secp256Affine::one());

    let mut hash_times_g = {
        let bytes = message_hash_by_r_inv
            .limbs
            .iter()
            .flat_map(|el| unsafe { UInt16::from_variable_unchecked(*el).to_le_bytes(cs) })
            .collect::<Vec<UInt8<F>>>();

        let ids = vec![
            cs.get_table_id_for_marker::<FixedBaseMulTable<0>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<1>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<2>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<3>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<4>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<5>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<6>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<7>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<8>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<9>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<10>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<11>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<12>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<13>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<14>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<FixedBaseMulTable<15>>()
                .expect("table must exist"),
        ];
        let mut acc = SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::zero(
            cs,
            base_field_params,
        );
        bytes[..32].iter().enumerate().rev().for_each(|(i, el)| {
            let index = UInt8::allocated_constant(cs, i as u8).get_variable();
            let chunks = ids
                .iter()
                .map(|id| unsafe {
                    UInt32::from_variable_unchecked(
                        cs.perform_lookup::<2, 1>(*id, &[el.get_variable(), index])[0],
                    )
                })
                .collect::<Vec<UInt32<F>>>();
            let mut x = [UInt32::zero(cs); 8];
            x.copy_from_slice(&chunks[..8]);
            let x = UInt256 { inner: x };
            let x = convert_uint256_to_field_element(cs, &x, base_field_params);
            let mut y = [UInt32::zero(cs); 8];
            y.copy_from_slice(&chunks[8..]);
            let y = UInt256 { inner: y };
            let y = convert_uint256_to_field_element(cs, &y, base_field_params);
            acc = acc.add_mixed(cs, &mut (x, y));
        });
        acc
    };

    let (mut q_acc, _) = hash_times_g.convert_to_affine_or_default(cs, Secp256Affine::one());
    let mut q_acc = s_times_x.add_mixed(cs, &mut q_acc);

    let ((mut q_x, mut q_y), is_infinity) =
        q_acc.convert_to_affine_or_default(cs, Secp256Affine::one());
    exception_flags.push(is_infinity);
    let any_exception = Boolean::multi_or(cs, &exception_flags[..]);

    let zero_u8 = UInt8::zero(cs);

    let mut bytes_to_hash = [zero_u8; 64];
    let it = q_x.limbs[..16]
        .iter()
        .rev()
        .chain(q_y.limbs[..16].iter().rev());

    for (dst, src) in bytes_to_hash.array_chunks_mut::<2>().zip(it) {
        let limb = unsafe { UInt16::from_variable_unchecked(*src) };
        *dst = limb.to_be_bytes(cs);
    }

    let mut digest_bytes = keccak256(cs, &bytes_to_hash);
    // digest is 32 bytes, but we need only 20 to recover address
    digest_bytes[0..12].copy_from_slice(&[zero_u8; 12]); // empty out top bytes
    digest_bytes.reverse();
    let written_value_unmasked = UInt256::from_le_bytes(cs, digest_bytes);

    let written_value = written_value_unmasked.mask_negated(cs, any_exception);
    let all_ok = any_exception.negated(cs);

    (all_ok, written_value)
}

pub fn ecrecover_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: EcrecoverCircuitInstanceWitness<F>,
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

    let EcrecoverCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;

    let memory_reads_witness: VecDeque<_> = memory_reads_witness.into_iter().flatten().collect();

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::ECRECOVER_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS,
    );
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    let scalar_params = Arc::new(secp256k1_scalar_field_params());
    let base_params = Arc::new(secp256k1_base_field_params());

    use boojum::pairing::ff::PrimeField;

    let valid_x_in_external_field = Secp256BaseNNField::allocated_constant(
        cs,
        Secp256Fq::from_str(&VALID_X_CUBED_IN_EXTERNAL_FIELD.to_string()).unwrap(),
        &base_params,
    );
    let valid_t_in_external_field = Secp256BaseNNField::allocated_constant(
        cs,
        Secp256Fq::from_str(&(VALID_X_CUBED_IN_EXTERNAL_FIELD + SECP_B_COEF).to_string()).unwrap(),
        &base_params,
    );
    let valid_y_in_external_field = Secp256BaseNNField::allocated_constant(
        cs,
        Secp256Fq::from_str(&VALID_Y_IN_EXTERNAL_FIELD.to_string()).unwrap(),
        &base_params,
    );

    let mut structured_input =
        EcrecoverCircuitInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
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
            EcrecoverPrecompileCallParams::from_encoding(cs, request.key);

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

        let mut read_values = [zero_u256; NUM_MEMORY_READS_PER_CYCLE];
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

        let [message_hash_as_u256, v_as_u256, r_as_u256, s_as_u256] = read_values;
        let rec_id = v_as_u256.inner[0].to_le_bytes(cs)[0];

        let (success, written_value) = ecrecover_precompile_inner_routine(
            cs,
            &rec_id,
            &r_as_u256,
            &s_as_u256,
            &message_hash_as_u256,
            valid_x_in_external_field.clone(),
            valid_y_in_external_field.clone(),
            valid_t_in_external_field.clone(),
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
    use boojum::pairing::ff::{Field, PrimeField, SqrtField};
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

    use crate::ecrecover::secp256k1::fixed_base_mul_table::{
        create_fixed_base_mul_table, FixedBaseMulTable,
    };
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
        let max_trace_len = 1 << 21;

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
            let builder = U8x4FMAGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
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
            let builder = UIntXAddGate::<8>::configure_builder(
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

        let table = create_or8_table();
        owned_cs.add_lookup_table::<Or8Table, 3>(table);

        let table = create_div_two8_table();
        owned_cs.add_lookup_table::<DivTwo8Table, 3>(table);

        let table = create_fixed_base_mul_table::<F, 0>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<0>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 1>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<1>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 2>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<2>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 3>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<3>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 4>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<4>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 5>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<5>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 6>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<6>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 7>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<7>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 8>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<8>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 9>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<9>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 10>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<10>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 11>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<11>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 12>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<12>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 13>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<13>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 14>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<14>, 3>(table);
        let table = create_fixed_base_mul_table::<F, 15>();
        owned_cs.add_lookup_table::<FixedBaseMulTable<15>, 3>(table);

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

        let scalar_params = secp256k1_scalar_field_params();
        let base_params = secp256k1_base_field_params();

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

        let (no_error, digest) = ecrecover_precompile_inner_routine(
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

    #[test]
    fn test_wnaf() {
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
            let builder = U8x4FMAGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
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

        let table = create_div_two8_table();
        owned_cs.add_lookup_table::<DivTwo8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);
        let table = create_byte_split_table::<F, 7>();
        owned_cs.add_lookup_table::<ByteSplitTable<7>, 3>(table);

        let cs = &mut owned_cs;

        let scalar_params = Arc::new(secp256k1_scalar_field_params());
        let base_params = Arc::new(secp256k1_base_field_params());

        let scalar = U256::from_str_radix(
            "0xba970c512de6508041367fb69be09645a349114b310046a1dc08db8d1da17f86",
            16,
        )
        .unwrap();
        let scalar = UInt256::allocated_constant(cs, scalar);
        let scalar = convert_uint256_to_field_element(cs, &scalar, &scalar_params);

        let x = U256::from_str_radix(
            "0x8c06f833d40cd2042ea492789a4d11271bcb10f9c9aaf16c49df53ea67f6cb9b",
            16,
        )
        .unwrap();
        let y = U256::from_str_radix(
            "0x7489a93e12cba4b822fdd7ad07a6c5b415d811c59fca45d47a09fd20afb177be",
            16,
        )
        .unwrap();
        let x = UInt256::allocated_constant(cs, x);
        let y = UInt256::allocated_constant(cs, y);
        let x = convert_uint256_to_field_element(cs, &x, &base_params);
        let y = convert_uint256_to_field_element(cs, &y, &base_params);
        let point = SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::from_xy_unchecked(
            cs, x, y,
        );

        wnaf_scalar_mul(cs, point, scalar);
        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_standard_mul() {
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
            let builder = U8x4FMAGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
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

        let table = create_div_two8_table();
        owned_cs.add_lookup_table::<DivTwo8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);
        let table = create_byte_split_table::<F, 7>();
        owned_cs.add_lookup_table::<ByteSplitTable<7>, 3>(table);

        let cs = &mut owned_cs;

        let scalar_params = Arc::new(secp256k1_scalar_field_params());
        let base_params = Arc::new(secp256k1_base_field_params());

        let scalar = U256::from_str_radix(
            "0xba970c512de6508041367fb69be09645a349114b310046a1dc08db8d1da17f86",
            16,
        )
        .unwrap();
        let scalar = UInt256::allocated_constant(cs, scalar);
        let scalar = convert_uint256_to_field_element(cs, &scalar, &scalar_params);

        let x = U256::from_str_radix(
            "0x8c06f833d40cd2042ea492789a4d11271bcb10f9c9aaf16c49df53ea67f6cb9b",
            16,
        )
        .unwrap();
        let y = U256::from_str_radix(
            "0x7489a93e12cba4b822fdd7ad07a6c5b415d811c59fca45d47a09fd20afb177be",
            16,
        )
        .unwrap();
        let x = UInt256::allocated_constant(cs, x);
        let y = UInt256::allocated_constant(cs, y);
        let x = convert_uint256_to_field_element(cs, &x, &base_params);
        let y = convert_uint256_to_field_element(cs, &y, &base_params);
        let point = SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::from_xy_unchecked(
            cs, x, y,
        );

        let mut s_times_x =
            SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::zero(cs, &base_params);

        let s_by_r_inv_bits: Vec<_> = scalar
            .limbs
            .iter()
            .map(|el| Num::<F>::from_variable(*el).spread_into_bits::<_, 16>(cs))
            .flatten()
            .collect();
        for (cycle, x_bit) in s_by_r_inv_bits.into_iter().rev().enumerate() {
            if cycle != 0 {
                s_times_x = s_times_x.double(cs);
            }
            let q_plus_x = s_times_x.add_mixed(cs, &mut (point.x.clone(), point.y.clone()));
            s_times_x = Selectable::conditionally_select(cs, x_bit, &q_plus_x, &s_times_x);
        }
        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
