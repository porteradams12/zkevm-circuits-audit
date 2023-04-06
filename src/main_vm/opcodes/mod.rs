use super::*;
use boojum::cs::gates::U8x4FMAGate;
use crate::base_structures::vm_state::VmLocalState;
use crate::main_vm::opcode_bitmask::SUPPORTED_ISA_VERSION;
use crate::main_vm::pre_state::AfterDecodingCarryParts;
use crate::main_vm::pre_state::CommonOpcodeState;
use crate::main_vm::state_diffs::StateDiffsAccumulator;
use zkevm_opcode_defs::*;

pub mod add_sub;
pub mod binop;
pub mod call_ret;
pub mod context;
pub mod jump;
pub mod log;
pub mod nop;
pub mod ptr;
pub mod mul_div;
pub mod shifts;
pub mod uma;

pub(crate) mod call_ret_impl;

pub use self::add_sub::*;
pub use self::binop::*;
pub use self::call_ret::*;
pub use self::context::*;
pub use self::ptr::*;
pub use self::shifts::*;
pub use self::mul_div::*;
pub use self::jump::*;
pub use self::log::*;
pub use self::nop::*;
pub use self::ptr::*;
pub use self::uma::*;

pub struct AddSubRelation<F: SmallField> {
    pub a: [UInt32<F>; 8],
    pub b: [UInt32<F>; 8],
    pub c: [UInt32<F>; 8],
    pub of: Boolean<F>,
}

impl<F: SmallField> Selectable<F> for AddSubRelation<F> {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let sel_a = UInt32::parallel_select(cs, flag, &a.a, &b.a);
        let sel_b = UInt32::parallel_select(cs, flag, &a.b, &b.b);
        let c = UInt32::parallel_select(cs, flag, &a.c, &b.c);
        let of = Boolean::conditionally_select(cs, flag, &a.of, &b.of);

        Self {
            a: sel_a, b: sel_b, c, of
        }
    }
}

pub struct MulDivRelation<F: SmallField> {
    pub a: [UInt32<F>; 8],
    pub b: [UInt32<F>; 8],
    pub rem: [UInt32<F>; 8],
    pub mul_low: [UInt32<F>; 8],
    pub mul_high: [UInt32<F>; 8]
}

impl<F: SmallField> Selectable<F> for MulDivRelation<F> {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let sel_a = UInt32::parallel_select(cs, flag, &a.a, &b.a);
        let sel_b = UInt32::parallel_select(cs, flag, &a.b, &b.b);
        let rem = UInt32::parallel_select(cs, flag, &a.rem, &b.rem);
        let mul_low = UInt32::parallel_select(cs, flag, &a.mul_low, &b.mul_low);
        let mul_high = UInt32::parallel_select(cs, flag, &a.mul_high, &b.mul_high);

        Self {
            a: sel_a, b: sel_b, rem, mul_low, mul_high
        }
    }
}

use boojum::cs::gates::UIntXAddGate;
use boojum::cs::gates::ConstantAllocatableCS;

pub(crate) fn enforce_addition_relation<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    relation: AddSubRelation<F>,
) {
    let AddSubRelation {
        a, b, c, of
    } = relation;
    if cs.gate_is_allowed::<UIntXAddGate<32>>() {
        let mut intermediate_of = cs.allocate_constant(F::ZERO);

        for ((a, b), c) in a.iter().zip(b.iter()).zip(c.iter()) {
            intermediate_of = UIntXAddGate::<32>::enforce_add_relation_compute_carry(
                cs,
                a.get_variable(),
                b.get_variable(),
                intermediate_of,
                c.get_variable(),
            );
        }

        let intermediate_of = unsafe { Boolean::from_variable_unchecked(intermediate_of) };

        Boolean::enforce_equal(cs, &intermediate_of, &of);
    } else {
        unimplemented!()
    }
}

pub(crate) fn enforce_mul_relation<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS, 
    relation: MulDivRelation<F>,
) {
    let MulDivRelation { a, b, rem, mul_low, mul_high } = relation;

    if cs.gate_is_allowed::<U8x4FMAGate>() {
        let mut partial_result = [UInt32::zero(cs); 16];
        partial_result[0..8].copy_from_slice(&rem[0..8]);
        for a_idx in 0..8 {
            let mut intermidiate_overflow = UInt32::zero(cs);
            for b_idx in 0..8 {
                let [low_wrapped, high_wrapped] = UInt32::fma_with_carry(
                    cs, a[a_idx], b[b_idx], partial_result[a_idx+b_idx], intermidiate_overflow
                );
                partial_result[a_idx+b_idx] = low_wrapped.0;
                intermidiate_overflow = high_wrapped.0;
            }  
        }
        for (lhs, rhs) in partial_result.iter().zip(mul_low.iter().chain(mul_high.iter())) {
            Num::enforce_equal(cs, &lhs.into_num(), &rhs.into_num())
        } 
    } else {
        unimplemented!()
    }
}

