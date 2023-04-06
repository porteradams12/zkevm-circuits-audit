use crate::main_vm::register_input_view::RegisterInputView;

use super::*;
use cs_derive::*;

pub mod far_call;
pub mod near_call;
pub mod ret;

pub use self::far_call::*;
pub use self::near_call::*;
pub use self::ret::*;

pub(crate) fn compute_shared_abi_parts<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    src0_view: &RegisterInputView<F>,
) -> (
    CommonCallRetABI<F>,
    FarCallPartialABI<F>,
    PartialRetABI<F>,
    FarCallForwardingMode<F>,
    RetForwardingMode<F>,
) {
    let far_call_abi = FarCallPartialABI::from_register_view(cs, src0_view);
    let ret_abi = PartialRetABI::from_register_view(cs, src0_view);

    // we can share some checks

    let use_aux_heap_marker =
        UInt8::allocated_constant(cs, FarCallForwardPageType::UseAuxHeap as u8);
    let forward_fat_pointer_marker =
        UInt8::allocated_constant(cs, FarCallForwardPageType::ForwardFatPointer as u8);

    let far_call_use_aux_heap =
        UInt8::equals(cs, &far_call_abi.forwarding_mode_byte, &use_aux_heap_marker);
    let far_call_forward_fat_pointer = UInt8::equals(
        cs,
        &far_call_abi.forwarding_mode_byte,
        &forward_fat_pointer_marker,
    );
    let far_call_use_heap =
        Boolean::multi_or(cs, &[far_call_use_aux_heap, far_call_forward_fat_pointer]).negated(cs);

    let ret_use_aux_heap =
        UInt8::equals(cs, &far_call_abi.forwarding_mode_byte, &use_aux_heap_marker);
    let ret_forward_fat_pointer = UInt8::equals(
        cs,
        &far_call_abi.forwarding_mode_byte,
        &forward_fat_pointer_marker,
    );
    let ret_use_heap =
        Boolean::multi_or(cs, &[ret_use_aux_heap, ret_forward_fat_pointer]).negated(cs);

    let (fat_ptr, upper_bound, ptr_validation_data) =
        FatPtrInABI::parse_and_validate(cs, src0_view);

    let common_parts = CommonCallRetABI {
        fat_ptr,
        upper_bound,
        ptr_validation_data,
    };

    let far_call_forwarding_mode = FarCallForwardingMode {
        use_heap: far_call_use_heap,
        use_aux_heap: far_call_use_aux_heap,
        forward_fat_pointer: far_call_forward_fat_pointer,
    };

    let ret_forwarding_mode = RetForwardingMode {
        use_heap: ret_use_heap,
        use_aux_heap: ret_use_aux_heap,
        forward_fat_pointer: ret_forward_fat_pointer,
    };

    (
        common_parts,
        far_call_abi,
        ret_abi,
        far_call_forwarding_mode,
        ret_forwarding_mode,
    )
}
