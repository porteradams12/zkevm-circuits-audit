//! Methods used in different tests in main_vm circuits.

use boojum::{
    cs::traits::cs::ConstraintSystem,
    field::goldilocks::GoldilocksField,
    gadgets::{
        boolean::Boolean, num::Num, traits::witnessable::CSWitnessable, u16::UInt16, u32::UInt32,
    },
    worker::Worker,
};
use zkevm_opcode_defs::{
    OPCODE_INPUT_VARIANT_FLAGS, OPCODE_OUTPUT_VARIANT_FLAGS, OPCODE_TYPE_BITS,
};

use crate::base_structures::{
    register::VMRegister,
    vm_state::{ArithmeticFlagsPort, FULL_SPONGE_QUEUE_STATE_WIDTH, REGISTERS_COUNT},
};

use super::{
    decoded_opcode::{OpcodePreliminaryDecoding, OpcodePropertiesDecoding, NUM_SRC_REGISTERS},
    opcode_bitmask::{OpcodeBitmask, OPCODE_FLAGS_BITS, OPCODE_VARIANT_BITS},
    pre_state::{AfterDecodingCarryParts, CommonOpcodeState, MemoryLocation, PendingSponge},
    register_input_view::RegisterInputView,
    state_diffs::StateDiffsAccumulator,
};

pub trait Testable {
    /// Creates a new object for unittests.
    fn test_default<CS: ConstraintSystem<GoldilocksField>>(cs: &mut CS) -> Self;
}

impl Testable for ArithmeticFlagsPort<GoldilocksField> {
    fn test_default<CS: ConstraintSystem<GoldilocksField>>(cs: &mut CS) -> Self {
        let boolean_false = Boolean::allocated_constant(cs, false);

        ArithmeticFlagsPort {
            overflow_or_less_than: boolean_false,
            equal: boolean_false,
            greater_than: boolean_false,
        }
    }
}

impl Testable for OpcodeBitmask<GoldilocksField> {
    fn test_default<CS: ConstraintSystem<GoldilocksField>>(cs: &mut CS) -> Self {
        let boolean_false = Boolean::allocated_constant(cs, false);

        OpcodeBitmask {
            opcode_type_booleans: [boolean_false; OPCODE_TYPE_BITS],
            opcode_variant_booleans: [boolean_false; OPCODE_VARIANT_BITS],
            flag_booleans: [boolean_false; OPCODE_FLAGS_BITS],
            input_variant_booleans: [boolean_false; OPCODE_INPUT_VARIANT_FLAGS],
            output_variant_booleans: [boolean_false; OPCODE_OUTPUT_VARIANT_FLAGS],
        }
    }
}

impl Testable for AfterDecodingCarryParts<GoldilocksField> {
    fn test_default<CS: ConstraintSystem<GoldilocksField>>(cs: &mut CS) -> Self {
        let boolean_false = Boolean::allocated_constant(cs, false);

        let zero_u32 = UInt32::zero(cs);
        let zero_u16: UInt16<GoldilocksField> = UInt16::zero(cs);
        let zero_num = Num::zero(cs);
        AfterDecodingCarryParts {
            did_skip_cycle: boolean_false,
            heap_page: zero_u32,
            aux_heap_page: zero_u32,
            next_pc: zero_u16,
            preliminary_ergs_left: zero_u32,
            src0_read_sponge_data: PendingSponge {
                initial_state: [zero_num; FULL_SPONGE_QUEUE_STATE_WIDTH],
                final_state: [zero_num; FULL_SPONGE_QUEUE_STATE_WIDTH],
                should_enforce: boolean_false,
            },
            dst0_memory_location: MemoryLocation {
                page: zero_u32,
                index: zero_u32,
            },
            dst0_performs_memory_access: boolean_false,
        }
    }
}

pub fn opcode_properties_for_opcode<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    opcode: zkevm_opcode_defs::Opcode,
) -> OpcodePropertiesDecoding<GoldilocksField> {
    let mut opcode_bitmask = OpcodeBitmask::test_default(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);

    let boolean_true = Boolean::allocated_constant(cs, true);

    match opcode {
        zkevm_opcode_defs::Opcode::Invalid(_) => todo!(),
        zkevm_opcode_defs::Opcode::Nop(_) => todo!(),
        zkevm_opcode_defs::Opcode::Add(_) => todo!(),
        zkevm_opcode_defs::Opcode::Sub(_) => todo!(),
        zkevm_opcode_defs::Opcode::Mul(_) => todo!(),
        zkevm_opcode_defs::Opcode::Div(_) => {
            opcode_bitmask.opcode_type_booleans[opcode.variant_idx()] = boolean_true
        }
        zkevm_opcode_defs::Opcode::Jump(_) => todo!(),
        zkevm_opcode_defs::Opcode::Context(_) => todo!(),
        zkevm_opcode_defs::Opcode::Shift(_) => {
            opcode_bitmask.opcode_type_booleans[opcode.variant_idx()] = boolean_true;
            opcode_bitmask.opcode_variant_booleans[opcode.materialize_subvariant_idx()] =
                boolean_true;
        }
        zkevm_opcode_defs::Opcode::Binop(_) => todo!(),
        zkevm_opcode_defs::Opcode::Ptr(_) => todo!(),
        zkevm_opcode_defs::Opcode::NearCall(_) => todo!(),
        zkevm_opcode_defs::Opcode::Log(_) => todo!(),
        zkevm_opcode_defs::Opcode::FarCall(_) => todo!(),
        zkevm_opcode_defs::Opcode::Ret(_) => todo!(),
        zkevm_opcode_defs::Opcode::UMA(_) => todo!(),
    };
    OpcodePropertiesDecoding {
        properties_bits: opcode_bitmask,
        src_regs_selectors: [[boolean_false; REGISTERS_COUNT]; NUM_SRC_REGISTERS],
        dst_regs_selectors: [[boolean_false; REGISTERS_COUNT]; NUM_SRC_REGISTERS],
        imm0: UInt16::zero(cs),
        imm1: UInt16::zero(cs),
    }
}

/// Creates a CommonOpcodeState struct, with concrete (small) values in the input registers.
pub fn common_opcode_state_with_values<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    reg0_imm: u16,
    reg1_imm: u16,
    decoded_opcode: OpcodePropertiesDecoding<GoldilocksField>,
) -> CommonOpcodeState<GoldilocksField> {
    let default_flag = ArithmeticFlagsPort::test_default(cs);
    let mut register_from_imm = |imm| {
        let imm_cs = UInt16::allocated_constant(cs, imm);
        VMRegister::<GoldilocksField>::from_imm(cs, imm_cs)
    };
    let reg0 = register_from_imm(reg0_imm);
    let reg1 = register_from_imm(reg1_imm);
    let zero_u32 = UInt32::zero(cs);

    CommonOpcodeState {
        reseted_flags: default_flag,
        current_flags: default_flag,
        decoded_opcode,
        src0: reg0,
        src1: reg1,
        src0_view: RegisterInputView::from_input_value(cs, &reg0),
        src1_view: RegisterInputView::from_input_value(cs, &reg1),
        timestamp_for_code_or_src_read: zero_u32,
        timestamp_for_first_decommit_or_precompile_read: zero_u32,
        timestamp_for_second_decommit_or_precompile_write: zero_u32,
        timestamp_for_dst_write: zero_u32,
    }
}

pub fn get_dst0_value<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    diffs_accumulator: &StateDiffsAccumulator<GoldilocksField>,
) -> u64 {
    let (_, should_apply, dst0) = diffs_accumulator.dst_0_values[0];

    assert_eq!(true, should_apply.get_witness(cs).wait().unwrap());

    dst0.value.get_witness(cs).wait().unwrap().as_u64()
}

pub fn get_dst1_value<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    diffs_accumulator: &StateDiffsAccumulator<GoldilocksField>,
) -> u64 {
    let (should_apply, dst1) = diffs_accumulator.dst_1_values[0];

    assert_eq!(true, should_apply.get_witness(cs).wait().unwrap());

    dst1.value.get_witness(cs).wait().unwrap().as_u64()
}
