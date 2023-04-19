use arrayvec::ArrayVec;

use super::opcodes::context::apply_context;
use super::pre_state::{create_prestate, PendingSponge};
use super::state_diffs::{StateDiffsAccumulator, MAX_ADD_SUB_RELATIONS_PER_CYCLE, MAX_MUL_DIV_RELATIONS_PER_CYCLE};
use super::*;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::CSGeometry;
use boojum::field::goldilocks::GoldilocksField;
use boojum::gadgets::poseidon::CircuitRoundFunction;
use boojum::gadgets::traits::allocatable::CSAllocatableExt;
use boojum::gadgets::traits::selectable::MultiSelectable;
use boojum::gadgets::u256::{UInt256, recompose_u256_as_u32x8};
use crate::base_structures::decommit_query::DecommitQuery;
use crate::base_structures::log_query::LogQuery;
use crate::base_structures::memory_query::{self, MemoryQuery};
use crate::base_structures::register::VMRegister;
use crate::base_structures::vm_state::callstack::Callstack;
use crate::base_structures::vm_state::saved_context::ExecutionContextRecord;
use crate::base_structures::vm_state::{GlobalContext, ArithmeticFlagsPort};
use crate::base_structures::vm_state::{VmLocalState, FULL_SPONGE_QUEUE_STATE_WIDTH};
use crate::main_vm::opcodes::*;
use crate::main_vm::witness_oracle::SynchronizedWitnessOracle;
use crate::main_vm::witness_oracle::WitnessOracle;
use boojum::cs::traits::cs::DstBuffer;

pub(crate) fn vm_cycle<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    W: WitnessOracle<F>,
>(
    cs: &mut CS,
    current_state: VmLocalState<F>,
    witness_oracle: &SynchronizedWitnessOracle<F, W>,
    global_context: &GlobalContext<F>,
    round_function: &R,
) -> VmLocalState<F>
where
    [(); <ExecutionContextRecord<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    // first we create a pre-state

    // if let Some(initial_state) = (current_state.witness_hook(&*cs))() {
    //     dbg!(&initial_state);
    // }

    let (draft_next_state, common_opcode_state, opcode_carry_parts) =
        create_prestate(cs, current_state, witness_oracle, round_function);

    // if let Some(wit) = (common_opcode_state.witness_hook(&*cs))() {
    //     dbg!(&wit);
    // }

    // then we apply each opcode and accumulate state diffs

    let mut diffs_accumulator = StateDiffsAccumulator::<F>::default();

    apply_nop(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_add_sub(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_jump(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_binop(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_context(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_ptr(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
    );
    apply_log(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
        witness_oracle,
        round_function,
    );
    apply_calls_and_ret(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
        witness_oracle,
        global_context,
        round_function,
    );
    apply_mul_div(
        cs, 
        &draft_next_state, 
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator
    );
    apply_shifts(
        cs, 
        &draft_next_state, 
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator
    );
    apply_uma(
        cs,
        &draft_next_state,
        &common_opcode_state,
        &opcode_carry_parts,
        &mut diffs_accumulator,
        witness_oracle,
        round_function,
    );

    // and finally apply state diffs

    let mut new_state = draft_next_state;

    let mut write_dst0_bools = ArrayVec::<Boolean<F>, 8>::new();
    for el in diffs_accumulator.dst_0_values.iter() {
        if el.0 {
            write_dst0_bools.push(el.1);
        }
    }
    // potentially we can have registers that update DST0 as memory location,
    // so we choose only cases where it's indeed into memory.
    // It is only a possibility for now. Later we will predicate it based on the
    // decoded opcode properties
    let dst0_update_potentially_to_memory = Boolean::multi_or(cs, &write_dst0_bools);

    // select dst0 and dst1 values

    let mut can_update_dst0_as_register_only = ArrayVec::<Boolean<F>, 8>::new();
    let mut should_update_dst1 = ArrayVec::<Boolean<F>, 8>::new();

    // for DST0 it's possible to have opcode-constrainted updates only into registers
    for el in diffs_accumulator.dst_0_values.iter() {
        if el.0 == false {
            can_update_dst0_as_register_only.push(el.1);
        }
    }
    for el in diffs_accumulator.dst_1_values.iter() {
        should_update_dst1.push(el.0);
    }

    let can_update_dst0_as_register_only =
        Boolean::multi_or(cs, &can_update_dst0_as_register_only);

    let mut dst0_is_ptr_candidates_iter = diffs_accumulator
        .dst_0_values
        .iter()
        .map(|el| (el.1, el.2.is_pointer));
    let mut dst0_value_candidates_iter = diffs_accumulator
        .dst_0_values
        .iter()
        .map(|el| (el.1, el.2.value));
    let num_candidates_len = dst0_is_ptr_candidates_iter.len();

    let dst0_is_ptr = dst0_is_ptr_candidates_iter.next().expect("is some").1;
    let dst0_value = dst0_value_candidates_iter.next().expect("is some").1;

    let dst0_is_ptr = Boolean::multiselect(
        cs,
        &dst0_is_ptr,
        &mut dst0_is_ptr_candidates_iter,
        num_candidates_len - 1,
    );
    let dst0_value = UInt256::multiselect(
        cs,
        &dst0_value,
        &mut dst0_value_candidates_iter,
        num_candidates_len - 1,
    );

    let mut dst1_is_ptr_candidates_iter = diffs_accumulator
        .dst_0_values
        .iter()
        .map(|el| (el.1, el.2.is_pointer));
    let mut dst1_value_candidates_iter = diffs_accumulator
        .dst_0_values
        .iter()
        .map(|el| (el.1, el.2.value));
    let num_candidates_len = dst1_is_ptr_candidates_iter.len();

    let dst1_is_ptr = dst1_is_ptr_candidates_iter.next().expect("is some").1;
    let dst1_value = dst1_value_candidates_iter.next().expect("is some").1;

    let dst1_is_ptr = Boolean::multiselect(
        cs,
        &dst1_is_ptr,
        &mut dst1_is_ptr_candidates_iter,
        num_candidates_len - 1,
    );
    let dst1_value = UInt256::multiselect(
        cs,
        &dst1_value,
        &mut dst1_value_candidates_iter,
        num_candidates_len - 1,
    );
    
    let perform_dst0_memory_write_update = Boolean::multi_and(
        cs,
        &[
            opcode_carry_parts.dst0_performs_memory_access,
            dst0_update_potentially_to_memory,
        ],
    );

    // We know that UMA opcodes (currently by design) are not allowed to write dst argument into memory
    // in any form, so if we do the write here we always base on the state of memory from prestate

    let memory_queue_tail_for_dst0_write = draft_next_state.memory_queue_state;
    let memory_queue_length_for_dst0_write = draft_next_state.memory_queue_length;

    let dst0 = VMRegister {
        is_pointer: dst0_is_ptr,
        value: dst0_value,
    };

    let (
        (dst0_write_initial_state_to_enforce, dst0_write_final_state_to_enforce),
        new_memory_queue_tail,
        new_memory_queue_len,
    ) = may_be_write_memory(
        cs,
        &perform_dst0_memory_write_update,
        &dst0,
        &common_opcode_state.timestamp_for_dst_write,
        &opcode_carry_parts.dst0_memory_location,
        &memory_queue_tail_for_dst0_write,
        &memory_queue_length_for_dst0_write,
        witness_oracle,
        round_function,
    );

    // update tail in next state candidate
    new_state.memory_queue_state = new_memory_queue_tail;
    new_state.memory_queue_length = new_memory_queue_len;

    // if dst0 is not in memory then update

    let boolean_false = Boolean::allocated_constant(cs, false);
    let _boolean_true = Boolean::allocated_constant(cs, true);
    let zero_u256 = UInt256::zero(cs);

    // do at once for dst0 and dst1

    // case when we want to update DST0 from potentially memory-writing opcodes,
    // but we address register in fact

    let dst0_performs_reg_update = opcode_carry_parts.dst0_performs_memory_access.negated(cs);
    let t = Boolean::multi_and(
        cs,
        &[
            dst0_performs_reg_update,
            dst0_update_potentially_to_memory,
        ],
    );

    let dst0_update_register =
        Boolean::multi_or(cs, &[can_update_dst0_as_register_only, t]);

    for (idx, (flag_dst0, flag_dst1)) in common_opcode_state.decoded_opcode.dst_regs_selectors[0]
        .iter()
        .zip(common_opcode_state.decoded_opcode.dst_regs_selectors[1].iter())
        .enumerate()
    {
        // form an iterator for all possible candidates
        let write_as_dst0 =
            Boolean::multi_and(cs, &[dst0_update_register, *flag_dst0]);
        // dst1 is always register
        let write_as_dst1 = *flag_dst1;

        // unfortunately we can not use iter chaining here due to syntax constraint
        let mut apply_ptr_update = ArrayVec::<Boolean<F>, 32>::new();
        let mut apply_value_update = ArrayVec::<Boolean<F>, 32>::new();
        let mut it_is_ptr = ArrayVec::<(Boolean<F>, Boolean<F>), 32>::new();
        let mut it_value = ArrayVec::<(Boolean<F>, UInt256<F>), 32>::new();

        apply_ptr_update.push(write_as_dst0);
        apply_ptr_update.push(write_as_dst1);

        apply_value_update.push(write_as_dst0);
        apply_value_update.push(write_as_dst1);

        it_is_ptr.push((write_as_dst0, dst0_is_ptr));
        it_value.push((write_as_dst0, dst0_value));

        it_is_ptr.push((write_as_dst1, dst1_is_ptr));
        it_value.push((write_as_dst1, dst1_value));

        // then chain all specific register updates
        for specific_update in diffs_accumulator.specific_registers_updates[idx].drain(..) {
            apply_ptr_update.push(specific_update.0);
            apply_value_update.push(specific_update.0);
            it_is_ptr.push((specific_update.0, specific_update.1.is_pointer));
            it_value.push((specific_update.0, specific_update.1.value));
        }

        // chain removal of pointer markers at once
        let mut tmp = ArrayVec::<Boolean<F>, 16>::new();
        for remove_ptr_request in diffs_accumulator.remove_ptr_on_specific_registers[idx].drain(..)
        {
            tmp.push(remove_ptr_request);
        }

        if tmp.is_empty() == false {
            let remove_ptr_marker = Boolean::multi_or(cs, &tmp);
            apply_ptr_update.push(remove_ptr_marker);
            it_is_ptr.push((remove_ptr_marker, boolean_false));
        }

        // chain zeroing at once
        let mut tmp = ArrayVec::<Boolean<F>, 16>::new();
        for zeroing_requests in diffs_accumulator.specific_registers_zeroing[idx].drain(..) {
            tmp.push(zeroing_requests);
        }

        if tmp.is_empty() == false {
            let zero_out_reg = Boolean::multi_or(cs, &tmp);
            apply_value_update.push(zero_out_reg);
            it_value.push((zero_out_reg, zero_u256));
        }

        let any_ptr_update = Boolean::multi_or(cs, &apply_ptr_update);
        let any_value_update = Boolean::multi_or(cs, &apply_value_update);

        let keep_is_ptr = any_ptr_update.negated(cs);
        let keep_value = any_value_update.negated(cs);

        // add current reg values
        it_is_ptr.push((keep_is_ptr, new_state.registers[idx].is_pointer));
        it_value.push((keep_value, new_state.registers[idx].value));

        let num_candidates = it_is_ptr.len();
        let is_ptr_baseline = boolean_false;
        new_state.registers[idx].is_pointer = Boolean::multiselect(
            cs,
            &is_ptr_baseline,
            it_is_ptr.into_iter(),
            num_candidates,
        );

        let num_candidates = it_value.len();
        let value_baseline = zero_u256;
        new_state.registers[idx].value = UInt256::multiselect(
            cs,
            &value_baseline,
            it_value.into_iter(),
            num_candidates,
        );
    }

    // apply smaller changes to VM state, such as ergs left, etc

    // PC
    for (flag, value) in diffs_accumulator.new_pc_candidates.drain(..) {
        new_state.callstack.current_context.saved_context.pc = UInt16::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.callstack.current_context.saved_context.pc
        );
    }

    // Ergs
    for (flag, value) in diffs_accumulator.new_ergs_left_candidates.drain(..) {
        new_state.callstack.current_context.saved_context.ergs_remaining = UInt32::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.callstack.current_context.saved_context.ergs_remaining
        );
    }

    // Ergs per pubdata
    for (flag, value) in diffs_accumulator.new_ergs_per_pubdata.into_iter() {
        new_state.ergs_per_pubdata_byte = UInt32::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.ergs_per_pubdata_byte
        );
    }

    // Tx number in block
    for (flag, value) in diffs_accumulator.new_tx_number.into_iter() {
        new_state.tx_number_in_block = UInt32::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.tx_number_in_block
        );
    }

    // Page counter
    new_state.memory_page_counter = diffs_accumulator.memory_page_counters.expect("is some");

    // Context value
    for (flag, value) in diffs_accumulator.context_u128_candidates.drain(..) {
        new_state.context_composite_u128 = UInt32::parallel_select(
            cs, 
            flag, 
            &value, 
            &new_state.context_composite_u128
        );
    }

    // Heap limit
    for (flag, value) in diffs_accumulator.new_heap_bounds.drain(..) {
        new_state.callstack.current_context.saved_context.heap_upper_bound = UInt32::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.callstack.current_context.saved_context.heap_upper_bound
        );
    }

    // Axu heap limit
    for (flag, value) in diffs_accumulator.new_aux_heap_bounds.drain(..) {
        new_state.callstack.current_context.saved_context.aux_heap_upper_bound = UInt32::conditionally_select(
            cs, 
            flag, 
            &value, 
            &new_state.callstack.current_context.saved_context.aux_heap_upper_bound
        );
    }

    // variable queue states 

    // Memory due to UMA
    for (flag, length, state) in diffs_accumulator.memory_queue_candidates.into_iter() {
        new_state.memory_queue_length = UInt32::conditionally_select(
            cs, 
            flag, 
            &length, 
            &new_state.memory_queue_length
        );

        new_state.memory_queue_state = Num::parallel_select(
            cs, 
            flag, 
            &state, 
            &new_state.memory_queue_state
        );
    }

    // decommittment due to far call
    for (flag, length, state) in diffs_accumulator.decommitment_queue_candidates.into_iter() {
        new_state.code_decommittment_queue_length = UInt32::conditionally_select(
            cs, 
            flag, 
            &length, 
            &new_state.code_decommittment_queue_length
        );

        new_state.code_decommittment_queue_state = Num::parallel_select(
            cs, 
            flag, 
            &state, 
            &new_state.code_decommittment_queue_state
        );
    }

    // forward storage log
    for (flag, length, state) in diffs_accumulator.log_queue_forward_candidates.into_iter() {
        new_state.callstack.current_context.log_queue_forward_part_length = UInt32::conditionally_select(
            cs, 
            flag, 
            &length, 
            &new_state.callstack.current_context.log_queue_forward_part_length
        );

        new_state.callstack.current_context.log_queue_forward_tail = Num::parallel_select(
            cs, 
            flag, 
            &state, 
            &new_state.callstack.current_context.log_queue_forward_tail
        );
    }

    // rollback log head(!)
    for (flag, length, state) in diffs_accumulator.log_queue_rollback_candidates.into_iter() {
        new_state.callstack.current_context.saved_context.reverted_queue_segment_len = UInt32::conditionally_select(
            cs, 
            flag, 
            &length, 
            &new_state.callstack.current_context.saved_context.reverted_queue_segment_len
        );

        new_state.callstack.current_context.saved_context.reverted_queue_head = Num::parallel_select(
            cs, 
            flag, 
            &state, 
            &new_state.callstack.current_context.saved_context.reverted_queue_head 
        );
    }

    // flags
    for (flag, flags) in diffs_accumulator.flags.iter() {
        new_state.flags = ArithmeticFlagsPort::conditionally_select(
            cs, 
            *flag, 
            flags,
            &new_state.flags
        );
    }

    // and now we either replace or not the callstack in full
    for (flag, callstack) in diffs_accumulator.callstacks.into_iter() {
        new_state.callstack = Callstack::conditionally_select(
            cs, 
            flag, 
            &callstack, 
            &new_state.callstack
        );
    }

    // add/sub relations

    let cap = diffs_accumulator.add_sub_relations.len();
    for _ in 0..MAX_ADD_SUB_RELATIONS_PER_CYCLE {
        let mut relations = Vec::with_capacity(cap);
        for (flag, values) in diffs_accumulator.add_sub_relations.iter_mut() {
            if let Some(el) = values.pop() {
                relations.push((*flag, el));
            }
        }

        if let Some((_, selected)) = relations.pop() {
            let mut selected = selected;
            for (flag, el) in relations.into_iter() {
                selected = AddSubRelation::conditionally_select(
                    cs,
                    flag,
                    &el,
                    &selected
                );
            }
    
            enforce_addition_relation(cs, selected);
        }
    }

    let cap = diffs_accumulator.mul_div_relations.len();
    for _ in 0..MAX_MUL_DIV_RELATIONS_PER_CYCLE {
        let mut relations = Vec::with_capacity(cap);
        for (flag, values) in diffs_accumulator.mul_div_relations.iter_mut() {
            if let Some(el) = values.pop() {
                relations.push((*flag, el));
            }
        }

        if let Some((_, selected)) = relations.pop() {
            let mut selected = selected;
            for (flag, el) in relations.into_iter() {
                selected = MulDivRelation::conditionally_select(
                    cs,
                    flag,
                    &el,
                    &selected
                );
            }
    
            enforce_mul_relation(cs, selected);
        }
    }

    // now we can enforce sponges. There are only 2 outcomes
    // - we have dst0 write (and may be src0 read), that we taken care above
    // - opcode itself modified memory queue, based on outcome of src0 read
    // in parallel opcodes either
    // - do not use sponges and only rely on src0/dst0
    // - can not have src0/dst0 in memory, but use sponges (UMA, near_call, far call, ret)

    let src0_read_state_pending_sponge = opcode_carry_parts.src0_read_sponge_data;
    let dst0_write_state_pending_sponge = PendingSponge {
        initial_state: dst0_write_initial_state_to_enforce,
        final_state: dst0_write_final_state_to_enforce,
        should_enforce: perform_dst0_memory_write_update,
    };

    let boolean_true = Boolean::allocated_constant(cs, true);

    let mut first_sponge_candidate = src0_read_state_pending_sponge;
    for (can_use_sponge_for_src0, can_use_sponge_for_dst0, opcode_applies, sponge_data) in diffs_accumulator.sponge_candidates_to_run.iter_mut() {
        assert!(*can_use_sponge_for_src0 == false);
        assert!(*can_use_sponge_for_dst0 == false);

        if let Some((initial_state, final_state)) = sponge_data.pop() {
            // we can conditionally select
            let formal_sponge = PendingSponge {
                initial_state: initial_state,
                final_state: final_state,
                should_enforce: boolean_true,
            };

            first_sponge_candidate = Selectable::conditionally_select(
                cs, 
                *opcode_applies,
                &formal_sponge,
                &first_sponge_candidate,
            );
        }
    }

    let mut second_sponge_candidate = dst0_write_state_pending_sponge;
    for (can_use_sponge_for_src0, can_use_sponge_for_dst0, opcode_applies, sponge_data) in diffs_accumulator.sponge_candidates_to_run.iter_mut() {
        assert!(*can_use_sponge_for_src0 == false);
        assert!(*can_use_sponge_for_dst0 == false);

        if let Some((initial_state, final_state)) = sponge_data.pop() {
            // we can conditionally select
            let formal_sponge = PendingSponge {
                initial_state: initial_state,
                final_state: final_state,
                should_enforce: boolean_true,
            };

            second_sponge_candidate = Selectable::conditionally_select(
                cs, 
                *opcode_applies,
                &formal_sponge,
                &second_sponge_candidate,
            );
        }
    }

    use super::state_diffs::MAX_SPONGES_PER_CYCLE;
    let mut selected_sponges_to_enforce = ArrayVec::<_, MAX_SPONGES_PER_CYCLE>::new();
    selected_sponges_to_enforce.push(first_sponge_candidate);
    selected_sponges_to_enforce.push(second_sponge_candidate);

    for _ in 2..MAX_SPONGES_PER_CYCLE {
        let mut selected = None;
        for (_, _, opcode_applies, sponge_data) in diffs_accumulator.sponge_candidates_to_run.iter_mut() {    
            if let Some((initial_state, final_state)) = sponge_data.pop() {
                if let Some(selected) = selected.as_mut() {
                    // we can conditionally select
                    let formal_sponge = PendingSponge {
                        initial_state: initial_state,
                        final_state: final_state,
                        should_enforce: boolean_true,
                    };

                    *selected = Selectable::conditionally_select(
                        cs, 
                        *opcode_applies,
                        &formal_sponge,
                        &*selected,
                    );
                } else {
                    let formal_sponge = PendingSponge {
                        initial_state: initial_state,
                        final_state: final_state,
                        should_enforce: *opcode_applies,
                    };
                    selected = Some(formal_sponge);
                }
            }
        }

        let selected = selected.expect("non-trivial sponge");
        selected_sponges_to_enforce.push(selected);
    }

    // ensure that we selected everything
    for (_, _, _, sponge_data) in diffs_accumulator.sponge_candidates_to_run.iter_mut() {
        assert!(sponge_data.is_empty());
    }
    assert_eq!(selected_sponges_to_enforce.len(), MAX_SPONGES_PER_CYCLE);

    // actually enforce_sponges

    enforce_sponges(
        cs,
        &selected_sponges_to_enforce,
        round_function
    );

    new_state
}

use crate::main_vm::pre_state::MemoryLocation;

fn may_be_write_memory<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    W: WitnessOracle<F>,
>(
    cs: &mut CS,
    should_write_dst0: &Boolean<F>,
    dst0_value: &VMRegister<F>,
    timestamp: &UInt32<F>,
    location: &MemoryLocation<F>,
    current_memory_sponge_tail: &[Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
    current_memory_sponge_length: &UInt32<F>,
    witness_oracle: &SynchronizedWitnessOracle<F, W>,
    _round_function: &R,
) -> (
    (
        [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
        [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
    ),
    [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
    UInt32<F>,
)
where
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let MemoryLocation { page, index } = location;

    let boolean_true = Boolean::allocated_constant(cs, true);

    let query = MemoryQuery {
        timestamp: *timestamp,
        memory_page: *page,
        index: *index,
        is_ptr: dst0_value.is_pointer,
        value: dst0_value.value,
        rw_flag: boolean_true,
    };

    use boojum::gadgets::traits::encodable::CircuitEncodable;
    let packed_query = query.encode(cs);

    // absorb by replacement

    use boojum::gadgets::queue::full_state_queue::simulate_new_tail_for_full_state_queue;

    use crate::base_structures::memory_query::MEMORY_QUERY_PACKED_WIDTH;

    let simulated_values = simulate_new_tail_for_full_state_queue::<
        F,
        8,
        FULL_SPONGE_QUEUE_STATE_WIDTH,
        4,
        MEMORY_QUERY_PACKED_WIDTH,
        R,
        _,
    >(
        cs,
        packed_query,
        current_memory_sponge_tail.map(|el| el.get_variable()),
        boolean_true,
    );

    let simulated_final_state = simulated_values.map(|el| Num::from_variable(el));

    // for all reasonable execution traces it's fine
    let new_len_candidate = unsafe { current_memory_sponge_length.increment_unchecked(cs) };

    let new_length = UInt32::conditionally_select(
        cs,
        *should_write_dst0,
        &new_len_candidate,
        &current_memory_sponge_length,
    );

    let final_state = Num::parallel_select(
        cs,
        *should_write_dst0,
        &simulated_final_state,
        current_memory_sponge_tail,
    );

    let oracle = witness_oracle.clone();
    // we should assemble all the dependencies here, and we will use AllocateExt here
    let mut dependencies =
        Vec::with_capacity(<MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1);
    dependencies.push(should_write_dst0.get_variable().into());
    dependencies.extend(Place::from_variables(query.flatten_as_variables()));

    cs.set_values_with_dependencies_vararg(
        &dependencies,
        &[],
        move |inputs: &[F], _buffer: &mut DstBuffer<'_, F>| {
            let execute = inputs[0].as_u64();
            let execute = u64_as_bool(execute);

            use crate::main_vm::cycle::memory_query::MemoryQueryWitness;

            let mut query = [F::ZERO; <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            query.copy_from_slice(&inputs[1..]);
            let query: MemoryQueryWitness<F> = CSAllocatableExt::witness_from_set_of_values(query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            guard.push_memory_witness(&query, execute);
            drop(guard);
        },
    );

    (
        (*current_memory_sponge_tail, simulated_final_state),
        final_state,
        new_length,
    )
}

fn enforce_sponges<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    candidates: &[PendingSponge<F>],
    _round_function: &R
) {
    for el in candidates.iter() {
        let PendingSponge { initial_state, final_state, should_enforce } = el;
        let true_final = R::compute_round_function_over_nums(cs, *initial_state);
        for (a, b) in true_final.iter().zip(final_state.iter()) {
            Num::conditionally_enforce_equal(cs, *should_enforce, a, b);
        }
    }
}

pub const fn reference_vm_geometry() -> CSGeometry {
    CSGeometry {
        num_columns_under_copy_permutation: 140,
        num_witness_columns: 0,
        num_constant_columns: 8,
        max_allowed_constraint_degree: 8,
    }
}

// use boojum::cs::traits::cs::GatesConfigulation;
// pub fn gates_setup(geometry: &CSGeometry) -> impl GatesConfigulation<GoldilocksField> {
//     type F = GoldilocksField;

//     use boojum::cs::empty_gates_set;
//     use boojum::cs::gates::*;
//     use crate::implementations::poseidon_goldilocks::PoseidonGoldilocks;

//     type PoseidonGate = PoseidonFlattenedGate<F, 8, 12, 4, PoseidonGoldilocks>;

//     let gates = empty_gates_set().allow_gate::<ConstantsAllocatorGate<F>>(());
//     let gates = PoseidonGate::compute_strategy_and_add_into_gates_set(gates, geometry);
//     let gates = gates.allow_gate::<DotProductGate<4>>(());
//     let gates = gates.allow_gate::<BooleanConstraintGate>(());
//     let gates = gates.allow_gate::<QuadraticCombinationGate<4>>(());
//     let gates = gates.allow_gate::<ZeroCheckGate>(false);
//     let gates = gates.allow_gate::<FmaGateInBaseFieldWithoutConstant<F>>(());
//     let gates = gates.allow_gate::<UIntXAddGate<32>>(());
//     let gates = gates.allow_gate::<UIntXAddGate<16>>(());
//     let gates = gates.allow_gate::<UIntXAddGate<8>>(());
//     let gates = gates.allow_gate::<ReductionByPowersGate<F, 4>>(());
//     let gates = gates.allow_gate::<SelectionGate>(());
//     let gates = gates.allow_gate::<ParallelSelectionGate<4>>(());
//     let gates = gates.allow_gate::<ReductionGate<F, 4>>(());
//     let gates = gates.allow_gate::<U8x4FMAGate>(());

//     gates
// }

// use boojum::cs::implementations::cs::CSDevelopmentAssembly;

// pub fn testing_cs<G: GatesConfigulation<GoldilocksField>>(
//     geometry: CSGeometry,
//     max_trace_length: usize, 
//     gates: G,
// ) -> CSDevelopmentAssembly<GoldilocksField, G> {
//     use boojum::cs::create_test_cs_with_lookup_ext;
//     use crate::tables::bitshift::create_shift_to_num_converter_table;
//     use crate::tables::conditional::create_conditionals_resolution_table;
//     use crate::tables::integer_to_boolean_mask::REG_IDX_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::UMA_SHIFT_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::{
//         create_integer_to_bitmask_table, create_subpc_bitmask_table,
//     };
//     use crate::tables::uma_ptr_read_cleanup::create_uma_ptr_read_bitmask_table;
//     use crate::tables::opcodes_decoding::create_opcodes_decoding_and_pricing_table;
//     type F = GoldilocksField;
//     use crate::base_structures::vm_state::REGISTERS_COUNT;

//     let mut cs_owned = create_test_cs_with_lookup_ext(geometry, max_trace_length * 100, max_trace_length, gates);

//     let subpc_to_mask_table = create_subpc_bitmask_table::<F>();
//     cs_owned.add_lookup_table(subpc_to_mask_table);

//     let opcode_decoding_table = create_opcodes_decoding_and_pricing_table::<F>();
//     cs_owned.add_lookup_table(opcode_decoding_table);

//     let conditions_resolution_table = create_conditionals_resolution_table::<F>();
//     cs_owned.add_lookup_table(conditions_resolution_table);

//     let integer_to_bitmask_table = create_integer_to_bitmask_table::<F>(
//         REGISTERS_COUNT.next_power_of_two().trailing_zeros() as usize,
//         REG_IDX_TO_BITMASK_TABLE_NAME,
//     );
//     cs_owned.add_lookup_table(integer_to_bitmask_table);

//     let shifts_table = create_shift_to_num_converter_table::<F>();
//     cs_owned.add_lookup_table(shifts_table);

//     let uma_unaligned_access_table = create_integer_to_bitmask_table::<F>(
//         5,
//         UMA_SHIFT_TO_BITMASK_TABLE_NAME
//     );
//     cs_owned.add_lookup_table(uma_unaligned_access_table);

//     let uma_ptr_read_cleanup_table = create_uma_ptr_read_bitmask_table::<F>();
//     cs_owned.add_lookup_table(uma_ptr_read_cleanup_table);

//     cs_owned
// }

// use boojum::cs::implementations::cs::CSBasicProvingAssembly;

// pub fn basic_proving_cs<G: GatesConfigulation<GoldilocksField>>(
//     geometry: CSGeometry,
//     max_trace_length: usize, 
//     gates: G,
// ) -> CSBasicProvingAssembly<GoldilocksField, G> {
//     use crate::tables::bitshift::create_shift_to_num_converter_table;
//     use crate::tables::conditional::create_conditionals_resolution_table;
//     use crate::tables::integer_to_boolean_mask::REG_IDX_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::UMA_SHIFT_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::{
//         create_integer_to_bitmask_table, create_subpc_bitmask_table,
//     };
//     use crate::tables::uma_ptr_read_cleanup::create_uma_ptr_read_bitmask_table;
//     use crate::tables::opcodes_decoding::create_opcodes_decoding_and_pricing_table;
//     type F = GoldilocksField;
//     use crate::base_structures::vm_state::REGISTERS_COUNT;

//     use boojum::cs::LookupParameters;

//     let mut cs_owned = CSBasicProvingAssembly::<GoldilocksField, G>::new_for_geometry(
//         geometry,
//         max_trace_length * 100,
//         max_trace_length,
//         LookupParameters::TableIdAsConstant { width: 3 },
//         gates,
//     );

//     use boojum::cs::gates::ConstantsAllocatorGate;
//     assert!(cs_owned.gate_is_allowed::<ConstantsAllocatorGate<GoldilocksField>>());

//     use boojum::cs::tables::binop_table::create_binop_table;
//     let binop_table = create_binop_table();
//     cs_owned.add_lookup_table(binop_table);

//     let subpc_to_mask_table = create_subpc_bitmask_table::<F>();
//     cs_owned.add_lookup_table(subpc_to_mask_table);

//     let opcode_decoding_table = create_opcodes_decoding_and_pricing_table::<F>();
//     cs_owned.add_lookup_table(opcode_decoding_table);

//     let conditions_resolution_table = create_conditionals_resolution_table::<F>();
//     cs_owned.add_lookup_table(conditions_resolution_table);

//     let integer_to_bitmask_table = create_integer_to_bitmask_table::<F>(
//         REGISTERS_COUNT.next_power_of_two().trailing_zeros() as usize,
//         REG_IDX_TO_BITMASK_TABLE_NAME,
//     );
//     cs_owned.add_lookup_table(integer_to_bitmask_table);

//     let shifts_table = create_shift_to_num_converter_table::<F>();
//     cs_owned.add_lookup_table(shifts_table);

//     let uma_unaligned_access_table = create_integer_to_bitmask_table::<F>(
//         5,
//         UMA_SHIFT_TO_BITMASK_TABLE_NAME
//     );
//     cs_owned.add_lookup_table(uma_unaligned_access_table);

//     let uma_ptr_read_cleanup_table = create_uma_ptr_read_bitmask_table::<F>();
//     cs_owned.add_lookup_table(uma_ptr_read_cleanup_table);

//     cs_owned
// }

// #[cfg(test)]
// mod test {
//     use std::sync::RwLock;

//     use super::*;
//     use crate::algebraic_props::round_function;
//     use boojum::cs::empty_gates_set;
//     use boojum::cs::gates::*;
//     use boojum::cs::{create_setup_cs_with_lookup_ext, CSGeometry};
//     use boojum::field::goldilocks::GoldilocksField;
//     use crate::implementations::poseidon_goldilocks::PoseidonGoldilocks;
//     use crate::main_vm::witness_oracle::DummyOracle;
//     use crate::tables::bitshift::create_shift_to_num_converter_table;
//     use crate::tables::conditional::create_conditionals_resolution_table;
//     use crate::tables::integer_to_boolean_mask::REG_IDX_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::UMA_SHIFT_TO_BITMASK_TABLE_NAME;
//     use crate::tables::integer_to_boolean_mask::{
//         create_integer_to_bitmask_table, create_subpc_bitmask_table,
//     };
//     use crate::tables::uma_ptr_read_cleanup::create_uma_ptr_read_bitmask_table;
//     use crate::tables::opcodes_decoding::create_opcodes_decoding_and_pricing_table;
//     type F = GoldilocksField;
//     use crate::base_structures::vm_state::REGISTERS_COUNT;

//     #[test]
//     fn try_synthesize_setup() {
//         let geometry = CSGeometry {
//             num_columns_under_copy_permutation: 140,
//             num_witness_columns: 0,
//             num_constant_columns: 8,
//             max_allowed_constraint_degree: 8,
//         };

//         type PoseidonGate = PoseidonFlattenedGate<F, 8, 12, 4, PoseidonGoldilocks>;

//         let gates = empty_gates_set().allow_gate::<ConstantsAllocatorGate<F>>(());
//         let gates = PoseidonGate::compute_strategy_and_add_into_gates_set(gates, &geometry);
//         let gates = gates.allow_gate::<DotProductGate<4>>(());
//         let gates = gates.allow_gate::<BooleanConstraintGate>(());
//         let gates = gates.allow_gate::<QuadraticCombinationGate<4>>(());
//         let gates = gates.allow_gate::<ZeroCheckGate>(false);
//         let gates = gates.allow_gate::<FmaGateInBaseFieldWithoutConstant<F>>(());
//         let gates = gates.allow_gate::<UIntXAddGate<32>>(());
//         let gates = gates.allow_gate::<UIntXAddGate<16>>(());
//         let gates = gates.allow_gate::<UIntXAddGate<8>>(());
//         let gates = gates.allow_gate::<ReductionByPowersGate<F, 4>>(());
//         let gates = gates.allow_gate::<SelectionGate>(());
//         let gates = gates.allow_gate::<ParallelSelectionGate<4>>(());
//         let gates = gates.allow_gate::<ReductionGate<F, 4>>(());
//         let gates = gates.allow_gate::<U8x4FMAGate>(());

//         let mut cs_owned = create_setup_cs_with_lookup_ext(geometry, 1 << 20, 1 << 17, gates);

//         let subpc_to_mask_table = create_subpc_bitmask_table::<F>();
//         cs_owned.add_lookup_table(subpc_to_mask_table);

//         let opcode_decoding_table = create_opcodes_decoding_and_pricing_table::<F>();
//         cs_owned.add_lookup_table(opcode_decoding_table);

//         let conditions_resolution_table = create_conditionals_resolution_table::<F>();
//         cs_owned.add_lookup_table(conditions_resolution_table);

//         let integer_to_bitmask_table = create_integer_to_bitmask_table::<F>(
//             REGISTERS_COUNT.next_power_of_two().trailing_zeros() as usize,
//             REG_IDX_TO_BITMASK_TABLE_NAME,
//         );
//         cs_owned.add_lookup_table(integer_to_bitmask_table);

//         let shifts_table = create_shift_to_num_converter_table::<F>();
//         cs_owned.add_lookup_table(shifts_table);

//         let uma_unaligned_access_table = create_integer_to_bitmask_table::<F>(
//             5,
//             UMA_SHIFT_TO_BITMASK_TABLE_NAME
//         );
//         cs_owned.add_lookup_table(uma_unaligned_access_table);

//         let uma_ptr_read_cleanup_table = create_uma_ptr_read_bitmask_table::<F>();
//         cs_owned.add_lookup_table(uma_ptr_read_cleanup_table);

//         let cs = &mut cs_owned;

//         let mut state = VmLocalState::uninitialized(cs);
//         let witness_oracle = DummyOracle::default();
//         let witness_oracle = SynchronizedWitnessOracle {
//             inner: std::sync::Arc::new(RwLock::new(witness_oracle)),
//             _marker: std::marker::PhantomData,
//         };

//         let global_context = GlobalContext {
//             default_aa_code_hash: UInt256::zero(cs),
//             zkporter_is_available: Boolean::allocated_constant(cs, false),
//         };

//         let round_function = PoseidonGoldilocks;

//         let now = std::time::Instant::now();

//         for _ in 0..128 {
//             state = vm_cycle(cs, state, &witness_oracle, &global_context, &round_function);
//         }

//         dbg!(now.elapsed());

//         dbg!(cs.next_available_row);
//         // dbg!(&cs.gates_ordered_eval_functions_set);
//         cs.print_gate_stats();

//         let _ = cs.compute_selectors_and_constants_placement();
//     }
// }
