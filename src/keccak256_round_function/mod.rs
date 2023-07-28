use super::*;

use boojum::field::SmallField;

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::gadgets::u16::UInt16;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use cs_derive::*;

use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::keccak256_round_function::buffer::ByteBuffer;
use boojum::gadgets::num::Num;
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

use crate::base_structures::log_query::*;
use crate::base_structures::memory_query::*;
use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::demux_log_queue::StorageLogQueue;
use crate::fsm_input_output::*;
use crate::storage_application::ConditionalWitnessAllocator;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::Variable;
use boojum::gadgets::keccak256::{self};
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::allocatable::{CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::encodable::CircuitVarLengthEncodable;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::u160::UInt160;
use boojum::gadgets::u8::UInt8;
use std::sync::{Arc, RwLock};

pub mod buffer;

pub mod input;
use self::input::*;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
// #[DerivePrettyComparison("true")]
pub struct Keccak256PrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_memory_byte_offset: UInt32<F>,
    pub input_memory_byte_length: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_word_offset: UInt32<F>,
    pub needs_full_padding_round: Boolean<F>,
}

impl<F: SmallField> CSPlaceholder<F> for Keccak256PrecompileCallParams<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_u32 = UInt32::zero(cs);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Self {
            input_page: zero_u32,
            input_memory_byte_offset: zero_u32,
            input_memory_byte_length: zero_u32,
            output_page: zero_u32,
            output_word_offset: zero_u32,
            needs_full_padding_round: boolean_false,
        }
    }
}

impl<F: SmallField> Keccak256PrecompileCallParams<F> {
    // from PrecompileCallInnerABI
    pub fn from_encoding<CS: ConstraintSystem<F>>(cs: &mut CS, encoding: UInt256<F>) -> Self {
        let input_memory_byte_offset = encoding.inner[0];
        let input_memory_byte_length = encoding.inner[1];

        let output_word_offset = encoding.inner[2];

        let input_page = encoding.inner[4];
        let output_page = encoding.inner[5];

        let (_, rem) = input_memory_byte_length.div_by_constant(cs, KECCAK_RATE_BYTES as u32);

        let needs_full_padding_round = rem.is_zero(cs);

        let new = Self {
            input_page,
            input_memory_byte_offset,
            input_memory_byte_length,
            output_page,
            output_word_offset,
            needs_full_padding_round,
        };

        new
    }
}

fn trivial_mapping_function<F: SmallField, CS: ConstraintSystem<F>, const N: usize, const BUFFER_SIZE: usize>(
    cs: &mut CS,
    bytes_to_consume: &UInt8<F>,
    current_fill_factor: &UInt8<F>,
    _unused: [(); N]
) -> [Boolean<F>; BUFFER_SIZE] {
    use boojum::config::*;
    if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
        let already_filled = current_fill_factor.witness_hook(cs)();
        let new_to_fill = bytes_to_consume.witness_hook(cs)();
        if let Some(already_filled) = already_filled {
            if let Some(new_to_fill) = new_to_fill {
                assert!(new_to_fill as usize + already_filled as usize <= BUFFER_SIZE);
            }
        }
    }

    let boolean_false = Boolean::allocated_constant(cs, false);

    let mut result = [boolean_false; BUFFER_SIZE];
    let zero_to_fill = bytes_to_consume.is_zero(cs);
    let marker = zero_to_fill.negated(cs);

    // we just need to put a marker after the current fill value
    let mut tmp = current_fill_factor.into_num();
    let one_num = Num::allocated_constant(cs, F::ONE);
    for dst in result.iter_mut() {
        let should_fill = tmp.is_zero(cs);
        *dst = should_fill.and(cs, marker);
        tmp = tmp.sub(cs, &one_num);
    }

    result
}

pub const KECCAK256_RATE_IN_U64_WORDS: usize = 17;
pub const MEMORY_EQURIES_PER_CYCLE: usize = 5; // we need to read as much as possible to use a round function every cycle
pub const NUM_U64_WORDS_PER_CYCLE: usize = 4 * MEMORY_EQURIES_PER_CYCLE;
pub const NEW_BYTES_PER_CYCLE: usize = 8 * NUM_U64_WORDS_PER_CYCLE;
// we absorb 136 elements per cycle, and add 160 elements per cycle, so we need to skip memory reads
// sometimes and do absorbs instead
pub const BUFFER_SIZE_IN_U64_WORDS: usize =
    MEMORY_EQURIES_PER_CYCLE * 4 + KECCAK256_RATE_IN_U64_WORDS - 1;
pub const BYTES_BUFFER_SIZE: usize = BUFFER_SIZE_IN_U64_WORDS * 8;

use boojum::gadgets::keccak256::KECCAK_RATE_BYTES;

pub fn keccak256_precompile_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueue<F, R>,
    precompile_calls_queue: &mut StorageLogQueue<F, R>,
    memory_read_witness: ConditionalWitnessAllocator<F, UInt256<F>>,
    mut state: Keccak256RoundFunctionFSM<F>,
    _round_function: &R,
    limit: usize,
) -> Keccak256RoundFunctionFSM<F>
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    assert!(limit <= u32::MAX as usize);

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::KECCAK256_ROUND_FUNCTION_PRECOMPILE_FORMAL_ADDRESS,
    );
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);
    let zero_u8 = UInt8::zero(cs);
    let one_num = Num::allocated_constant(cs, F::ONE);

    let empty_buffer = ByteBuffer::<F, KECCAK_PRECOMPILE_BUFFER_SIZE>::placeholder(cs);

    let mut full_padding_buffer = [zero_u8; KECCAK_RATE_BYTES];
    full_padding_buffer[0] = UInt8::allocated_constant(cs, 0x01);
    full_padding_buffer[KECCAK_RATE_BYTES-1] = UInt8::allocated_constant(cs, 0x80);

    // we can have a degenerate case when queue is empty, but it's a first circuit in the queue,
    // so we taken default FSM state that has state.read_precompile_call = true;
    let input_queue_is_empty = precompile_calls_queue.is_empty(cs);
    // we can only skip the full circuit if we are not in any form of progress
    let can_finish_immediatelly =
        Boolean::multi_and(cs, &[state.read_precompile_call, input_queue_is_empty]);

    if crate::config::CIRCUIT_VERSOBE {
        dbg!(can_finish_immediatelly.witness_hook(cs)());
        dbg!(state.witness_hook(cs)());
    }

    state.read_precompile_call = state
        .read_precompile_call
        .mask_negated(cs, can_finish_immediatelly);
    state.read_unaligned_words_for_round = state
        .read_unaligned_words_for_round
        .mask_negated(cs, can_finish_immediatelly);
    state.completed = Boolean::multi_or(cs, &[state.completed, can_finish_immediatelly]);

    // main work cycle
    for _cycle in 0..limit {
        // if we are in a proper state then get the ABI from the queue
        let (precompile_call, _) = precompile_calls_queue.pop_front(cs, state.read_precompile_call);

        Num::conditionally_enforce_equal(
            cs,
            state.read_precompile_call,
            &Num::from_variable(precompile_call.aux_byte.get_variable()),
            &Num::from_variable(aux_byte_for_precompile.get_variable()),
        );
        for (a, b) in precompile_call
            .address
            .inner
            .iter()
            .zip(precompile_address.inner.iter())
        {
            Num::conditionally_enforce_equal(
                cs,
                state.read_precompile_call,
                &Num::from_variable(a.get_variable()),
                &Num::from_variable(b.get_variable()),
            );
        }

        // now compute some parameters that describe the call itself

        let params_encoding = precompile_call.key;
        let call_params = Keccak256PrecompileCallParams::from_encoding(cs, params_encoding);

        state.precompile_call_params = Keccak256PrecompileCallParams::conditionally_select(
            cs,
            state.read_precompile_call,
            &call_params,
            &state.precompile_call_params,
        );
        // also set timestamps
        state.timestamp_to_use_for_read = UInt32::conditionally_select(
            cs,
            state.read_precompile_call,
            &precompile_call.timestamp,
            &state.timestamp_to_use_for_read,
        );

        // timestamps have large space, so this can be expected
        let timestamp_to_use_for_write =
            unsafe { state.timestamp_to_use_for_read.increment_unchecked(cs) };
        state.timestamp_to_use_for_write = UInt32::conditionally_select(
            cs,
            state.read_precompile_call,
            &timestamp_to_use_for_write,
            &state.timestamp_to_use_for_write,
        );

        // and do some work! keccak256 is expensive
        let reset_buffer = Boolean::multi_or(cs, &[state.read_precompile_call, state.completed]);
        state.read_unaligned_words_for_round = Boolean::multi_or(
            cs,
            &[
                state.read_precompile_call,
                state.read_unaligned_words_for_round,
            ],
        );
        state.read_precompile_call = boolean_false;

        // ---------------------------------
        // Now perform few memory queries to read content

        state.buffer = ByteBuffer::<F, KECCAK_PRECOMPILE_BUFFER_SIZE>::conditionally_select(
            cs,
            reset_buffer,
            &empty_buffer,
            &state.buffer,
        );

        // conditionally reset state. Keccak256 empty state is just all 0s

        for dst in state.keccak_internal_state.iter_mut() {
            for dst in dst.iter_mut() {
                for dst in dst.iter_mut() {
                    *dst = dst.mask_negated(cs, reset_buffer);
                }
            }
        }

        let no_more_bytes = state.precompile_call_params.input_memory_byte_length.is_zero(cs);
        let have_leftover_bytes = no_more_bytes.negated(cs);
        let should_read_in_general = Boolean::multi_and(
            cs,
            &[
                have_leftover_bytes,
                state.read_unaligned_words_for_round,
            ],
        );

        let mapping_function = |cs: &mut CS, bytes_to_consume: UInt8<F>, current_fill_factor: UInt8<F>, _unused: [(); 32]| {
            trivial_mapping_function::<F, CS, 32, KECCAK_PRECOMPILE_BUFFER_SIZE>(cs, &bytes_to_consume, &current_fill_factor, _unused)
        };

        let mut bias_variable = should_read_in_general.get_variable();
        for _ in 0..MEMORY_EQURIES_PER_CYCLE {
            // we have a little more complex logic here, but it's homogenious

            let (aligned_memory_index, unalignment) = state.precompile_call_params.input_memory_byte_offset.div_by_constant(cs, 32);
            let at_most_meaningful_bytes_in_query = UInt32::allocated_constant(cs, 32).into_num().sub(cs, &unalignment.into_num());
            let at_most_meaningful_bytes_in_query = unsafe { UInt32::from_variable_unchecked(at_most_meaningful_bytes_in_query.get_variable()) };
            let (_, uf) = at_most_meaningful_bytes_in_query.overflowing_sub(cs, state.precompile_call_params.input_memory_byte_length);
            let meaningful_bytes_in_query = UInt32::conditionally_select(
                cs,
                uf,
                &state.precompile_call_params.input_memory_byte_length,
                &at_most_meaningful_bytes_in_query,
            );

            let nothing_to_read = meaningful_bytes_in_query.is_zero(cs);
            let have_something_to_read = nothing_to_read.negated(cs);
            let bytes_to_fill = unsafe { UInt8::from_variable_unchecked(meaningful_bytes_in_query.get_variable()) };
            let enough_buffer_space = state.buffer.can_fill_bytes(cs, bytes_to_fill);
            let should_read = Boolean::multi_and(cs, &[have_something_to_read, enough_buffer_space, state.read_unaligned_words_for_round]);

            let read_query_value =
                memory_read_witness.conditionally_allocate_biased(cs, should_read, bias_variable);
            bias_variable = read_query_value.inner[0].get_variable();

            let read_query = MemoryQuery {
                timestamp: state.timestamp_to_use_for_read,
                memory_page: state.precompile_call_params.input_page,
                index: aligned_memory_index,
                rw_flag: boolean_false,
                is_ptr: boolean_false,
                value: read_query_value,
            };

            // perform read
            memory_queue.push(cs, read_query, should_read);

            // update state variables
            state.precompile_call_params.input_memory_byte_length = state.precompile_call_params.input_memory_byte_length.sub_no_overflow(cs, meaningful_bytes_in_query);
            state.precompile_call_params.input_memory_byte_offset = state.precompile_call_params.input_memory_byte_offset.add_no_overflow(cs, meaningful_bytes_in_query);

            // fill the buffer
            let be_bytes = read_query_value.to_be_bytes(cs);
            let offset = unsafe { UInt8::from_variable_unchecked(unalignment.get_variable()) };

            state.buffer.fill_with_bytes(cs, &be_bytes, offset, bytes_to_fill, mapping_function);
        }

        // now actually run keccak permutation

        // we either mask for padding, or mask in full if it's full padding round
        let zero_bytes_left = state.precompile_call_params.input_memory_byte_length.is_zero(cs);
        let apply_padding = Boolean::multi_and(cs, &[zero_bytes_left, state.read_unaligned_words_for_round]);

        let currently_filled = state.buffer.filled;
        let almost_filled = UInt8::allocated_constant(cs, (KECCAK_RATE_BYTES - 1) as u8);
        let do_one_byte_of_padding = UInt8::equals(cs, &currently_filled, &almost_filled);
        let mut input = state.buffer.consume::<CS, KECCAK_RATE_BYTES>(cs, boolean_true);

        let mut tmp = currently_filled.into_num();
        let pad_constant = UInt8::allocated_constant(cs, 0x01);
        for dst in input[..(KECCAK_RATE_BYTES-1)].iter_mut() {
            let pad_this_byte = tmp.is_zero(cs);
            let apply_padding = Boolean::multi_and(cs, &[apply_padding, pad_this_byte]);
            *dst = UInt8::conditionally_select(cs, apply_padding, &pad_constant, &*dst);
            tmp = tmp.sub(cs, &one_num);
        }

        let normal_last_byte_padding_value = UInt8::allocated_constant(cs, 0x80);
        let special_last_byte_paddings_value = UInt8::allocated_constant(cs, 0x81);
        let last_byte_padding_value = UInt8::conditionally_select(cs, do_one_byte_of_padding, &special_last_byte_paddings_value, &normal_last_byte_padding_value);
        input[KECCAK_RATE_BYTES-1] = UInt8::conditionally_select(cs, apply_padding, &last_byte_padding_value, &input[KECCAK_RATE_BYTES-1]);

        let input = UInt8::<F>::parallel_select(cs, state.padding_round, &full_padding_buffer, &input);

        // manually absorb and run round function
        let squeezed =
            keccak256_absorb_and_run_permutation(cs, &mut state.keccak_internal_state, &input);

        let absorbed_and_padded = apply_padding;
        let finished_processing = Boolean::multi_or(cs, &[absorbed_and_padded, state.padding_round]);
        let write_result = finished_processing;

        let result = UInt256::from_be_bytes(cs, squeezed);

        let write_query = MemoryQuery {
            timestamp: state.timestamp_to_use_for_write,
            memory_page: state.precompile_call_params.output_page,
            index: state.precompile_call_params.output_word_offset,
            rw_flag: boolean_true,
            is_ptr: boolean_false,
            value: result,
        };

        // perform write
        memory_queue.push(cs, write_query, write_result);

        // ---------------------------------

        // update FSM state
        let input_is_empty = precompile_calls_queue.is_empty(cs);
        let input_is_not_empty = input_is_empty.negated(cs);
        let nothing_left = Boolean::multi_and(cs, &[write_result, input_is_empty]);
        let process_next = Boolean::multi_and(cs, &[write_result, input_is_not_empty]);

        state.read_precompile_call = process_next;
        state.completed = Boolean::multi_or(cs, &[nothing_left, state.completed]);

        // now we need to decide on full padding round
        let needs_full_padding = Boolean::multi_and(cs, &[state.read_precompile_call, zero_bytes_left, state.precompile_call_params.needs_full_padding_round]);
        state.padding_round = needs_full_padding;

        // otherwise we just continue
        let t = Boolean::multi_or(cs, &[state.read_precompile_call, state.padding_round, state.completed]);
        state.read_unaligned_words_for_round = t.negated(cs);
    }

    precompile_calls_queue.enforce_consistency(cs);

    state
}

#[track_caller]
pub fn keccak256_round_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: Keccak256RoundFunctionCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    let Keccak256RoundFunctionCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;

    let mut structured_input = Keccak256RoundFunctionCircuitInputOutput::alloc_ignoring_outputs(
        cs,
        closed_form_input.clone(),
    );

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

    let read_queries_allocator = ConditionalWitnessAllocator::<F, UInt256<F>> {
        witness_source: Arc::new(RwLock::new(memory_reads_witness)),
    };

    let mut starting_fsm_state = Keccak256RoundFunctionFSM::placeholder(cs);
    starting_fsm_state.read_precompile_call = Boolean::allocated_constant(cs, true);

    let initial_state = Keccak256RoundFunctionFSM::conditionally_select(
        cs,
        start_flag,
        &starting_fsm_state,
        &structured_input.hidden_fsm_input.internal_fsm,
    );

    let final_state = keccak256_precompile_inner::<F, CS, R>(
        cs,
        &mut memory_queue,
        &mut requests_queue,
        read_queries_allocator,
        initial_state,
        round_function,
        limit,
    );

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();

    // form the final state
    let done = final_state.completed;
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::placeholder(cs);

    structured_input.observable_output.final_memory_state = QueueState::conditionally_select(
        cs,
        structured_input.completion_flag,
        &final_memory_state,
        &structured_input.observable_output.final_memory_state,
    );

    structured_input.hidden_fsm_output.internal_fsm = final_state;
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

pub(crate) fn keccak256_absorb_and_run_permutation<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [[[UInt8<F>; keccak256::BYTES_PER_WORD]; keccak256::LANE_WIDTH];
             keccak256::LANE_WIDTH],
    block: &[UInt8<F>; keccak256::KECCAK_RATE_BYTES],
) -> [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE] {
    let mut state_as_variables = state.map(|el| el.map(|el| el.map(|el| el.get_variable())));
    for i in 0..keccak256::LANE_WIDTH {
        for j in 0..keccak256::LANE_WIDTH {
            if i + keccak256::LANE_WIDTH * j
                < (keccak256::KECCAK_RATE_BYTES / keccak256::BYTES_PER_WORD)
            {
                let tmp = block
                    .array_chunks::<{ keccak256::BYTES_PER_WORD }>()
                    .skip(i + keccak256::LANE_WIDTH * j)
                    .next()
                    .unwrap();
                use boojum::gadgets::blake2s::mixing_function::xor_many;
                let tmp = tmp.map(|el| el.get_variable());
                state_as_variables[i][j] = xor_many(cs, &state_as_variables[i][j], &tmp);
            }
        }
    }
    use boojum::gadgets::keccak256::round_function::keccak_256_round_function;
    keccak_256_round_function(cs, &mut state_as_variables);

    let new_state = unsafe {
        state_as_variables.map(|el| el.map(|el| el.map(|el| UInt8::from_variable_unchecked(el))))
    };

    *state = new_state;

    // copy back
    let mut result =
        [std::mem::MaybeUninit::<UInt8<F>>::uninit(); keccak256::KECCAK256_DIGEST_SIZE];
    for (i, dst) in result.array_chunks_mut::<8>().enumerate() {
        for (dst, src) in dst.iter_mut().zip(state[i][0].iter()) {
            dst.write(*src);
        }
    }

    unsafe { result.map(|el| el.assume_init()) }
}


#[cfg(test)]
mod test {
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::cs::*;
    use boojum::cs::gates::*;
    use boojum::cs::cs_builder::*;
    use boojum::cs::traits::gate::*;
    use boojum::algebraic_props::poseidon2_parameters::*;
    use boojum::cs::implementations::reference_cs::CSReferenceImplementation;
    use boojum::config::DevCSConfig;

    use super::*;

    type F = GoldilocksField;
    type P = GoldilocksField;

    fn create_test_cs() -> CSReferenceImplementation<GoldilocksField, GoldilocksField, DevCSConfig, impl GateConfigurationHolder<GoldilocksField>, impl StaticToolboxHolder> {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 100,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
        };

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 4,
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
            let builder = MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksExternalMatrix>::configure_builder(builder,GatePlacementStrategy::UseGeneralPurposeColumns);
            let builder = MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksInnerMatrix>::configure_builder(builder,GatePlacementStrategy::UseGeneralPurposeColumns);
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, 1 << 26, 1 << 20);
        use boojum::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // add tables for keccak

        owned_cs
    }
}