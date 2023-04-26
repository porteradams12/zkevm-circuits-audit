mod input;
use input::*;

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};
use ethereum_types::U256;
use boojum::cs::Variable;

use boojum::cs::{traits::cs::ConstraintSystem, gates::*};
use boojum::field::SmallField;
use boojum::gadgets::{
    poseidon::CircuitRoundFunction,
    traits::{
        selectable::Selectable, 
        allocatable::CSAllocatableExt, 
        allocatable::CSAllocatable,
        encodable::CircuitEncodableExt
    },
    num::Num,
    boolean::Boolean,
    u8::UInt8,
    u16::UInt16,
    u32::UInt32,
    u160::*,
    u256::UInt256,
    queue::*
};
use boojum::gadgets::sha256::round_function::round_function_over_uint32;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::base_structures::{
    vm_state::*, 
    log_query::{LogQuery,LOG_QUERY_PACKED_WIDTH},
    decommit_query::*,
    memory_query::*,
};

use zkevm_opcode_defs::system_params::*;

use crate::{
    demux_log_queue::input::*,
    fsm_input_output::{*, circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH} 
};

use crate::storage_application::ConditionalWitnessAllocator;

pub fn unpack_code_into_memory_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: CodeDecommitterCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where 
    [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); UInt256::<F>::INTERNAL_STRUCT_LEN]:,
    [(); UInt256::<F>::INTERNAL_STRUCT_LEN + 1]:,
{
    let CodeDecommitterCircuitInstanceWitness {
        closed_form_input,
        sorted_requests_queue_witness,
        code_words,
    } = witness;

    let code_words: VecDeque<U256> = code_words.into_iter().flatten().collect();

    let mut structured_input =
        CodeDecommitterCycleInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());

    let requests_queue_state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &structured_input
            .observable_input
            .sorted_requests_queue_initial_state,
        &structured_input
            .hidden_fsm_input
            .decommittment_requests_queue_state
    );

    let mut requests_queue = 
        DecommitQueue::<F, 8, 12, 4, R>::from_state(cs, requests_queue_state);

    use crate::code_unpacker_sha256::full_state_queue::FullStateCircuitQueueWitness;
    requests_queue.witness = Arc::new(
        FullStateCircuitQueueWitness::from_inner_witness(sorted_requests_queue_witness)
    );

    let memory_queue_state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &structured_input
            .observable_input
            .memory_queue_initial_state,
        &structured_input
            .hidden_fsm_input
            .memory_queue_state
    );

    let mut memory_queue = 
        MemoryQueryQueue::<F, 8, 12, 4, R>::from_state(cs, memory_queue_state);

    use boojum::gadgets::traits::allocatable::CSPlaceholder;
    let mut starting_fsm_state = CodeDecommittmentFSM::placeholder(cs);
    starting_fsm_state.state_get_from_queue = Boolean::allocated_constant(cs, true);

    let initial_state = CodeDecommittmentFSM::conditionally_select(
        cs,
        structured_input.start_flag,
        &starting_fsm_state,
        &structured_input.hidden_fsm_input.internal_fsm,
    );

    let code_words_allocator = ConditionalWitnessAllocator::<F, UInt256<F>> {
        witness_source: Arc::new(RwLock::new(code_words))
    };

    let final_state = unpack_code_into_memory_inner(
        cs,
        &mut memory_queue,
        &mut requests_queue,
        initial_state,
        code_words_allocator,
        round_function,
        limit,
    );

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();
    // form the final state
    let done = final_state.finished;
    structured_input.completion_flag = done;
    structured_input.observable_output = CodeDecommitterOutputData::placeholder(cs);

    structured_input.observable_output.memory_queue_final_state =
        QueueState::conditionally_select(
            cs,
            structured_input.completion_flag,
            &final_memory_state,
            &structured_input.observable_output.memory_queue_final_state,
        );

    structured_input.hidden_fsm_output.internal_fsm = final_state;
    structured_input
        .hidden_fsm_output
        .decommittment_requests_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);

    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }
    
    input_commitment
}

// we take a request to decommit hash H into memory page X. Following our internal conventions
// we decommit individual elements starting from the index 1 in the page, and later on set a full length
// into index 0. All elements are 32 bytes
pub fn unpack_code_into_memory_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueryQueue<F, 8, 12, 4, R>,
    unpack_requests_queue: &mut DecommitQueue<F, 8, 12, 4, R>,
    initial_state: CodeDecommittmentFSM<F>,
    code_word_witness: ConditionalWitnessAllocator::<F, UInt256<F>>,
    _round_function: &R,
    limit: usize,
) -> CodeDecommittmentFSM<F>
where 
    [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); UInt256::<F>::INTERNAL_STRUCT_LEN]:,
    [(); UInt256::<F>::INTERNAL_STRUCT_LEN + 1]:,
{
    assert!(limit <= u32::MAX as usize);

    // const POP_QUEUE_OR_WRITE_ID: u64 = 0;
    // const FINALIZE_SHA256: u64 = 1;

    let mut state = initial_state;

    let mut half = F::ONE;
    half.double();
    half = half.inverse().unwrap();
    let half_num = Num::allocated_constant(cs, half);

    let words_to_bits = UInt32::allocated_constant(cs, 32 * 8);

    let initial_state_uint32 = boojum::gadgets::sha256::ivs_as_uint32(cs);

    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);

    let zero_u32 = UInt32::zero(cs);

    use zkevm_opcode_defs::VersionedHashDef;
    let versioned_hash_top_16_bits =
        (zkevm_opcode_defs::versioned_hash::ContractCodeSha256::VERSION_BYTE as u16) << 8;
    let versioned_hash_top_16_bits = UInt16::allocated_constant(cs, versioned_hash_top_16_bits);

    for _cycle in 0..limit {
        // we need exactly 3 sponges per cycle:
        // - two memory reads when we work on the existing decommittment
        // - and may be queue pop before it
        let (may_be_new_request, _) =
            unpack_requests_queue.pop_front(cs, state.state_get_from_queue);

        let hash = may_be_new_request.code_hash;

        let chunks = decompose_uint32_to_uint16s(cs, &hash.inner[7]);

        let version_hash_matches = UInt16::equals(
            cs,
            &chunks[1],
            &versioned_hash_top_16_bits,
        );

        state.state_get_from_queue.conditionally_enforce_true(cs, version_hash_matches);

        let uint_16_one = UInt16::allocated_constant(cs, 1);
        let length_in_words = chunks[0];
        let length_in_words = UInt16::conditionally_select(
            cs,
            state.state_get_from_queue,
            &length_in_words,
            &uint_16_one,
        );

        let length_in_rounds = unsafe {
            length_in_words.increment_unchecked(cs)
        };

        let length_in_rounds = length_in_rounds.into_num().mul(cs, &half_num);
        // length is always a multiple of 2 since we decided so

        let (length_in_rounds, _) = 
            UInt16::from_variable_checked(cs, length_in_rounds.get_variable());

        let (length_in_bits_may_be, _) = 
            unsafe {
                UInt32::from_variable_unchecked(
                    length_in_words.get_variable()
                ).non_widening_mul(cs, &words_to_bits)
            };

        // turn over the endianess
        // we IGNORE the highest 4 bytes
        let uint32_zero = UInt32::allocated_constant(cs, 0);
        let mut cutted_hash = hash;
        cutted_hash.inner[7] = uint32_zero;

        state.num_rounds_left = UInt16::conditionally_select(
            cs,
            state.state_get_from_queue,
            &length_in_rounds,
            &state.num_rounds_left,
        );
        state.length_in_bits = UInt32::conditionally_select(
            cs,
            state.state_get_from_queue,
            &length_in_bits_may_be,
            &state.length_in_bits,
        );
        state.timestamp = UInt32::conditionally_select(
            cs,
            state.state_get_from_queue,
            &may_be_new_request.timestamp,
            &state.timestamp,
        );
        state.current_page = UInt32::conditionally_select(
            cs,
            state.state_get_from_queue,
            &may_be_new_request.page,
            &state.current_page,
        );
        state.hash_to_compare_against = UInt256::conditionally_select(
            cs,
            state.state_get_from_queue,
            &cutted_hash,
            &state.hash_to_compare_against,
        );
        state.current_index = UInt32::conditionally_select(
            cs,
            state.state_get_from_queue,
            &uint32_zero,
            &state.current_index,
        );
        state.sha256_inner_state = <[UInt32<F>; 8]>::conditionally_select(
            cs,
            state.state_get_from_queue,
            &initial_state_uint32,
            &state.sha256_inner_state,
        );
        state.length_in_bits = UInt32::conditionally_select(
            cs,
            state.state_get_from_queue,
            &length_in_bits_may_be,
            &state.length_in_bits,
        );

        // we decommit if we either decommit or just got a new request
        let t = state.state_decommit.or(cs, state.state_get_from_queue);
        state.state_decommit = t;
        state.state_get_from_queue = boolean_false;

        // even though it's not that useful, we will do it in a checked way for ease of witness
        let may_be_num_rounds_left = unsafe {
            state.num_rounds_left.decrement_unchecked(cs)
        };
        state.num_rounds_left = UInt16::conditionally_select(
            cs,
            state.state_decommit,
            &may_be_num_rounds_left,
            &state.num_rounds_left,
        );

        let last_round = state.num_rounds_left.is_zero(cs);
        let finalize = last_round.and(cs, state.state_decommit);
        let not_last_round = last_round.negated(cs);
        let process_second_word = not_last_round.and(cs, state.state_decommit);

        // we either pop from the queue, or absorb-decommit, or finalize hash
        let code_word_0 = code_word_witness.conditionally_allocate(cs, state.state_decommit);
        let code_word_0_be_bytes = code_word_0.to_be_bytes(cs);

        let code_word_1 = code_word_witness.conditionally_allocate(cs, state.state_decommit);
        let code_word_1_be_bytes = code_word_1.to_be_bytes(cs);

        // perform two writes. It's never a "pointer" type
        let mem_query_0 = MemoryQuery {
            timestamp: state.timestamp,
            memory_page: state.current_page,
            index: state.current_index,
            rw_flag: boolean_true,
            value: code_word_0,
            is_ptr: boolean_false,
        };

        let state_index_incremented = unsafe {
            state
                .current_index
                .increment_unchecked(cs)
        };

        state.current_index = UInt32::conditionally_select(
            cs, 
            state.state_decommit, 
            &state_index_incremented, 
            &state.current_index
        ); 

        let mem_query_1 = MemoryQuery {
            timestamp: state.timestamp,
            memory_page: state.current_page,
            index: state.current_index,
            rw_flag: boolean_true,
            value: code_word_1,
            is_ptr: boolean_false,
        };

        // even if we do not write in practice then we will never use next value too

        let state_index_incremented = unsafe {
            state
                .current_index
                .increment_unchecked(cs)
        };

        state.current_index = UInt32::conditionally_select(
            cs, 
            process_second_word, 
            &state_index_incremented, 
            &state.current_index
        );

        memory_queue.push(cs, mem_query_0, state.state_decommit);
        memory_queue.push(cs, mem_query_1, process_second_word);

        // mind endianess!
        let mut sha256_input = [zero_u32; 16];
        for (dst, src) in sha256_input.iter_mut().zip(code_word_0_be_bytes.array_chunks::<4>().chain(code_word_1_be_bytes.array_chunks::<4>())) {
            *dst = UInt32::from_be_bytes(cs, *src);
        }

        // then conditionally form the second half of the block

        let mut sha256_padding = [zero_u32; 8];

        // padding of single byte of 1<<7 and some zeroes after
        sha256_padding[0] = UInt32::allocated_constant(cs, 1 << 31);

        // and final word that will encode the bit length of the input
        // and now put bitlength as BE, that is a little unfortunate, and we need to change endianess
        let bytes = state.length_in_bits.to_be_bytes(cs);
        sha256_padding[7] = UInt32::from_le_bytes(cs, bytes);

        assert_eq!(sha256_input.len(), 16);
        
        for (dst, src) in sha256_input[8..].iter_mut().zip(sha256_padding.iter()) {
            *dst = UInt32::conditionally_select(cs, finalize, src, dst);
        }

        let sha256_input: [_; 16] = sha256_input.try_into().unwrap();

        let mut new_internal_state = state.sha256_inner_state;
        round_function_over_uint32(cs, &mut new_internal_state, &sha256_input);

        state.sha256_inner_state = <[UInt32<F>; 8]>::conditionally_select(
            cs,
            state.state_decommit,
            &new_internal_state,
            &state.sha256_inner_state,
        );

        // make it into uint256, and do not forget to ignore highest two bytes
        let hash = UInt256{
            inner: [
                new_internal_state[7],
                new_internal_state[6],
                new_internal_state[5],
                new_internal_state[4],
                new_internal_state[3],
                new_internal_state[2],
                new_internal_state[1],
                UInt32::allocated_constant(cs, 0),
            ]
        };

        for (part_of_first, part_of_second) in hash
            .inner
            .iter()
            .zip(
                state.hash_to_compare_against
                    .inner
                    .iter()
            )
        {
            Num::conditionally_enforce_equal(
                cs, 
                finalize, 
                &part_of_first.into_num(), 
                &part_of_second.into_num()
            );
        }

        // finish
        let is_empty = unpack_requests_queue.is_empty(cs);
        let not_empty = is_empty.negated(cs);
        let done = is_empty.and(cs, finalize);
        state.finished = state.finished.or(cs, done);
        let proceed_next = not_empty.and(cs, finalize);
        state.state_get_from_queue = proceed_next;
        let continue_decommit = process_second_word;
        state.state_decommit = continue_decommit;
    }

    state
}

fn decompose_uint32_to_uint16s<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    value: &UInt32<F>,
) -> [UInt16<F>; 2] {
    let [byte_0, 
        byte_1, 
        byte_2, 
        byte_3
    ] = value.decompose_into_bytes(cs);
    
    [
        UInt16::from_le_bytes(cs, [byte_0, byte_1]),
        UInt16::from_le_bytes(cs, [byte_2, byte_3])
    ]
}