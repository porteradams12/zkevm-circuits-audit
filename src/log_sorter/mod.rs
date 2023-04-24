mod input;
use super::*;
use boojum::cs::{traits::cs::ConstraintSystem, gates::*};
use boojum::field::SmallField;
use boojum::gadgets::{
    poseidon::CircuitRoundFunction,
    traits::{selectable::Selectable, allocatable::{CSAllocatableExt, CSPlaceholder}, encodable::CircuitEncodableExt},
    num::Num,
    boolean::Boolean,
    u32::UInt32,
    queue::*,
    u256::UInt256,
    u8::UInt8
};
use crate::fsm_input_output::{ClosedFormInputCompactForm, commit_variable_length_encodable_item};
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::base_structures::log_query::LogQuery;
use crate::base_structures::{vm_state::*, 
    log_query::{LOG_QUERY_PACKED_WIDTH}};

use crate::demux_log_queue::StorageLogQueue;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
// This is a sorter of logs that are kind-of "pure", e.g. event emission or L2 -> L1 messages.
// Those logs do not affect a global state and may either be rolled back in full or not.
// We identify equality of logs using "timestamp" field that is a monotonic unique counter
// across the block
pub const STORAGE_LOG_RECORD_ENCODING_LEN: usize = 5;

use crate::log_sorter::input::*;
const NUM_PERMUTATION_ARG_CHALLENGES: usize = STORAGE_LOG_RECORD_ENCODING_LEN + 1;

pub fn sort_and_deduplicate_events_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: EventsDeduplicatorInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]  
where [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:{

//use table

    let structured_input_witness = witness.closed_form_input;
    let initial_queue_witness = witness.initial_queue_witness;
    let intermediate_sorted_queue_witness = witness.intermediate_sorted_queue_witness;

    let mut structured_input = EventsDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    );

    let unsorted_queue_from_passthrough: CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R> = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .initial_log_queue_state
            .head,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail.tail,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail.length,
    );


    // passthrough must be trivial
    let zero_num = Num::zero(cs);
     for el in unsorted_queue_from_passthrough.head.iter() {
        Num::enforce_equal(cs, el, &zero_num);
    }

    let unsorted_queue_from_fsm: CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R> = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .tail.tail,
        structured_input
            .hidden_fsm_input
            .initial_unsorted_queue_state
            .tail.length,
    );

    let mut state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &unsorted_queue_from_passthrough.into_state(),
        &unsorted_queue_from_fsm.into_state()
    );

    let mut unsorted_queue = StorageLogQueue::<F, R>::from_raw_parts(
        cs, 
        state.head, 
        state.tail.tail, 
        state.tail.length
    );

    use std::sync::Arc;
    unsorted_queue.witness = Arc::new(initial_queue_witness);

    let intermediate_sorted_queue_from_passthrough: CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R> = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .head,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail.tail,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail.length,
    );

    // passthrough must be trivial
    let zero_num = Num::zero(cs);
    for el in intermediate_sorted_queue_from_passthrough.head.iter() {
        Num::enforce_equal(cs, el, &zero_num);
    }

    let intermediate_sorted_queue_from_fsm: CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R> = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .tail.tail,
        structured_input
            .hidden_fsm_input
            .intermediate_sorted_queue_state
            .tail.length,
    );

    let mut state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough.into_state(),
        &intermediate_sorted_queue_from_fsm.into_state()
    );
    let mut intermediate_sorted_queue = StorageLogQueue::<F, R>::from_raw_parts(
        cs, 
        state.head, 
        state.tail.tail, 
        state.tail.length
    );

    intermediate_sorted_queue.witness = Arc::new(intermediate_sorted_queue_witness);


    let final_sorted_queue_from_fsm: CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R> = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .tail.tail,
        structured_input
            .hidden_fsm_input
            .final_result_queue_state
            .tail.length,
    );
    let empty_state = QueueState::empty(cs);

    let mut final_sorted_state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &empty_state,
        &final_sorted_queue_from_fsm.into_state()
    );
    let mut final_sorted_queue = StorageLogQueue::<F, R>::from_raw_parts(
        cs, 
        final_sorted_state.head, 
        final_sorted_state.tail.tail, 
        final_sorted_state.tail.length
    );

    // get challenges for permutation argument
    let mut fs_input = vec![];
    fs_input.extend_from_slice(&unsorted_queue_from_passthrough.tail.map(|el| el.get_variable()));
    fs_input.push(unsorted_queue_from_passthrough.length.get_variable());

    fs_input.extend_from_slice(&intermediate_sorted_queue_from_passthrough.tail.map(|el| el.get_variable()));
    fs_input.push(intermediate_sorted_queue_from_passthrough.length.get_variable());


    let total_elements_to_absorb = MEMORY_QUERY_PACKED_WIDTH;
    let num_rounds = (total_elements_to_absorb + 8 - 1) / 8;
    let mut elements_source= fs_input.into_iter();

    let zero_element = cs.allocate_constant(F::ZERO);

    let mut capacity_elements = [zero_element; 4];
    let mut sponge_state = [zero_element; 12];

    for _ in 0..num_rounds {
        let mut to_absorb = [zero_element; 8];
        for (dst, src) in to_absorb.iter_mut().zip(&mut elements_source) {
            *dst = src;
        }

        let result_state = R::absorb_with_replacement(cs, to_absorb, capacity_elements);
        capacity_elements.copy_from_slice(&result_state[8..]);
        sponge_state = result_state;
    }

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..NUM_PERMUTATION_ARG_CHALLENGES {
        if taken == MEMORY_QUERY_PACKED_WIDTH {
            // run round
            sponge_state = R::compute_round_function(cs, sponge_state);
            taken = 0;
        }

        let challenge = sponge_state[taken];
        fs_challenges.push(Num::from_variable(challenge));

        taken += 1;
    }

    let mut fs_challenge= [[Num::zero(cs);  MEMORY_QUERY_PACKED_WIDTH + 1]; NUM_PERMUTATION_ARG_CHALLENGES];
    for (src, dst) in fs_challenges
    .chunks(MEMORY_QUERY_PACKED_WIDTH + 1)
    .zip(fs_challenge.iter_mut()) {
        dst.copy_from_slice(src);
    }


    let one =  Num::from_variable(cs.allocate_constant(F::ONE));
    let zero = Num::from_variable(cs.allocate_constant(F::ZERO));
    let make_one_chunks: [Num<F>; DEFAULT_NUM_CHUNKS] = [one, zero, zero, zero];
    let initial_lhs = Num::parallel_select(
        cs,
        structured_input.start_flag,
        &make_one_chunks,
        &structured_input.hidden_fsm_input.lhs_accumulator,
    );

    let initial_rhs = Num::parallel_select(
        cs,
        structured_input.start_flag,
        &make_one_chunks,
        &structured_input.hidden_fsm_input.rhs_accumulator,
    );

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    // let make_zero_chunks: [Num<F>; DEFAULT_NUM_CHUNKS] = [zero, zero, zero, zero];
    let zero = Num::zero(cs);
    let previous_packed_key = Num::conditionally_select(
        cs,
        structured_input.start_flag,
        &zero,
        &structured_input.hidden_fsm_input.previous_packed_key
    );

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let empty_storage = LogQuery::empty(cs);
    let previous_item = LogQuery::conditionally_select(
        cs,
        structured_input.start_flag,
        &empty_storage,
        &structured_input.hidden_fsm_input.previous_item
    );

    let (
        new_lhs,
        new_rhs,
        previous_packed_key,
        previous_item,
    ) = repack_and_prove_events_rollbacks_inner(
        cs,
        initial_lhs,
        initial_rhs,
        &mut unsorted_queue,
        &mut intermediate_sorted_queue,
        &mut final_sorted_queue,
        structured_input.start_flag,
        fs_challenge,
        previous_packed_key,
        previous_item,
        round_function,
        limit,
    );

    let unsorted_is_empty = unsorted_queue.is_empty(cs);
    let sorted_is_empty = intermediate_sorted_queue.is_empty(cs);

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty);

    let completed = unsorted_queue.length.is_zero(cs);
    for (lhs, rhs) in new_lhs.iter().zip(new_rhs.iter()) {
        Num::conditionally_enforce_equal(cs, completed, lhs, rhs);
    }
    // form the final state
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_item = previous_item;
    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;

    structured_input
        .hidden_fsm_output
        .initial_unsorted_queue_state = unsorted_queue.into_state();
    structured_input
        .hidden_fsm_output
        .intermediate_sorted_queue_state = intermediate_sorted_queue.into_state();

    structured_input.completion_flag = completed;

    let empty_state = QueueState::empty(cs);
    let final_queue_for_observable_output = QueueState::conditionally_select(
        cs, 
        completed, 
        &final_sorted_queue.into_state(), 
        &empty_state
    );

    structured_input.observable_output.final_queue_state = final_queue_for_observable_output;

    structured_input
        .hidden_fsm_output
        .final_result_queue_state = final_sorted_queue.into_state();

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);

    // dbg!(compact_form.create_witness());
    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}
use crate::base_structures::memory_query::MEMORY_QUERY_PACKED_WIDTH;
pub fn repack_and_prove_events_rollbacks_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    mut lhs: [Num<F>; 4],
    mut rhs: [Num<F>; 4],
    unsorted_queue: &mut StorageLogQueue<F, R>,
    intermediate_sorted_queue: &mut StorageLogQueue<F, R>,
    result_queue: &mut StorageLogQueue<F, R>,
    is_start: Boolean<F>,
    fs_challenges: [[Num<F>; MEMORY_QUERY_PACKED_WIDTH + 1]; NUM_PERMUTATION_ARG_CHALLENGES],
    mut previous_packed_key: Num<F>,
    mut previous_item: LogQuery<F>,
    round_function: &R,
    limit: usize,
) -> (
    [Num<F>; 4], 
    [Num<F>; 4],
        Num<F>,
        LogQuery<F>
    ) where [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]: {
    assert!(limit <= u32::MAX as usize);

    // we can recreate it here, there are two cases:
    // - we are 100% empty, but it's the only circuit in this case
    // - otherwise we continue, and then it's not trivial
    let no_work = unsorted_queue.is_empty(cs);
    let mut previous_is_trivial = Boolean::multi_or(cs, &[no_work, is_start]);

    let unsorted_queue_lenght = Num::from_variable(unsorted_queue.length.get_variable());
    let intermediate_sorted_queue_lenght = Num::from_variable(intermediate_sorted_queue.length.get_variable());

    Num::enforce_equal(cs,  &unsorted_queue_lenght, &intermediate_sorted_queue_lenght);

    let additive_part = fs_challenges[NUM_PERMUTATION_ARG_CHALLENGES - 1];

    // reallocate and simultaneously collapse rollbacks

    const PACKED_WIDTHS: [usize; 1] = [33];

    for _cycle in 0..limit {
        let original_is_empty = unsorted_queue.is_empty(cs);
        let sorted_is_empty = intermediate_sorted_queue.is_empty(cs);
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty);

        let should_pop = original_is_empty.negated(cs);
        let is_trivial = should_pop.negated(cs);

        let (_, original_encoding) = unsorted_queue.pop_front(
            cs,
            should_pop,
        );
        let (sorted_item, sorted_encoding) =
        intermediate_sorted_queue.pop_front(cs, should_pop);

        // we also ensure that items are "write" unless it's a padding
        sorted_item.rw_flag.conditionally_enforce_false(cs, original_is_empty);

        assert_eq!(original_encoding.len(), sorted_encoding.len());
        assert_eq!(original_encoding.len(), fs_challenges.len() - 1);
        for ((challenges, lhs), rhs) in fs_challenges
            .iter()
            .zip(lhs.iter_mut())
            .zip(rhs.iter_mut())
        {
            let mut lhs_contribution = challenges[MEMORY_QUERY_PACKED_WIDTH];
            let mut rhs_contribution = challenges[MEMORY_QUERY_PACKED_WIDTH];

            for ((original_el, sorted_el), challenge) in original_encoding
                .iter()
                .zip(sorted_encoding.iter())
                .zip(challenges.iter())
            {
                let left = Num::from_variable(*original_el).mul(cs, challenge);
                lhs_contribution = lhs_contribution.add(cs, &left);
                let right = Num::from_variable(*sorted_el).mul(cs, challenge);
                rhs_contribution = rhs_contribution.add(cs, &right);
            }

            let new_lhs = lhs.mul(cs, &lhs_contribution);
            let new_rhs = rhs.mul(cs, &rhs_contribution);

            *lhs = Num::conditionally_select(cs, should_pop, &new_lhs, &lhs);
            *rhs = Num::conditionally_select(cs, should_pop, &new_rhs, &rhs);
        }
        // now ensure sorting
        {
            // sanity check - all such logs are "write into the sky"
            sorted_item.rw_flag.conditionally_enforce_false(cs,  is_trivial);

            // check if keys are equal and check a value
            let packed_key = pack_key(cs, (sorted_item.timestamp, sorted_item.rollback));

            // ensure sorting for uniqueness timestamp and rollback flag
            // We know that timestamps are unique accross logs, and are also the same between write and rollback
            let (_keys_are_equal, new_key_is_greater) =
                prepacked_long_comparison(cs, &[packed_key], &[previous_packed_key], &PACKED_WIDTHS);

            // keys are always ordered no matter what, and are never equal unless it's padding
            new_key_is_greater.conditionally_enforce_false(cs, is_trivial);

            // there are only two cases when keys are equal:
            // - it's a padding element
            // - it's a rollback

            // it's enough to compare timestamps as VM circuit guarantees uniqueness of the if it's not a padding
            let same_log = UInt32::equals(cs, &sorted_item.timestamp, &previous_item.timestamp);

            let mut tmp = vec![];
            for (a, b) in sorted_item.written_value.inner.iter().zip(previous_item.written_value.inner.iter()){
                let values_are_equal = UInt32::equals(cs, &a, &b);
                tmp.push(values_are_equal);
            }

            let values_are_equal = Boolean::multi_and(cs, &tmp);
            let negate_previous_is_trivial = previous_is_trivial.negated(cs);
            let should_enforce = Boolean::multi_and(cs, &[same_log, negate_previous_is_trivial]);
            values_are_equal.conditionally_enforce_true(cs, should_enforce);

            let negate_trivial = is_trivial.negated(cs);
            let this_item_is_non_trivial_rollback =
                Boolean::multi_and(cs, &[sorted_item.rollback, negate_trivial]);
            let negate_previous_item_rollback = previous_item.rollback.negated(cs);
            let prevous_item_is_non_trivial_write = Boolean::multi_and(
                cs,
                &[
                    negate_previous_item_rollback,
                    negate_previous_is_trivial,
                ],
            );
            let is_sequential_rollback = Boolean::multi_and(
                cs,
                &[
                    this_item_is_non_trivial_rollback,
                    prevous_item_is_non_trivial_write,
                ],
            );
            same_log.conditionally_enforce_true(cs, is_sequential_rollback);

            // decide if we should add the PREVIOUS into the queue
            // We add only if previous one is not trivial,
            // and it had a different key, and it wasn't rolled back
            let negate_same_log = same_log.negated(cs);
            let add_to_the_queue = Boolean::multi_and(
                cs,
                &[
                    negate_previous_is_trivial,
                    negate_same_log,
                    negate_previous_item_rollback,
                ],
            );
            let boolean_false = Boolean::allocated_constant(cs, false);
            // cleanup some fields that are not useful
            let query_to_add = LogQuery {
                address: previous_item.address,
                key: previous_item.key,
                read_value: UInt256::zero(cs),
                written_value: previous_item.written_value,
                rw_flag: boolean_false,
                aux_byte: UInt8::zero(cs),
                rollback: boolean_false,
                is_service: previous_item.is_service,
                shard_id: previous_item.shard_id,
                tx_number_in_block: previous_item.tx_number_in_block,
                timestamp: UInt32::zero(cs),
            };

            result_queue.push(cs, query_to_add, add_to_the_queue);

            previous_is_trivial = is_trivial;
            previous_item = sorted_item;
            previous_packed_key = packed_key;
        }
    }
    
    // finalization step - same way, check if last item is not a rollback
    {
        let now_empty = unsorted_queue.is_empty(cs);

        let negate_previous_is_trivial = previous_is_trivial.negated(cs);
        let negate_previous_item_rollback = previous_item.rollback.negated(cs);
        let add_to_the_queue = Boolean::multi_and(
            cs,
            &[
                negate_previous_is_trivial,
                negate_previous_item_rollback,
                now_empty
            ],
        );
        let boolean_false = Boolean::allocated_constant(cs, false);
        let query_to_add = LogQuery {
            address: previous_item.address,
            key: previous_item.key,
            read_value: UInt256::zero(cs),
            written_value: previous_item.written_value,
            rw_flag: boolean_false,
            aux_byte: UInt8::zero(cs),
            rollback: boolean_false,
            is_service: previous_item.is_service,
            shard_id: previous_item.shard_id,
            tx_number_in_block: previous_item.tx_number_in_block,
            timestamp: UInt32::zero(cs),
        };

        result_queue.push(cs, query_to_add, add_to_the_queue);
    }

    (
        lhs,
        rhs,
        previous_packed_key,
        previous_item
    )
}

pub fn pack_key<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    key_tuple: (UInt32<F>, Boolean<F>),
) -> Num<F>{


    let (timestamp, rollback) = key_tuple;
    // 32 + 1 = 33 in total
    let value_0 = Num::linear_combination(
        cs,
        &[(rollback.get_variable(), F::ONE),
        (timestamp.get_variable(), F::from_u64_unchecked(1u64 << 32)),
        ]
    );
    value_0
}
/// Check that a == b and a > b by performing a long subtraction b - a with borrow.
/// Both a and b are considered as least significant word first
#[track_caller]
pub fn prepacked_long_comparison<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &[Num<F>],
    b: &[Num<F>],
    width_data: &[usize],
) -> (Boolean<F>, Boolean<F>){
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), width_data.len());

    let mut previous_borrow = Boolean::allocated_constant(cs, false);
    let mut limbs_are_equal = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        let a_uint32 = unsafe {
            UInt32::from_variable_unchecked(a.get_variable())
        };
        let b_uint32 = unsafe {
            UInt32::from_variable_unchecked(b.get_variable())
        };
        let (diff, borrow, _) = a_uint32.overflowing_sub_with_borrow_in(cs, b_uint32, previous_borrow);
        let equal = diff.is_zero(cs);
        limbs_are_equal.push(equal);
        previous_borrow = borrow;
    }
    let final_borrow = previous_borrow;
    let eq = Boolean::multi_and(cs, &limbs_are_equal);

    (eq, final_borrow)
}

