use super::*;

use crate::base_structures::log_query::LOG_QUERY_PACKED_WIDTH;
use crate::fsm_input_output::ClosedFormInputCompactForm;

use boojum::cs::{traits::cs::ConstraintSystem, gates::*};
use boojum::field::SmallField;
use boojum::gadgets::queue::full_state_queue::FullStateCircuitQueueWitness;
use boojum::gadgets::{
    traits::{selectable::Selectable, allocatable::CSAllocatableExt},
    num::Num,
    boolean::Boolean,
    u32::UInt32,
    queue::*
};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::encodable::CircuitEncodable;
use boojum::gadgets::traits::allocatable::CSPlaceholder;
use crate::storage_validity_by_grand_product::unpacked_long_comparison;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::base_structures::vm_state::*;
use crate::base_structures::decommit_query::DecommitQueue;
use crate::{
    fsm_input_output::{*, circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH} 
};
use boojum::gadgets::u256::UInt256;
use crate::base_structures::{
    decommit_query::DecommitQuery,
    memory_query::MEMORY_QUERY_PACKED_WIDTH};
use crate::sort_decommittment_requests::input::*;

pub mod input;

// This is a sorter of logs that are kind-of "pure", F.g. event emission or L2 -> L1 messages.
// Those logs do not affect a global state and may either be rolled back in full or not.
// We identify equality of logs using "timestamp" field that is a monotonic unique counter
// across the block
pub const NUM_PERMUTATION_ARG_CHALLENGES: usize = LOG_QUERY_PACKED_WIDTH + 1;

pub fn sort_and_deduplicate_code_decommittments_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: CodeDecommittmentsDeduplicatorInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH] 
where [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:{
    // as usual we assume that a caller of this fuunction has already split input queue,
    // so it can be comsumed in full

    //use table
    let CodeDecommittmentsDeduplicatorInstanceWitness {
        closed_form_input,
        initial_queue_witness,
        sorted_queue_witness,
    } = witness;

    let mut structured_input = CodeDecommittmentsDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        closed_form_input.clone()
    );

    let initial_queue_from_passthrough_state = structured_input
            .observable_input
            .initial_queue_state;
    let initial_log_queue_state_from_fsm_state = structured_input
            .hidden_fsm_input
            .initial_queue_state;

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &initial_queue_from_passthrough_state,
        &initial_log_queue_state_from_fsm_state,
    );
    let mut initial_queue = DecommitQueue::<F, R>::from_state(cs, state);

    // passthrough must be trivial
    initial_queue_from_passthrough_state.enforce_trivial_head(cs);
    
    use std::sync::Arc;
    let initial_queue_witness = FullStateCircuitQueueWitness::from_inner_witness(initial_queue_witness);
    initial_queue.witness = Arc::new(initial_queue_witness);

    let intermediate_sorted_queue_from_passthrough_state = structured_input
            .observable_input
            .sorted_queue_initial_state;
    let intermediate_sorted_queue_from_fsm_input_state = structured_input
            .hidden_fsm_input
            .sorted_queue_state;

    // it must be trivial
    intermediate_sorted_queue_from_passthrough_state.enforce_trivial_head(cs);

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough_state,
        &intermediate_sorted_queue_from_fsm_input_state
    );
    let mut intermediate_sorted_queue = DecommitQueue::<F, R>::from_state(cs, state);

    let sorted_queue_witness = FullStateCircuitQueueWitness::from_inner_witness(sorted_queue_witness);
    intermediate_sorted_queue.witness = Arc::new(sorted_queue_witness);

    let empty_state = QueueState::empty(cs);

    let final_sorted_queue_from_fsm_state = structured_input
            .hidden_fsm_input
            .final_queue_state;
    
    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &empty_state,
        &final_sorted_queue_from_fsm_state,
    );
    let mut final_sorted_queue = DecommitQueue::<F, R>::from_state(cs, state);

    let challenges = crate::utils::produce_fs_challenges::<F, CS, R, FULL_SPONGE_QUEUE_STATE_WIDTH, {MEMORY_QUERY_PACKED_WIDTH + 1}, DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS> (
        cs, 
        structured_input
            .observable_input
            .initial_queue_state
            .tail, 
        structured_input
            .observable_input
            .sorted_queue_initial_state
            .tail,
        round_function
    );

    let one = Num::allocated_constant(cs, F::ONE);
    let initial_lhs = Num::parallel_select(
        cs,
        structured_input.start_flag,
        &[one; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
        &structured_input.hidden_fsm_input.lhs_accumulator,
    );

    let initial_rhs = Num::parallel_select(
        cs,
        structured_input.start_flag,
        &[one; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
        &structured_input.hidden_fsm_input.rhs_accumulator,
    );

    let trivial_record = DecommitQuery::placeholder(cs);
    let mut previous_record = DecommitQuery::conditionally_select(
        cs, 
        structured_input.start_flag, 
        &trivial_record, 
        &structured_input.hidden_fsm_input.previous_record,
    );

    let zero_u32 = UInt32::zero(cs);
    let mut previous_packed_key = <[UInt32<F>; PACKED_KEY_LENGTH]>::conditionally_select(
        cs, 
        structured_input.start_flag, 
        &[zero_u32; PACKED_KEY_LENGTH], 
        &structured_input.hidden_fsm_input.previous_packed_key,
    );

    let mut first_encountered_timestamp = UInt32::conditionally_select(
        cs, 
        structured_input.start_flag, 
        &zero_u32, 
        &structured_input.hidden_fsm_input.first_encountered_timestamp,
    );

    let (completed, new_lhs,new_rhs) = sort_and_deduplicate_code_decommittments_inner(
        cs,
        &mut initial_queue,
        &mut intermediate_sorted_queue,
        &mut final_sorted_queue,
        initial_lhs,
        initial_rhs,
        challenges,
        &mut previous_packed_key,
        &mut first_encountered_timestamp,
        &mut previous_record,
        structured_input.start_flag,
        limit,
    );

    for (lhs, rhs) in new_lhs.iter().zip(new_rhs.iter()) {
        Num::conditionally_enforce_equal(cs, completed, lhs, rhs);
    }
    // form the final state
    structured_input.observable_output = CodeDecommittmentsDeduplicatorOutputData::placeholder(cs);

    structured_input.hidden_fsm_output = CodeDecommittmentsDeduplicatorFSMInputOutput::placeholder(cs);
    structured_input.hidden_fsm_output.initial_queue_state = initial_queue.into_state();
    structured_input.hidden_fsm_output.sorted_queue_state = intermediate_sorted_queue.into_state();
    structured_input.hidden_fsm_output.final_queue_state = final_sorted_queue.into_state();
    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_record = previous_record;
    structured_input.hidden_fsm_output.first_encountered_timestamp = first_encountered_timestamp;

    structured_input.observable_output.final_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.final_queue_state,
        &structured_input.observable_output.final_queue_state
    );

    structured_input.completion_flag = completed;

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

pub fn sort_and_deduplicate_code_decommittments_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    original_queue: &mut DecommitQueue<F, R>,
    sorted_queue: &mut DecommitQueue<F, R>,
    result_queue: &mut DecommitQueue<F, R>,
    mut lhs: [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
    mut rhs: [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
    fs_challenges: [[Num<F>; MEMORY_QUERY_PACKED_WIDTH + 1]; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
    previous_packed_key: &mut [UInt32<F>; PACKED_KEY_LENGTH],
    first_encountered_timestamp: &mut UInt32<F>,
    previous_record: &mut DecommitQuery<F>,
    start_flag: Boolean<F>,
    limit: usize,
) -> (
    Boolean<F>, 
    [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS], 
    [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS]
) 
    where [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    assert!(limit <= u32::MAX as usize);
    let unsorted_queue_length = Num::from_variable(original_queue.length.get_variable());
    let intermediate_sorted_queue_length = Num::from_variable(sorted_queue.length.get_variable());

    Num::enforce_equal(cs,  &unsorted_queue_length, &intermediate_sorted_queue_length);

    let no_work = original_queue.is_empty(cs);
    
    let mut previous_item_is_trivial = no_work.or(cs, start_flag);

    // Simultaneously pop, prove sorting and resolve logic

    for _cycle in 0..limit {
        let original_is_empty = original_queue.is_empty(cs);
        let sorted_is_empty = sorted_queue.is_empty(cs);
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty);

        let should_pop = original_is_empty.negated(cs);
        let is_trivial = original_is_empty;

        let (_, original_encoding) =
            original_queue.pop_front(cs, should_pop);
        let (sorted_item, sorted_encoding) =
            sorted_queue.pop_front(cs, should_pop);

        // we make encoding that is the same as defined for timestamped item
        assert_eq!(original_encoding.len(), sorted_encoding.len());
        assert_eq!(lhs.len(), rhs.len());

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
                lhs_contribution = Num::fma(
                    cs, 
                    &Num::from_variable(*original_el),
                    challenge, 
                    &F::ONE, 
                    &lhs_contribution, 
                    &F::ONE
                );

                rhs_contribution = Num::fma(
                    cs, 
                    &Num::from_variable(*sorted_el),
                    challenge, 
                    &F::ONE, 
                    &rhs_contribution, 
                    &F::ONE
                );
            }

            let new_lhs = lhs.mul(cs, &lhs_contribution);
            let new_rhs = rhs.mul(cs, &rhs_contribution);

            *lhs = Num::conditionally_select(cs, should_pop, &new_lhs, &lhs);
            *rhs = Num::conditionally_select(cs, should_pop, &new_rhs, &rhs);
        }

        // check if keys are equal and check a value
        let packed_key = concatenate_key(cs, (sorted_item.timestamp, sorted_item.code_hash));

        // ensure sorting for uniqueness timestamp and rollback flag
        // We know that timestamps are unique accross logs, and are also the same between write and rollback
        let (_keys_are_equal, new_key_is_greater) =
            unpacked_long_comparison(cs, &packed_key, &*previous_packed_key);
        // always ascedning
        new_key_is_greater.conditionally_enforce_true(cs, should_pop);
        
        let same_hash = UInt256::equals(
            cs,
            &previous_record.code_hash,
            &sorted_item.code_hash,
        );

        // if we get new hash then it my have a "first" marker
        let different_hash = same_hash.negated(cs);
        let enforce_must_be_first = Boolean::multi_and(cs, &[different_hash, should_pop]);
        sorted_item.is_first.conditionally_enforce_true(cs, enforce_must_be_first);

        // otherwise it should have the same memory page
        let previous_is_non_trivial = previous_item_is_trivial.negated(cs);
        let enforce_same_memory_page = Boolean::multi_and(cs, &[same_hash, previous_is_non_trivial]);
        
        Num::conditionally_enforce_equal(
            cs,
            enforce_same_memory_page,
            &sorted_item.page.into_num(),
            &previous_record.page.into_num(),
        );
    

        // decide if we should add the PREVIOUS into the queue
        let add_to_the_queue = Boolean::multi_and(cs, &[previous_is_non_trivial, different_hash]);

        let mut record_to_add = *previous_record;
        record_to_add.is_first = Boolean::allocated_constant(cs, true); // we use convension to be easier consistent with out of circuit part
        record_to_add.timestamp = *first_encountered_timestamp;
        result_queue.push(cs, record_to_add, add_to_the_queue);

        previous_item_is_trivial = is_trivial;
        // may be update the timestamp
        *first_encountered_timestamp = UInt32::conditionally_select(
            cs,
            same_hash,
            &first_encountered_timestamp,
            &sorted_item.timestamp,
        );
        *previous_record = sorted_item;
        *previous_packed_key = packed_key;
    }

    // if this circuit is the last one the queues must be empty and grand products must be equal
    let completed = original_queue.is_empty(cs);
    let sorted_queue_is_empty = sorted_queue.is_empty(cs);
    Boolean::enforce_equal(cs, &completed, &sorted_queue_is_empty);

    // finalization step - push the last one if necessary
    {
        let previous_is_non_trivial = previous_item_is_trivial.negated(cs);
        let add_to_the_queue = Boolean::multi_and(cs, &[previous_is_non_trivial, completed]);

        let mut record_to_add = *previous_record;
        record_to_add.is_first = Boolean::allocated_constant(cs, true); // we use convension to be easier consistent with out of circuit part
        record_to_add.timestamp = *first_encountered_timestamp;

        result_queue.push(cs, record_to_add, add_to_the_queue);
    }

    (completed, lhs, rhs)
}

fn concatenate_key<F: SmallField, CS: ConstraintSystem<F>>(
    _cs: &mut CS,
    key_tuple: (UInt32<F>, UInt256<F>),
) -> [UInt32<F>; PACKED_KEY_LENGTH] {
    // LE packing so comparison is subtraction
    let (timestamp, key) = key_tuple;
    [
        timestamp,

        key.inner[0],
        key.inner[1],
        key.inner[2],
        key.inner[3],
        key.inner[4],
        key.inner[5],
        key.inner[6],
        key.inner[7],
    ]
}