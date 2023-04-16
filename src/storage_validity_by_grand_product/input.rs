use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::{
    gadgets::{
        boolean::Boolean,
        num::*,
        queue::*,
        traits::{
            allocatable::*, encodable::CircuitVarLengthEncodable, selectable::Selectable,
            witnessable::WitnessHookable,
        },
        u160::*,
        u256::*,
        u32::*,
        u8::*,
    },
    serde_utils::BigArraySerde,
};
use cs_derive::*;
use derivative::*;

// FSM

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorFSMInputOutput<F: SmallField> {
    pub lhs_accumulator: Num<F>,
    pub rhs_accumulator: Num<F>,
    pub current_unsorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub current_intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub current_final_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub cycle_idx: UInt32<F>,
    pub previous_packed_key: [Num<F>; 2],
    pub previous_key: UInt256<F>,
    pub previous_address: UInt160<F>,
    pub previous_timestamp: UInt32<F>,
    pub previous_shard_id: UInt8<F>,
    pub this_cell_has_explicit_read_and_rollback_depth_zero: Boolean<F>,
    pub this_cell_base_value: UInt256<F>,
    pub this_cell_current_value: UInt256<F>,
    pub this_cell_current_depth: UInt32<F>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            lhs_accumulator: Num::<F>::zero(cs),
            rhs_accumulator: Num::<F>::zero(cs),
            current_unsorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            current_intermediate_sorted_queue_state:
                QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            current_final_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            cycle_idx: UInt32::<F>::zero(cs),
            previous_packed_key: [Num::zero(cs); 2],
            previous_key: UInt256::<F>::zero(cs),
            previous_address: UInt160::<F>::zero(cs),
            previous_timestamp: UInt32::<F>::zero(cs),
            previous_shard_id: UInt8::<F>::zero(cs),
            this_cell_has_explicit_read_and_rollback_depth_zero:
                Boolean::<F>::allocate_without_value(cs),
            this_cell_base_value: UInt256::<F>::zero(cs),
            this_cell_current_value: UInt256::<F>::zero(cs),
            this_cell_current_depth: UInt32::<F>::zero(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorInputData<F: SmallField> {
    pub unsorted_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            unsorted_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorOutputData<F: SmallField> {
    pub final_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            final_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type StorageDeduplicatorInputOutput<F> = crate::fsm_input_output::ClosedFormInput<
    F,
    StorageDeduplicatorFSMInputOutput<F>,
    StorageDeduplicatorInputData<F>,
    StorageDeduplicatorOutputData<F>,
>;
pub type StorageDeduplicatorInputOutputWitness<F> = crate::fsm_input_output::ClosedFormInputWitness<
    F,
    StorageDeduplicatorFSMInputOutput<F>,
    StorageDeduplicatorInputData<F>,
    StorageDeduplicatorOutputData<F>,
>;

pub struct StorageDeduplicatorInstanceWitness<F: SmallField> {
    pub closed_form_input: StorageDeduplicatorInputOutputWitness<F>,
    pub unsorted_queue_witness: CircuitQueueWitness<F, LogQuery<F>, 5, LOG_QUERY_PACKED_WIDTH>,
    pub intermediate_sorted_queue_witness:
        CircuitQueueWitness<F, LogQuery<F>, 5, LOG_QUERY_PACKED_WIDTH>,
}
