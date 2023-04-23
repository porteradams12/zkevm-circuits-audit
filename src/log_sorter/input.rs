use derivative::*;
use cs_derive::*;
use boojum::cs::{
    traits::cs::ConstraintSystem,
    Variable
};
use boojum::serde_utils::BigArraySerde;
use boojum::field::SmallField;
use boojum::gadgets::queue::QueueState;
use crate::base_structures::{vm_state::*, 
    log_query::{LogQuery,LOG_QUERY_PACKED_WIDTH}, 
};
use boojum::gadgets::{
    queue::*,
    traits::{allocatable::*, selectable::Selectable, encodable::CircuitVarLengthEncodable, witnessable::WitnessHookable},
    boolean::Boolean,
    num::Num
};

pub const DEFAULT_NUM_CHUNKS: usize = 4;

#[derive(Derivative, CSAllocatable, CSVarLengthEncodable, CSSelectable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct EventsDeduplicatorFSMInputOutput<F: SmallField> {
    pub lhs_accumulator: [Num<F>; DEFAULT_NUM_CHUNKS],
    pub rhs_accumulator: [Num<F>; DEFAULT_NUM_CHUNKS],
    pub initial_unsorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub final_result_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub previous_packed_key: Num<F>,
    pub previous_item: LogQuery<F>
}

impl<F: SmallField> CSPlaceholder<F> for EventsDeduplicatorFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            lhs_accumulator: [Num::zero(cs); DEFAULT_NUM_CHUNKS],
            rhs_accumulator: [Num::zero(cs); DEFAULT_NUM_CHUNKS],
            initial_unsorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            final_result_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            previous_packed_key:Num::zero(cs),
            previous_item: LogQuery::<F>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct EventsDeduplicatorInputData<F: SmallField>  {
    pub initial_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for EventsDeduplicatorInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        
        Self {
            initial_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct EventsDeduplicatorOutputData<F: SmallField> {
    pub final_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for EventsDeduplicatorOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        
        Self {
            final_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type EventsDeduplicatorInputOutput<F> = 
crate::fsm_input_output::ClosedFormInput<
    F,
    EventsDeduplicatorFSMInputOutput<F>,
    EventsDeduplicatorInputData<F>,
    EventsDeduplicatorOutputData<F>,
>;
pub type EventsDeduplicatorInputOutputWitness<F> = 
crate::fsm_input_output::ClosedFormInputWitness<
    F,
    EventsDeduplicatorFSMInputOutput<F>,
    EventsDeduplicatorInputData<F>,
    EventsDeduplicatorOutputData<F>,
>;

pub struct EventsDeduplicatorInstanceWitness<F: SmallField> {
    pub closed_form_input: EventsDeduplicatorInputOutputWitness<F>,
    pub initial_queue_witness: CircuitQueueWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
    pub intermediate_sorted_queue_witness: CircuitQueueWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
}
