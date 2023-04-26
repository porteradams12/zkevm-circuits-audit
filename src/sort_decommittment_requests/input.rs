use cs_derive::*;
use boojum::field::SmallField;
use boojum::cs::{
    traits::cs::ConstraintSystem,
    Variable
};
use boojum::gadgets::{
    queue::*,
    traits::{allocatable::*, selectable::Selectable, encodable::CircuitVarLengthEncodable, witnessable::WitnessHookable},
    boolean::Boolean
};
use boojum::gadgets::num::Num;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use derivative::*;
use boojum::serde_utils::BigArraySerde;
use crate::base_structures::decommit_query::{DecommitQueryWitness, DECOMMIT_QUERY_PACKED_WIDTH};
use crate::sort_decommittment_requests::*;
pub const DEFAULT_NUM_CHUNKS: usize = 2;
#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct CodeDecommittmentsDeduplicatorFSMInputOutput<F: SmallField> {
    pub initial_log_queue_state:  QueueState<F, QUEUE_STATE_WIDTH>,
    pub sorted_queue_state:  QueueState<F, QUEUE_STATE_WIDTH>,
    pub final_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,

    pub lhs_accumulator: [Num<F>; DEFAULT_NUM_CHUNKS],
    pub rhs_accumulator: [Num<F>; DEFAULT_NUM_CHUNKS],

    pub previous_packed_key: [Num<F>; 5],
    pub previous_item_is_trivial: Boolean<F>,
    pub first_encountered_timestamp: UInt32<F>,
    pub previous_record_encoding: [Num<F>; DECOMMIT_QUERY_PACKED_WIDTH],
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommittmentsDeduplicatorFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            initial_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            final_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),

            lhs_accumulator: [Num::zero(cs); DEFAULT_NUM_CHUNKS],
            rhs_accumulator: [Num::zero(cs); DEFAULT_NUM_CHUNKS],

            previous_packed_key: [Num::zero(cs); 5],
            previous_item_is_trivial: Boolean::allocated_constant(cs, true),
            first_encountered_timestamp: UInt32::placeholder(cs),
            previous_record_encoding: [Num::zero(cs); DECOMMIT_QUERY_PACKED_WIDTH],
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct CodeDecommittmentsDeduplicatorInputData<F: SmallField> {
    pub initial_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub sorted_queue_initial_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommittmentsDeduplicatorInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            initial_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            sorted_queue_initial_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct CodeDecommittmentsDeduplicatorOutputData<F: SmallField> {
    pub final_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommittmentsDeduplicatorOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            final_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type CodeDecommittmentsDeduplicatorInputOutput<F> = crate::fsm_input_output::ClosedFormInput<
    F,
    CodeDecommittmentsDeduplicatorFSMInputOutput<F>,
    CodeDecommittmentsDeduplicatorInputData<F>,
    CodeDecommittmentsDeduplicatorOutputData<F>,
>;
pub type CodeDecommittmentsDeduplicatorInputOutputWitness<F> =
    crate::fsm_input_output::ClosedFormInputWitness<
        F,
        CodeDecommittmentsDeduplicatorFSMInputOutput<F>,
        CodeDecommittmentsDeduplicatorInputData<F>,
        CodeDecommittmentsDeduplicatorOutputData<F>,
    >;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct CodeDecommittmentsDeduplicatorInstanceWitness<F: SmallField> {
    pub closed_form_input: CodeDecommittmentsDeduplicatorInputOutputWitness<F>,

    pub initial_queue_witness: CircuitQueueRawWitness<F, DecommitQuery<F>, 4, DECOMMIT_QUERY_PACKED_WIDTH>,

    pub sorted_queue_witness:  CircuitQueueRawWitness<F, DecommitQuery<F>, 4, DECOMMIT_QUERY_PACKED_WIDTH>,
    pub previous_record_witness: DecommitQueryWitness<F>,
}
