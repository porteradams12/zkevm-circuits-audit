use std::collections::VecDeque;

use super::*;
use boojum::cs::Variable;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::encodable::CircuitVarLengthEncodable;
use crate::base_structures::precompile_input_outputs::*;
use boojum::gadgets::traits::allocatable::CSPlaceholder;
use boojum::gadgets::queue::*;
use crate::base_structures::vm_state::*;
use crate::base_structures::log_query::*;
use boojum::gadgets::traits::auxiliary::PrettyComparison;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EcrecoverCircuitFSMInputOutput<F: SmallField> {
    pub log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub memory_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for EcrecoverCircuitFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        
        Self {
            log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            memory_queue_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

use crate::fsm_input_output::*;

pub type EcrecoverCircuitInputOutput<F> = ClosedFormInput<
    F,
    EcrecoverCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;
pub type EcrecoverCircuitInputOutputWitness<F> = ClosedFormInputWitness<
    F,
    EcrecoverCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;


#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct EcrecoverCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: EcrecoverCircuitInputOutputWitness<F>,
    pub requests_queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
    pub memory_reads_witness: VecDeque<[U256; MEMORY_QUERIES_PER_CALL]>,
}