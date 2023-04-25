use cs_derive::*;
use ethereum_types::U256;
use boojum::field::SmallField;
use boojum::cs::{
    traits::cs::ConstraintSystem,
    Variable
};
use crate::base_structures::{vm_state::*, 
    log_query::{LogQuery,LOG_QUERY_PACKED_WIDTH}, 
};
use boojum::gadgets::{
    queue::*,
    traits::{allocatable::*, selectable::Selectable, encodable::CircuitVarLengthEncodable, witnessable::WitnessHookable},
    boolean::Boolean,
    num::Num,
    u16::UInt16,
    u32::UInt32,
    u256::UInt256,
};
use boojum::serde_utils::BigArraySerde;
use derivative::*;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct CodeDecommittmentFSM<F: SmallField> {
    pub sha256_inner_state: [UInt32<F>; 8], // 8 uint32 words of internal sha256 state
    // CHECK!!! \/
    pub hash_to_compare_against: UInt256<F>, // [Num<F>; 2], // endianess has been taken care of
    pub current_index: UInt32<F>,
    pub current_page: UInt32<F>,
    pub timestamp: UInt32<F>,
    pub num_rounds_left: UInt16<F>,
    pub length_in_bits: UInt32<F>,
    pub state_get_from_queue: Boolean<F>,
    pub state_decommit: Boolean<F>,
    pub finished: Boolean<F>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommittmentFSM<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let bool_false = Boolean::allocated_constant(cs, false);
        let zero_uint16 = UInt16::zero(cs);
        let zero_uint32 = UInt32::zero(cs);
        let zero_uint256 = UInt256::zero(cs);

        Self {
            sha256_inner_state: [zero_uint32; 8],
            hash_to_compare_against: zero_uint256,
            current_index: zero_uint32,
            current_page: zero_uint32,
            timestamp: zero_uint32,
            num_rounds_left: zero_uint16,
            length_in_bits: zero_uint32,
            state_get_from_queue: bool_false,
            state_decommit: bool_false,
            finished: bool_false,
        }
    }
}


#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct CodeDecommitterFSMInputOutput<F: SmallField> {
    pub internal_fsm: CodeDecommittmentFSM<F>,
    pub decommittment_requests_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub memory_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommitterFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            internal_fsm: CodeDecommittmentFSM::<F>::placeholder(cs),
            decommittment_requests_queue_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
            memory_queue_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct CodeDecommitterInputData<F: SmallField> {
    pub memory_queue_initial_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub sorted_requests_queue_initial_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommitterInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            memory_queue_initial_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
            sorted_requests_queue_initial_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct CodeDecommitterOutputData<F: SmallField> {
    pub memory_queue_final_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for CodeDecommitterOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            memory_queue_final_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type CodeDecommitterCycleInputOutput<F> = crate::fsm_input_output::ClosedFormInput<
    F,
    CodeDecommitterFSMInputOutput<F>,
    CodeDecommitterInputData<F>,
    CodeDecommitterOutputData<F>,
>;
pub type CodeDecommitterCycleInputOutputWitness<F> = crate::fsm_input_output::ClosedFormInputWitness<
    F,
    CodeDecommitterFSMInputOutput<F>,
    CodeDecommitterInputData<F>,
    CodeDecommitterOutputData<F>,
>;

use crate::code_unpacker_sha256::DecommitQueueWitness;
pub struct CodeDecommitterCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: CodeDecommitterCycleInputOutputWitness<F>,

    pub sorted_requests_queue_witness:
        DecommitQueueWitness<F, 12>,
    pub code_words: Vec<Vec<U256>>,
}