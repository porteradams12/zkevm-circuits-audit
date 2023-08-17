use super::*;
use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::keccak256;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::gadgets::{
    boolean::Boolean,
    queue::*,
    traits::{
        allocatable::*, encodable::CircuitVarLengthEncodable, selectable::Selectable,
        witnessable::WitnessHookable,
    },
};
use boojum::serde_utils::BigArraySerde;
use cs_derive::*;
use derivative::*;
use std::collections::VecDeque;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EIP4844InputData<F: SmallField> {
    pub hash: [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE],
    pub kzg_commitment_x: [UInt8<F>; NUM_WORDS_FQ],
    pub kzg_commitment_y: [UInt8<F>; NUM_WORDS_FQ],
    pub queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for EIP4844InputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            hash: [UInt8::<F>::placeholder(cs); keccak256::KECCAK256_DIGEST_SIZE],
            kzg_commitment_x: [UInt8::<F>::placeholder(cs); NUM_WORDS_FQ],
            kzg_commitment_y: [UInt8::<F>::placeholder(cs); NUM_WORDS_FQ],
            queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EIP4844OutputData<F: SmallField> {
    pub z: [UInt16<F>; NUM_WORDS_FR],
    pub y: [UInt16<F>; NUM_WORDS_FR],
}

impl<F: SmallField> CSPlaceholder<F> for EIP4844OutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            z: [UInt16::<F>::allocate_constant(cs, 0); NUM_WORDS_FR],
            y: [UInt16::<F>::allocate_constant(cs, 0); NUM_WORDS_FR],
        }
    }
}

pub type EIP4844InputOutput<F> =
    crate::fsm_input_output::ClosedFormInput<F, (), EIP4844InputData<F>, EIP4844OutputData<F>>;

pub type EIP4844InputOutputWitness<F> = crate::fsm_input_output::ClosedFormInputWitness<
    F,
    (),
    EIP4844InputData<F>,
    EIP4844OutputData<F>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct EIP4844CircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: EIP4844InputOutputWitness<F>,
    // #[serde(bound(
    //     serialize = "CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>: serde::Serialize"
    // ))]
    // #[serde(bound(
    //     deserialize = "CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>: serde::de::DeserializeOwned"
    // ))]
    pub queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
}
