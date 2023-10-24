use super::*;
use crate::base_structures::vm_state::*;
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::keccak256;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::gadgets::u256::recompose_u256_as_u32x8;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::gadgets::{
    boolean::Boolean,
    queue::*,
    traits::{
        allocatable::*,
        encodable::{CircuitEncodable, CircuitEncodableExt, CircuitVarLengthEncodable},
        selectable::Selectable,
        witnessable::WitnessHookable,
    },
};
use boojum::serde_utils::BigArraySerde;
use cs_derive::*;
use derivative::*;

#[derive(Derivative, CSAllocatable, CSSelectable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct BlobChunk<F: SmallField> {
    pub el: [UInt8<F>; 31],
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EIP4844OutputData<F: SmallField> {
    pub output_hash: [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE],
}

impl<F: SmallField> CSPlaceholder<F> for EIP4844OutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            output_hash: [UInt8::<F>::allocate_constant(cs, 0); keccak256::KECCAK256_DIGEST_SIZE],
        }
    }
}

pub type EIP4844InputOutput<F> =
    crate::fsm_input_output::ClosedFormInput<F, (), (), EIP4844OutputData<F>>;

pub type EIP4844InputOutputWitness<F> =
    crate::fsm_input_output::ClosedFormInputWitness<F, (), (), EIP4844OutputData<F>>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct EIP4844CircuitInstanceWitness<F: SmallField> {
    pub versioned_hash: [u8; 32],
    pub linear_hash_output: [u8; 32],
    pub data_chunks: Vec<BlobChunkWitness<F>>,
}
