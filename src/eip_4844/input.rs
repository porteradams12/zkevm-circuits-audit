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

#[derive(
    Derivative, CSAllocatable, CSSelectable, WitnessHookable, serde::Serialize, serde::Deserialize,
)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
#[serde(bound = "")]
pub struct BlobChunk<F: SmallField> {
    pub el: [UInt8<F>; 31],
}

impl<F: SmallField> CSAllocatableExt<F> for BlobChunk<F> {
    const INTERNAL_STRUCT_LEN: usize = 31;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        let el: [u8; 31] = [
            WitnessCastable::cast_from_source(values[0]),
            WitnessCastable::cast_from_source(values[1]),
            WitnessCastable::cast_from_source(values[2]),
            WitnessCastable::cast_from_source(values[3]),
            WitnessCastable::cast_from_source(values[4]),
            WitnessCastable::cast_from_source(values[5]),
            WitnessCastable::cast_from_source(values[6]),
            WitnessCastable::cast_from_source(values[7]),
            WitnessCastable::cast_from_source(values[8]),
            WitnessCastable::cast_from_source(values[9]),
            WitnessCastable::cast_from_source(values[10]),
            WitnessCastable::cast_from_source(values[11]),
            WitnessCastable::cast_from_source(values[12]),
            WitnessCastable::cast_from_source(values[13]),
            WitnessCastable::cast_from_source(values[14]),
            WitnessCastable::cast_from_source(values[15]),
            WitnessCastable::cast_from_source(values[16]),
            WitnessCastable::cast_from_source(values[17]),
            WitnessCastable::cast_from_source(values[18]),
            WitnessCastable::cast_from_source(values[19]),
            WitnessCastable::cast_from_source(values[20]),
            WitnessCastable::cast_from_source(values[21]),
            WitnessCastable::cast_from_source(values[22]),
            WitnessCastable::cast_from_source(values[23]),
            WitnessCastable::cast_from_source(values[24]),
            WitnessCastable::cast_from_source(values[25]),
            WitnessCastable::cast_from_source(values[26]),
            WitnessCastable::cast_from_source(values[27]),
            WitnessCastable::cast_from_source(values[28]),
            WitnessCastable::cast_from_source(values[29]),
            WitnessCastable::cast_from_source(values[30]),
        ];

        <BlobChunk<F> as CSAllocatable<F>>::Witness { el }
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            el: [UInt8::allocate_without_value(cs); 31],
        }
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        [
            self.el[0].get_variable(),
            self.el[1].get_variable(),
            self.el[2].get_variable(),
            self.el[3].get_variable(),
            self.el[4].get_variable(),
            self.el[5].get_variable(),
            self.el[6].get_variable(),
            self.el[7].get_variable(),
            self.el[8].get_variable(),
            self.el[9].get_variable(),
            self.el[10].get_variable(),
            self.el[11].get_variable(),
            self.el[12].get_variable(),
            self.el[13].get_variable(),
            self.el[14].get_variable(),
            self.el[15].get_variable(),
            self.el[16].get_variable(),
            self.el[17].get_variable(),
            self.el[18].get_variable(),
            self.el[19].get_variable(),
            self.el[20].get_variable(),
            self.el[21].get_variable(),
            self.el[22].get_variable(),
            self.el[23].get_variable(),
            self.el[24].get_variable(),
            self.el[25].get_variable(),
            self.el[26].get_variable(),
            self.el[27].get_variable(),
            self.el[28].get_variable(),
            self.el[29].get_variable(),
            self.el[30].get_variable(),
        ]
    }

    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        // NOTE: must be same sequence as in `flatten_as_variables`
        UInt8::set_internal_variables_values(witness.el[0], dst);
        UInt8::set_internal_variables_values(witness.el[1], dst);
        UInt8::set_internal_variables_values(witness.el[2], dst);
        UInt8::set_internal_variables_values(witness.el[3], dst);
        UInt8::set_internal_variables_values(witness.el[4], dst);
        UInt8::set_internal_variables_values(witness.el[5], dst);
        UInt8::set_internal_variables_values(witness.el[6], dst);
        UInt8::set_internal_variables_values(witness.el[7], dst);
        UInt8::set_internal_variables_values(witness.el[8], dst);
        UInt8::set_internal_variables_values(witness.el[9], dst);
        UInt8::set_internal_variables_values(witness.el[10], dst);
        UInt8::set_internal_variables_values(witness.el[11], dst);
        UInt8::set_internal_variables_values(witness.el[12], dst);
        UInt8::set_internal_variables_values(witness.el[13], dst);
        UInt8::set_internal_variables_values(witness.el[14], dst);
        UInt8::set_internal_variables_values(witness.el[15], dst);
        UInt8::set_internal_variables_values(witness.el[16], dst);
        UInt8::set_internal_variables_values(witness.el[17], dst);
        UInt8::set_internal_variables_values(witness.el[18], dst);
        UInt8::set_internal_variables_values(witness.el[19], dst);
        UInt8::set_internal_variables_values(witness.el[20], dst);
        UInt8::set_internal_variables_values(witness.el[21], dst);
        UInt8::set_internal_variables_values(witness.el[22], dst);
        UInt8::set_internal_variables_values(witness.el[23], dst);
        UInt8::set_internal_variables_values(witness.el[24], dst);
        UInt8::set_internal_variables_values(witness.el[25], dst);
        UInt8::set_internal_variables_values(witness.el[26], dst);
        UInt8::set_internal_variables_values(witness.el[27], dst);
        UInt8::set_internal_variables_values(witness.el[28], dst);
        UInt8::set_internal_variables_values(witness.el[29], dst);
        UInt8::set_internal_variables_values(witness.el[30], dst);
    }
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
    pub blob_hash: [u8; 32],
    pub blob: VecDeque<BlobChunkWitness<F>>,
}
