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
use std::collections::VecDeque;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct BlobChunk<F: SmallField> {
    pub el: UInt256<F>,
}

impl<F: SmallField> CircuitEncodable<F, 5> for BlobChunk<F> {
    fn encode<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> [Variable; 5] {
        debug_assert!(F::CAPACITY_BITS >= 56);

        let el_bytes = self.el.inner.map(|el| el.decompose_into_bytes(cs));
        let v0 = Num::linear_combination(
            cs,
            &[
                (el_bytes[0][0].get_variable(), F::ONE),
                (
                    el_bytes[0][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    el_bytes[0][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    el_bytes[0][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
                (
                    el_bytes[1][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
                (
                    el_bytes[1][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (
                    el_bytes[1][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 48),
                ),
            ],
        )
        .get_variable();

        let v1 = Num::linear_combination(
            cs,
            &[
                (el_bytes[1][3].get_variable(), F::ONE),
                (
                    el_bytes[2][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    el_bytes[2][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    el_bytes[2][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
                (
                    el_bytes[2][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
                (
                    el_bytes[3][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (
                    el_bytes[3][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 48),
                ),
            ],
        )
        .get_variable();

        let v2 = Num::linear_combination(
            cs,
            &[
                (el_bytes[3][2].get_variable(), F::ONE),
                (
                    el_bytes[3][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    el_bytes[4][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    el_bytes[4][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
                (
                    el_bytes[4][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
                (
                    el_bytes[4][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (
                    el_bytes[5][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 48),
                ),
            ],
        )
        .get_variable();

        let v3 = Num::linear_combination(
            cs,
            &[
                (el_bytes[5][1].get_variable(), F::ONE),
                (
                    el_bytes[5][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    el_bytes[5][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    el_bytes[6][0].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
                (
                    el_bytes[6][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
                (
                    el_bytes[6][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (
                    el_bytes[6][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 48),
                ),
            ],
        )
        .get_variable();

        let v4 = Num::linear_combination(
            cs,
            &[
                (el_bytes[7][0].get_variable(), F::ONE),
                (
                    el_bytes[7][1].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    el_bytes[7][2].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    el_bytes[7][3].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
            ],
        )
        .get_variable();

        [v0, v1, v2, v3, v4]
    }
}

impl<F: SmallField> CircuitEncodableExt<F, 5> for BlobChunk<F> {}

impl<F: SmallField> CSAllocatableExt<F> for BlobChunk<F> {
    const INTERNAL_STRUCT_LEN: usize = 8;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        let el: [u32; 8] = [
            WitnessCastable::cast_from_source(values[0]),
            WitnessCastable::cast_from_source(values[1]),
            WitnessCastable::cast_from_source(values[2]),
            WitnessCastable::cast_from_source(values[3]),
            WitnessCastable::cast_from_source(values[4]),
            WitnessCastable::cast_from_source(values[5]),
            WitnessCastable::cast_from_source(values[6]),
            WitnessCastable::cast_from_source(values[7]),
        ];
        let el = recompose_u256_as_u32x8(el);

        <BlobChunk<F> as CSAllocatable<F>>::Witness { el }
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            el: UInt256::allocate_without_value(cs),
        }
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        [
            self.el.inner[0].get_variable(),
            self.el.inner[1].get_variable(),
            self.el.inner[2].get_variable(),
            self.el.inner[3].get_variable(),
            self.el.inner[4].get_variable(),
            self.el.inner[5].get_variable(),
            self.el.inner[6].get_variable(),
            self.el.inner[7].get_variable(),
        ]
    }

    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        // NOTE: must be same sequence as in `flatten_as_variables`
        UInt256::set_internal_variables_values(witness.el, dst);
    }
}

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
    pub queue_witness: CircuitQueueRawWitness<F, BlobChunk<F>, 4, 5>,
}
