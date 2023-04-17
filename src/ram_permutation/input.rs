use cs_derive::*;
use boojum::field::SmallField;
use boojum::cs::{
    traits::cs::ConstraintSystem,
    Variable
};
use crate::base_structures::{vm_state::*,
    memory_query::{MemoryQuery, MEMORY_QUERY_PACKED_WIDTH},
};
use boojum::gadgets::{
    queue::*,
    queue::full_state_queue::*,
    traits::{allocatable::*, selectable::Selectable, encodable::CircuitVarLengthEncodable, witnessable::WitnessHookable},
    boolean::Boolean,
    num::Num,
    u32::UInt32,
    u256::UInt256,
    poseidon::CircuitRoundFunction,
};
use derivative::*;
use boojum::serde_utils::BigArraySerde;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct RamPermutationInputData<F: SmallField> {
    pub unsorted_queue_initial_state: QueueTailState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub sorted_queue_initial_state: QueueTailState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub non_deterministic_bootloader_memory_snapshot_length: UInt32<F>,
}

impl<F: SmallField> CSPlaceholder<F> for RamPermutationInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_u32 = UInt32::zero(cs);
        let empty_tail = QueueTailState::placeholder(cs);

        Self {
            unsorted_queue_initial_state: empty_tail,
            sorted_queue_initial_state: empty_tail,
            non_deterministic_bootloader_memory_snapshot_length: zero_u32
        }
    }
}

pub const NUM_PERMUTATION_ARGUMENT_CHALLENGES: usize = 4;
pub const RAM_SORTING_KEY_LENGTH: usize = 3;
pub const RAM_FULL_KEY_LENGTH: usize = 2;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct RamPermutationFSMInputOutput<F: SmallField> {
    pub lhs_accumulator: [Num<F>; NUM_PERMUTATION_ARGUMENT_CHALLENGES],
    pub rhs_accumulator: [Num<F>; NUM_PERMUTATION_ARGUMENT_CHALLENGES],
    pub current_unsorted_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub current_sorted_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub previous_sorting_key: [UInt32<F>; RAM_SORTING_KEY_LENGTH],
    pub previous_full_key: [UInt32<F>; RAM_FULL_KEY_LENGTH],
    pub previous_value: UInt256<F>,
    pub previous_is_ptr: Boolean<F>,
    pub num_nondeterministic_writes: UInt32<F>,
}

impl<F: SmallField> CSPlaceholder<F> for RamPermutationFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_num = Num::zero(cs);
        let zero_u32 = UInt32::zero(cs);
        let zero_u256 = UInt256::zero(cs);
        let boolean_false = Boolean::allocated_constant(cs, false);
        let empty_state = QueueState::placeholder(cs);

        Self {
            lhs_accumulator: [zero_num; NUM_PERMUTATION_ARGUMENT_CHALLENGES],
            rhs_accumulator: [zero_num; NUM_PERMUTATION_ARGUMENT_CHALLENGES],
            current_unsorted_queue_state: empty_state,
            current_sorted_queue_state: empty_state,
            previous_sorting_key: [zero_u32; RAM_SORTING_KEY_LENGTH],
            previous_full_key: [zero_u32; RAM_FULL_KEY_LENGTH],
            previous_value: zero_u256,
            previous_is_ptr: boolean_false,
            num_nondeterministic_writes: zero_u32,
        }
    }
}

pub type RamPermutationCycleInputOutput<F> =
    crate::fsm_input_output::ClosedFormInput<F, RamPermutationFSMInputOutput<F>, RamPermutationInputData<F>, ()>;
pub type RamPermutationCycleInputOutputWitness<F> =
    crate::fsm_input_output::ClosedFormInputWitness<F, RamPermutationFSMInputOutput<F>, RamPermutationInputData<F>, ()>;


pub struct RamPermutationCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: RamPermutationCycleInputOutputWitness<F>,
    // #[serde(bound(
    //     serialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    // ))]
    // #[serde(bound(
    //     deserialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    // ))]
    pub unsorted_queue_witness: MemoryQueriesQueueWitness<F>,
    // #[serde(bound(
    //     serialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::Serialize"
    // ))]
    // #[serde(bound(
    //     deserialize = "<RawMemoryQuery<E> as CSWitnessable<E>>::Witness: serde::de::DeserializeOwned"
    // ))]
    pub sorted_queue_witness: MemoryQueriesQueueWitness<F>,
}

pub type MemoryQueriesQueue<F, R: CircuitRoundFunction<F, 8, 12, 4>> =
    FullStateCircuitQueue<F, MemoryQuery<F>, 8, 12, 4, MEMORY_QUERY_PACKED_WIDTH, R>;
pub type MemoryQueriesQueueWitness<F> =
    FullStateCircuitQueueWitness<F, MemoryQuery<F>, 12, MEMORY_QUERY_PACKED_WIDTH>;

