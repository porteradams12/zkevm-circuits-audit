use cs_derive::*;
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
    boolean::Boolean
};
use derivative::*;

// FSM

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
    WitnessHookable,
)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorFSMInputOutput<F: SmallField> {
    pub lhs_accumulator: Num<E>,
    pub rhs_accumulator: Num<E>,
    pub current_unsorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub current_intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub current_final_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub cycle_idx: UInt32<E>,
    pub previous_packed_key: [Num<E>; 2],
    pub previous_key: UInt256<E>,
    pub previous_address: UInt160<E>,
    pub previous_timestamp: UInt32<E>,
    pub previous_shard_id: Byte<E>,
    pub this_cell_has_explicit_read_and_rollback_depth_zero: Boolean,
    pub this_cell_base_value: UInt256<E>,
    pub this_cell_current_value: UInt256<E>,
    pub this_cell_current_depth: UInt32<E>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            lhs_accumulator: CircuitEmpty::<E>::empty(),
            rhs_accumulator: CircuitEmpty::<E>::empty(),
            current_unsorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            current_intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            current_final_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            cycle_idx: CircuitEmpty::<E>::empty(),
            previous_packed_key: [Num::zero(); 2],
            previous_key: UInt256::<E>::zero(),
            previous_address: CircuitEmpty::<E>::empty(),
            previous_timestamp: CircuitEmpty::<E>::empty(),
            previous_shard_id: Byte::zero(),
            this_cell_has_explicit_read_and_rollback_depth_zero: CircuitEmpty::<E>::empty(),
            this_cell_base_value: UInt256::<E>::zero(),
            this_cell_current_value: UInt256::<E>::zero(),
            this_cell_current_depth: CircuitEmpty::<E>::empty(),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
    WitnessHookable,
)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorInputData<F: SmallField> {
    pub unsorted_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorInputData<F> {
    fn placeholder(cs: &mut CS) -> Self {
        Self {
            unsorted_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(
    Derivative,
    CSAllocatable,
    CSWitnessable,
    CSPackable,
    CSSelectable,
    CSEqual,
    CSEncodable,
    CSDecodable,
    CSVariableLengthEncodable,
    WitnessHookable,
)]
#[derivative(Clone, Debug)]
pub struct StorageDeduplicatorOutputData<F: SmallField> {
    pub final_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for StorageDeduplicatorOutputData<F> {
    fn placeholder(cs: &mut CS) -> Self {
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

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "")]
pub struct StorageDeduplicatorInstanceWitness<F: SmallField> {
    pub closed_form_input: StorageDeduplicatorInputOutputWitness<F>,
    #[serde(bound(
        serialize = "<StorageLogRecord<F> as CSWitnessable<F>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<StorageLogRecord<F> as CSWitnessable<F>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub unsorted_queue_witness: CircuitQueueWitness<F, LogQuery<F>, 5, LOG_QUERY_PACKED_WIDTH>,

    #[serde(bound(
        serialize = "<TimestampedStorageLogRecord<F> as CSWitnessable<F>>::Witness: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<TimestampedStorageLogRecord<F> as CSWitnessable<F>>::Witness: serde::de::DeserializeOwned"
    ))]
    pub intermediate_sorted_queue_witness:
    CircuitQueueWitness<F, LogQuery<F>, 5, LOG_QUERY_PACKED_WIDTH>,
}
