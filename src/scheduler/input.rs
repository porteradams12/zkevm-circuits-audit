use super::*;
use boojum::cs::implementations::proof::Proof;
use boojum::cs::implementations::verifier::VerificationKey;
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::queue::full_state_queue::FullStateCircuitQueueRawWitness;
use boojum::gadgets::{
    boolean::Boolean,
    queue::*,
    traits::{
        allocatable::*, encodable::CircuitVarLengthEncodable, selectable::Selectable,
        witnessable::WitnessHookable,
    },
};
use cs_derive::*;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputDataWitness;
use crate::base_structures::recursion_query::*;
use crate::base_structures::vm_state::*;
use crate::code_unpacker_sha256::input::CodeDecommitterOutputDataWitness;
use crate::demux_log_queue::input::LogDemuxerInputOutputWitness;
use crate::fsm_input_output::circuit_inputs::main_vm::VmOutputDataWitness;
use crate::log_sorter::input::EventsDeduplicatorOutputDataWitness;
use crate::sort_decommittment_requests::input::CodeDecommittmentsDeduplicatorInputOutputWitness;
use crate::storage_application::input::StorageApplicationOutputDataWitness;
use crate::storage_validity_by_grand_product::input::StorageDeduplicatorOutputDataWitness;
use crate::fsm_input_output::ClosedFormInputCompactFormWitness;
use boojum::gadgets::num::Num;
use boojum::gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher;
use std::collections::VecDeque;
use derivative::*;
use boojum::serde_utils::BigArraySerde;
use boojum::field::FieldExtension;
use crate::recursion::*;
use crate::recursion::leaf_layer::input::*;

// #[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
// #[derivative(Clone, Copy, Debug)]
// #[DerivePrettyComparison("true")]
// pub struct RecursionLeafParameters<F: SmallField> {
//     pub circuit_type: Num<F>,
//     pub vk_commitment: [Num<F>; VK_COMMITMENT_LENGTH],
// }

// impl<F: SmallField> CSPlaceholder<F> for RecursionLeafParameters<F> {
//     fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
//         let zero = Num::zero(cs);
//         Self {
//             circuit_type: zero,
//             vk_commitment: [zero; VK_COMMITMENT_LENGTH],
//         }
//     }
// }

// #[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
// #[derivative(Clone, Copy, Debug)]
// #[DerivePrettyComparison("true")]
// pub struct RecursionLeafInput<F: SmallField> {
//     pub params: RecursionLeafParameters<F>,
//     pub queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
// }

// impl<F: SmallField> CSPlaceholder<F> for RecursionLeafInput<F> {
//     fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
//         Self {
//             params: RecursionLeafParameters::placeholder(cs),
//             queue_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
//         }
//     }
// }

// #[derive(Derivative, serde::Serialize, serde::Deserialize)]
// #[derivative(Clone, Debug, Default(bound = "RecursionLeafInputWitness<F>: Default"))]
// #[serde(bound = "<H::CircuitOutput as CSAllocatable<F>>::Witness: serde::Serialize + serde::de::DeserializeOwned")]
// pub struct RecursionLeafInstanceWitness<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>, EXT: FieldExtension<2, BaseField = F>> {
//     pub input: RecursionLeafInputWitness<F>,
//     pub vk_witness: VerificationKey<F, H::NonCircuitSimulator>,
//     pub queue_witness: FullStateCircuitQueueRawWitness<F, RecursionQuery<F>, FULL_SPONGE_QUEUE_STATE_WIDTH, RECURSION_QUERY_PACKED_WIDTH>,
//     pub proof_witnesses: VecDeque<Proof<F, H::NonCircuitSimulator, EXT>>,
// }

// This structure only keeps witness, but there is a lot of in unfortunately
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "<H::CircuitOutput as CSAllocatable<F>>::Witness: serde::Serialize + serde::de::DeserializeOwned,
    [RecursionLeafParametersWitness<F>; NUM_BASE_LAYER_CIRCUITS]: serde::Serialize + serde::de::DeserializeOwned")]
pub struct SchedulerCircuitInstanceWitness<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>, EXT: FieldExtension<2, BaseField = F>> {
    pub prev_block_data: BlockPassthroughDataWitness<F>,
    pub block_meta_parameters: BlockMetaParametersWitness<F>,

    // passthrough outputs for all the circuits that produce such
    pub vm_end_of_execution_observable_output: VmOutputDataWitness<F>,
    pub decommits_sorter_observable_output: CodeDecommittmentsDeduplicatorOutputDataWitness<F>,
    pub code_decommitter_observable_output: CodeDecommitterOutputDataWitness<F>,
    pub log_demuxer_observable_output: LogDemuxerOutputDataWitness<F>,
    pub keccak256_observable_output: PrecompileFunctionOutputDataWitness<F>,
    pub sha256_observable_output: PrecompileFunctionOutputDataWitness<F>,
    pub ecrecover_observable_output: PrecompileFunctionOutputDataWitness<F>,
    // RAM permutation doesn't produce anything
    pub storage_sorter_observable_output: StorageDeduplicatorOutputDataWitness<F>,
    pub storage_application_observable_output: StorageApplicationOutputDataWitness<F>,
    pub events_sorter_observable_output: EventsDeduplicatorOutputDataWitness<F>,
    pub l1messages_sorter_observable_output: EventsDeduplicatorOutputDataWitness<F>,
    // pub l1messages_linear_hasher_observable_output: PubdataHasherOutputDataWitness<E>,

    // very few things that we need to properly produce this block
    pub storage_log_tail: [F; QUEUE_STATE_WIDTH],
    pub per_circuit_closed_form_inputs: VecDeque<ClosedFormInputCompactFormWitness<F>>,

    pub bootloader_heap_memory_state: QueueTailStateWitness<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub ram_sorted_queue_state: QueueTailStateWitness<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
    pub decommits_sorter_intermediate_queue_state: QueueTailStateWitness<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,

    // all multi-circuits responsible for sorting
    pub rollup_storage_sorter_intermediate_queue_state: QueueTailStateWitness<F, QUEUE_STATE_WIDTH>,
    pub events_sorter_intermediate_queue_state: QueueTailStateWitness<F, QUEUE_STATE_WIDTH>,
    pub l1messages_sorter_intermediate_queue_state: QueueTailStateWitness<F, QUEUE_STATE_WIDTH>,

    // extra information about the previous block
    pub previous_block_meta_hash: [u8; 32],
    pub previous_block_aux_hash: [u8; 32],

    // extra information about our recursion tree
    pub recursion_node_verification_key_hash: [u8; 32],
    pub recursion_leaf_verification_key_hash: [u8; 32],
    pub all_different_circuits_keys_hash: [u8; 32],

    // proofs for every individual circuit type's aggregation subtree
    #[derivative(Debug = "ignore")]
    pub proof_witnesses: VecDeque<Proof<F, H::NonCircuitSimulator, EXT>>,
    #[derivative(Debug = "ignore")]
    pub node_leyer_vk_witness: VerificationKey<F, H::NonCircuitSimulator>,
    #[derivative(Debug = "ignore")]
    pub leaf_layer_parameters: [RecursionLeafParametersWitness<F>; NUM_BASE_LAYER_CIRCUITS],
    #[derivative(Debug = "ignore")]
    pub leaf_layer_parameters_commitment: [F; LEAF_LAYER_PARAMETERS_COMMITMENT_LENGTH],
    #[derivative(Debug = "ignore")]
    pub node_layer_vk_commitment: [F; VK_COMMITMENT_LENGTH],
}