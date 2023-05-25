use crate::base_structures::recursion_query::{RecursionQuery, RecursionQueue};
use crate::fsm_input_output::commit_variable_length_encodable_item;
use boojum::cs::implementations::proof::Proof;
use boojum::cs::implementations::prover::ProofConfig;
use boojum::gadgets::queue;
use boojum::gadgets::recursion::allocated_proof::AllocatedProof;
use boojum::gadgets::recursion::allocated_vk::AllocatedVerificationKey;
use boojum::gadgets::recursion::recursive_transcript::RecursiveTranscript;
use boojum::gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher;
use boojum::gadgets::traits::witnessable::WitnessHookable;

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};
use ethereum_types::U256;
use boojum::cs::Variable;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::cs::{traits::cs::ConstraintSystem, gates::*};
use boojum::field::SmallField;
use boojum::gadgets::{
    traits::{
        selectable::Selectable, 
        allocatable::CSAllocatableExt, 
        allocatable::CSAllocatable,
        encodable::CircuitEncodableExt
    },
    num::Num,
    boolean::Boolean,
    queue::*
};
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use boojum::gadgets::queue::full_state_queue::FullStateCircuitQueueWitness;
use boojum::config::*;
use boojum::cs::traits::circuit::Circuit;
use boojum::gadgets::u32::UInt32;

use super::*;

pub mod input;

use self::input::*;

use boojum::cs::oracle::TreeHasher;
use boojum::gadgets::recursion::recursive_tree_hasher::CircuitTreeHasher;
use boojum::gadgets::recursion::recursive_transcript::CircuitTranscript;
use boojum::gadgets::recursion::circuit_pow::RecursivePoWRunner;
use boojum::field::FieldExtension;
use boojum::cs::implementations::verifier::VerificationKeyCircuitGeometry;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug(bound = ""))]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct NodeLayerRecursionConfig<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> {
    pub proof_config: ProofConfig,
    pub vk_fixed_parameters: VerificationKeyCircuitGeometry,
    pub leaf_layer_capacity: usize,
    pub node_layer_capacity: usize,
    pub padding_proof: Proof<F, H, EXT>
}

use boojum::cs::traits::circuit::*;

pub fn node_layer_recursion_entry_point<
F: SmallField,
CS: ConstraintSystem<F> + 'static,
R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
H: RecursiveTreeHasher<F, Num<F>>,
EXT: FieldExtension<2, BaseField = F>,
TR: RecursiveTranscript<F, CompatibleCap = <H::NonCircuitSimulator as TreeHasher<F>>::Output, CircuitReflection = CTR>,
CTR: CircuitTranscript<F, CircuitCompatibleCap = <H as CircuitTreeHasher<F, Num<F>>>::CircuitOutput, TransciptParameters = TR::TransciptParameters>,
POW: RecursivePoWRunner<F>,
>(
    cs: &mut CS,
    witness: RecursionNodeInstanceWitness<F, H, EXT>,
    round_function: &R,
    config: NodeLayerRecursionConfig<F, H::NonCircuitSimulator, EXT>,
    verifier_builder: Box<dyn ErasedBuilderForRecursiveVerifier<F, EXT, CS>>,
    transcript_params: TR::TransciptParameters,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where 
    [(); <RecursionQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let RecursionNodeInstanceWitness { 
        input,
        vk_witness,
        split_points,
        proof_witnesses,
    } = witness;

    let input = RecursionNodeInput::allocate(cs, input);
    let RecursionNodeInput {
        branch_circuit_type,
        leaf_layer_parameters,
        node_layer_vk_commitment,
        queue_state,
    } = input;

    let vk = AllocatedVerificationKey::<F, H>::allocate(cs, vk_witness);
    assert_eq!(vk.setup_merkle_tree_cap.len(), config.vk_fixed_parameters.cap_size);
    let vk_commitment_computed: [_; VK_COMMITMENT_LENGTH] = commit_variable_length_encodable_item(cs, &vk, round_function);

    // select VK commitment over which we will work with
    // make unreachable palceholder
    let zero_num = Num::zero(cs);
    let mut vk_commitment = [zero_num; VK_COMMITMENT_LENGTH];

    for el in leaf_layer_parameters.iter() {
        let this_type = Num::equals(cs, &branch_circuit_type, &el.circuit_type);
        vk_commitment = <[Num<F>; VK_COMMITMENT_LENGTH]>::conditionally_select(
            cs, 
            this_type, 
            &el.vk_commitment, 
            &vk_commitment
        );
    }

    // now we need to try to split the circuit

    let NodeLayerRecursionConfig { 
        proof_config, 
        vk_fixed_parameters,
        leaf_layer_capacity,
        node_layer_capacity,
        padding_proof 
    } = config;

    let max_length_if_leafs = leaf_layer_capacity * node_layer_capacity;
    let max_length_if_leafs = UInt32::allocated_constant(cs, max_length_if_leafs as u32);
    // if queue length is <= max_length_if_leafs then next layer we aggregate leafs, or aggregate nodes otherwise
    let (_, uf) = max_length_if_leafs.overflowing_sub(cs, queue_state.tail.length);
    let next_layer_aggregates_nodes = uf;
    vk_commitment = <[Num<F>; VK_COMMITMENT_LENGTH]>::conditionally_select(
        cs, 
        next_layer_aggregates_nodes, 
        &node_layer_vk_commitment, 
        &vk_commitment
    );

    for (a, b) in vk_commitment.iter().zip(vk_commitment_computed.iter()) {
        Num::enforce_equal(cs, a, b);
    }

    // split the original queue into "node_layer_capacity" elements, regardless if next layer
    // down will aggregate leafs or nodes

    let mut proof_witnesses = proof_witnesses;

    // use this and deal with borrow checker

    let r = cs as *mut CS;

    assert_eq!(vk_fixed_parameters.parameters, verifier_builder.geometry());

    let verifier = verifier_builder.create_recursive_verifier(cs);

    // use boojum::gadgets::recursion::recursive_verifier_builder::CsRecursiveVerifierBuilder;
    // let builder_impl = CsRecursiveVerifierBuilder::<'_, F, EXT, _>::new_from_parameters(
    //     cs,
    //     vk_fixed_parameters.parameters, 
    // );
    // use boojum::cs::cs_builder::new_builder;
    // let builder = new_builder::<_, F>(builder_impl);

    // let builder = e.configure_builder(builder);
    // let verifier = builder.build(());

    let cs = unsafe {&mut *r};

    let subqueues = split_queue_state_into_n(
        cs,
        queue_state,
        node_layer_capacity,
        split_points,
    );

    assert_eq!(subqueues.len(), node_layer_capacity);

    for subqueue in subqueues.into_iter() {
        // here we do the trick to protect ourselves from setup pending from witness, but
        // nevertheless do not create new types for proofs with fixed number of inputs, etc
        let witness = if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == false {
            padding_proof.clone()
        } else {
            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
                // proving mode
                proof_witnesses.pop_front().unwrap_or(padding_proof.clone())
            } else {
                // we are in the testing mode
                proof_witnesses.pop_front().unwrap_or(padding_proof.clone())
            }
        };
        let proof = AllocatedProof::<F, H, EXT>::allocate(cs, witness);

        let chunk_is_empty = subqueue.tail.length.is_zero(cs);
        let chunk_is_meaningful = chunk_is_empty.negated(cs);

        // verify the proof
        let (is_valid, public_inputs) = verifier.verify::<
            H,
            TR,
            CTR,
            POW,
        >(
            cs,
            transcript_params.clone(),
            &proof,
            &vk_fixed_parameters,
            &proof_config,
            &vk,
        );

        assert_eq!(public_inputs.len(), INPUT_OUTPUT_COMMITMENT_LENGTH);

        is_valid.conditionally_enforce_true(cs, chunk_is_meaningful);
    }

    let input_commitment: [_; INPUT_OUTPUT_COMMITMENT_LENGTH] = commit_variable_length_encodable_item(cs, &input, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}

pub(crate) fn split_first_n_from_queue_state<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const N: usize,
>(
    cs: &mut CS,
    queue_state: QueueState<F, N>,
    elements_to_split: UInt32<F>,
    split_point_witness: [F; N],
) -> (
    QueueState<F, N>,
    QueueState<F, N>
) {
    // check length <= elements_to_split
    let (second_length, uf) = queue_state.tail.length.overflowing_sub(cs, elements_to_split);
    let second_is_zero = second_length.is_zero(cs);

    let second_is_trivial = Boolean::multi_or(cs, &[second_is_zero, uf]);

    let intermediate = <[Num<F>; N]>::allocate(cs, split_point_witness);
    let intermediate_state = QueueTailState {
        tail: intermediate,
        length: elements_to_split
    };

    let first_tail = QueueTailState::conditionally_select(
        cs,
        uf, 
        &queue_state.tail, 
        &intermediate_state,
    );

    for (a, b) in intermediate.iter().zip(queue_state.tail.tail.iter()) {
        Num::conditionally_enforce_equal(cs, second_is_trivial, a, b);
    }

    let first = QueueState {
        head: queue_state.head,
        tail: first_tail,
    };

    let second_length = second_length.mask_negated(cs, uf);

    let second = QueueState {
        head: intermediate_state.tail,
        tail: QueueTailState { 
            tail: queue_state.tail.tail,
            length: second_length, 
        },
    };

    (first, second)
}

pub(crate) fn split_queue_state_into_n<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const N: usize,
>(
    cs: &mut CS,
    queue_state: QueueState<F, N>,
    split_into: usize,
    mut split_point_witnesses: VecDeque<[F; N]>,
) -> Vec<QueueState<F, N>> {
    assert!(split_into <= u32::MAX as usize);
    assert!(split_into >= 2);
    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        assert_eq!(split_point_witnesses.len() + 1, split_into);
    }
    let (div, rem) = queue_state.tail.length.div_by_constant(cs, split_into as u32);
    let div_plus_one = unsafe { div.increment_unchecked(cs) };
    let rem_is_zero = rem.is_zero(cs);
    let split_size = UInt32::conditionally_select(
        cs, 
        rem_is_zero, 
        &div, 
        &div_plus_one,
    );

    let mut current_state = queue_state;
    let mut result = Vec::with_capacity(split_into);

    for _ in 0..(split_into-1) {
        let witness = split_point_witnesses.pop_front().unwrap_or([F::ZERO; N]);
        let (first, second) = split_first_n_from_queue_state(
            cs,
            current_state,
            split_size,
            witness
        );

        current_state = second;
        result.push(first);
    }
    // push the last one
    result.push(current_state);

    assert_eq!(result.len(), split_into);
    
    result
}