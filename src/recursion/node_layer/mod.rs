use crate::base_structures::recursion_query::{RecursionQuery, RecursionQueue};
use crate::fsm_input_output::commit_variable_length_encodable_item;
use boojum::cs::implementations::proof::Proof;
use boojum::cs::implementations::prover::ProofConfig;
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
#[derivative(Clone, Debug)]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct NodeLayerRecursionConfig<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> {
    pub proof_config: ProofConfig,
    pub leaf_layer_capacity: usize,
    pub node_layer_capacity: usize,
    pub padding_proof: Proof<F, H, EXT>
}

use boojum::cs::traits::circuit::CircuitParametersForVerifier;


pub fn node_layer_recursion_entry_point<
F: SmallField,
CS: ConstraintSystem<F> + 'static,
R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
C: CircuitParametersForVerifier<F>,
H: RecursiveTreeHasher<F, Num<F>>,
EXT: FieldExtension<2, BaseField = F>,
TR: RecursiveTranscript<F, CompatibleCap = <H::NonCircuitSimulator as TreeHasher<F>>::Output, CircuitReflection = CTR>,
CTR: CircuitTranscript<F, CircuitCompatibleCap = <H as CircuitTreeHasher<F, Num<F>>>::CircuitOutput, TransciptParameters = TR::TransciptParameters>,
POW: RecursivePoWRunner<F>,
>(
    mut cs: &mut CS,
    witness: RecursionNodeInstanceWitness<F, H, EXT>,
    round_function: &R,
    config: NodeLayerRecursionConfig<F, H::NonCircuitSimulator, EXT>,
    circuit_placeholder: C,
    transcript_params: TR::TransciptParameters,
)
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
    let mut queue = 
        RecursionQueue::<F, 8, 12, 4, R>::from_state(cs, queue_state);

    let vk = AllocatedVerificationKey::<F, H>::allocate(cs, vk_witness);
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

    for (a, b) in vk_commitment.iter().zip(vk_commitment_computed.iter()) {
        Num::enforce_equal(cs, a, b);
    }

    let mut proof_witnesses = proof_witnesses;

    let LeafLayerRecursionConfig { 
        proof_config, 
        vk_fixed_parameters,
        capacity, 
        padding_proof 
    } = config;

    use boojum::gadgets::recursion::recursive_verifier_builder::CsRecursiveVerifierBuilder;

    // use this and deal with borrow checker

    let r = cs as *mut CS;
    let tmp_cs = unsafe {&mut *r};

    let builder_impl = CsRecursiveVerifierBuilder::<'_, F, EXT, _>::new_from_parameters(
        tmp_cs, 
        vk_fixed_parameters.parameters, 
        vk_fixed_parameters.lookup_parameters,
    );
    use boojum::cs::cs_builder::new_builder;
    let builder = new_builder::<_, F>(builder_impl);

    let builder = circuit_placeholder.configure_builder(builder);
    let verifier = builder.build(());

    for _ in 0..capacity {
        let witness = proof_witnesses.pop_front().unwrap_or(padding_proof.clone());
        let proof = AllocatedProof::<F, H, EXT>::allocate(cs, witness);

        let queue_is_empty = queue.is_empty(cs);
        let can_pop = queue_is_empty.negated(cs);

        let (recursive_request, _) = queue.pop_front(cs, can_pop);

        // ensure that it's an expected type
        Num::conditionally_enforce_equal(cs, can_pop, &recursive_request.circuit_type, &circuit_type);

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


        // expected proof should be valid
        is_valid.conditionally_enforce_true(cs, can_pop);

        // enforce publici inputs

        for (a, b) in recursive_request.input_commitment.iter().zip(public_inputs.iter()) {
            Num::conditionally_enforce_equal(cs, can_pop, a, b);
        }
    }

    let input_commitment: [_; INPUT_OUTPUT_COMMITMENT_LENGTH] = commit_variable_length_encodable_item(cs, &input, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }
}

pub(crate) fn split_first_n_from_queue_state<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const N: usize,
>(
    cs: &mut CS,
    queue_state: QueueState<F, N>,
    elements_to_split: UInt32<F>,
) -> (
    QueueState<F, N>,
    QueueState<F, N>
) {
    // check length <= elements_to_split
    let (_, uf) = elements_to_split.overflowing_sub(cs, queue_state.tail.length);
    let second_is_trivial = uf.negated(cs);

    todo!()
}