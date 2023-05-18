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
use boojum::cs::traits::circuit::{Circuit, ErasedBuilderForRecursiveVerifier};

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
pub struct LeafLayerRecursionConfig<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> {
    pub proof_config: ProofConfig,
    pub vk_fixed_parameters: VerificationKeyCircuitGeometry,
    pub capacity: usize,
    pub padding_proof: Proof<F, H, EXT>
}

pub fn leaf_layer_recursion_entry_point<
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
    witness: RecursionLeafInstanceWitness<F, H, EXT>,
    round_function: &R,
    config: LeafLayerRecursionConfig<F, H::NonCircuitSimulator, EXT>,
    verifier_builder: Box<dyn ErasedBuilderForRecursiveVerifier<F, EXT, CS>>,
    transcript_params: TR::TransciptParameters,
)
where 
    [(); <RecursionQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let RecursionLeafInstanceWitness { 
        input, 
        vk_witness,
        queue_witness,
        proof_witnesses,
    } = witness;

    let input = RecursionLeafInput::allocate(cs, input);
    let RecursionLeafInput {
        params,
        queue_state,
    } = input;
    let mut queue = 
        RecursionQueue::<F, R>::from_state(cs, queue_state);

    let RecursionLeafParameters { circuit_type, vk_commitment } = params;

    queue.witness = Arc::new(
        FullStateCircuitQueueWitness::from_inner_witness(queue_witness)
    );

    let vk = AllocatedVerificationKey::<F, H>::allocate(cs, vk_witness);
    let vk_commitment_computed: [_; VK_COMMITMENT_LENGTH] = commit_variable_length_encodable_item(cs, &vk, round_function);

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

    let queue_is_empty = queue.is_empty(cs);
    let boolean_true = Boolean::allocated_constant(cs, true);
    Boolean::enforce_equal(cs, &queue_is_empty, &boolean_true);

    let input_commitment: [_; INPUT_OUTPUT_COMMITMENT_LENGTH] = commit_variable_length_encodable_item(cs, &input, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }
}