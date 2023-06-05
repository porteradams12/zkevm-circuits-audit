use super::*;

pub mod input;
pub use self::input::*;

pub mod keccak_aggregator;

use boojum::cs::implementations::verifier::VerificationKey;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::num::Num;
use boojum::cs::implementations::prover::ProofConfig;
use boojum::cs::oracle::TreeHasher;
use boojum::field::FieldExtension;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::gadgets::recursion::allocated_vk::AllocatedVerificationKey;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::gadgets::recursion::recursive_tree_hasher::*;
use boojum::gadgets::recursion::recursive_transcript::*;
use boojum::gadgets::recursion::circuit_pow::RecursivePoWRunner;
use boojum::cs::traits::circuit::ErasedBuilderForRecursiveVerifier;
use boojum::config::*;
use boojum::cs::implementations::proof::Proof;
use boojum::gadgets::recursion::allocated_proof::AllocatedProof;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;

// performs recursion between "independent" units for FIXED verification key

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct InterblockRecursionConfig<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> {
    pub proof_config: ProofConfig,
    pub verification_key: VerificationKey<F, H>,
    pub capacity: usize,
    pub padding_proof: Proof<F, H, EXT>,
}

pub trait InputAggregationFunction<F: SmallField> {
    type Params;

    fn new<CS: ConstraintSystem<F>>(cs: &mut CS, params: Self::Params) -> Self;
    fn aggregate_inputs<CS: ConstraintSystem<F>>(&self, cs: &mut CS, inputs: &[Vec<Num<F>>], validity_flags: &[Boolean<F>]) -> Vec<Num<F>>;
}

pub fn interblock_recursion_function<
    F: SmallField,
    CS: ConstraintSystem<F> + 'static,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    H: RecursiveTreeHasher<F, Num<F>>,
    EXT: FieldExtension<2, BaseField = F>,
    TR: RecursiveTranscript<
        F,
        CompatibleCap = <H::NonCircuitSimulator as TreeHasher<F>>::Output,
        CircuitReflection = CTR,
    >,
    CTR: CircuitTranscript<
        F,
        CircuitCompatibleCap = <H as CircuitTreeHasher<F, Num<F>>>::CircuitOutput,
        TransciptParameters = TR::TransciptParameters,
    >,
    POW: RecursivePoWRunner<F>,
    AGG: InputAggregationFunction<F>,
>(
    cs: &mut CS,
    witness: InterblockRecursionCircuitInstanceWitness<F, H, EXT>,
    _round_function: &R,
    config: InterblockRecursionConfig<F, H::NonCircuitSimulator, EXT>,
    verifier_builder: Box<dyn ErasedBuilderForRecursiveVerifier<F, EXT, CS>>,
    transcript_params: TR::TransciptParameters,
    aggregation_params: AGG::Params,
) {
    let InterblockRecursionCircuitInstanceWitness { proof_witnesses } = witness;
    let mut proof_witnesses = proof_witnesses;

    // as usual - create verifier for FIXED VK, verify, aggregate inputs, output inputs

    let InterblockRecursionConfig {
        proof_config,
        verification_key,
        capacity,
        padding_proof,
    } = config;

    // use this and deal with borrow checker

    let r = cs as *mut CS;

    assert_eq!(verification_key.fixed_parameters.parameters, verifier_builder.geometry());

    let fixed_parameters = verification_key.fixed_parameters.clone();

    let verifier = verifier_builder.create_recursive_verifier(cs);

    let cs = unsafe { &mut *r };

    let mut validity_flags = Vec::with_capacity(capacity);
    let mut inputs = Vec::with_capacity(capacity);

    let vk = AllocatedVerificationKey::allocate_constant(cs, verification_key);

    for _ in 0..capacity {
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

        // verify the proof
        let (is_valid, public_inputs) = verifier.verify::<H, TR, CTR, POW>(
            cs,
            transcript_params.clone(),
            &proof,
            &fixed_parameters,
            &proof_config,
            &vk,
        );

        assert_eq!(public_inputs.len(), INPUT_OUTPUT_COMMITMENT_LENGTH);
        assert_eq!(public_inputs.len(), fixed_parameters.num_public_inputs());

        validity_flags.push(is_valid);
        inputs.push(public_inputs);
    }

    // now actually aggregate

    let aggregator = AGG::new(cs, aggregation_params);
    let aggregated_input = aggregator.aggregate_inputs(
        cs,
        &inputs,
        &validity_flags,
    );

    assert_eq!(aggregated_input.len(), INPUT_OUTPUT_COMMITMENT_LENGTH);

    for el in aggregated_input.into_iter() {
        use boojum::cs::gates::PublicInputGate;
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }
}