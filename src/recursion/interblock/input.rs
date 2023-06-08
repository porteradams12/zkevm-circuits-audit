use super::*;

use std::collections::VecDeque;
use boojum::cs::implementations::proof::Proof;
use boojum::field::SmallField;
use boojum::gadgets::num::Num;
use boojum::gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher;
use boojum::field::FieldExtension;
use boojum::gadgets::traits::allocatable::CSAllocatable;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default(bound = ""))]
#[serde(
    bound = "<H::CircuitOutput as CSAllocatable<F>>::Witness: serde::Serialize + serde::de::DeserializeOwned")]
pub struct InterblockRecursionCircuitInstanceWitness<
    F: SmallField,
    H: RecursiveTreeHasher<F, Num<F>>,
    EXT: FieldExtension<2, BaseField = F>,
> {
    #[derivative(Debug = "ignore")]
    pub proof_witnesses: VecDeque<Proof<F, H::NonCircuitSimulator, EXT>>,
}