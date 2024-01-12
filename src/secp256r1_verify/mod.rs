use super::*;
use crate::base_structures::log_query::*;
use crate::base_structures::memory_query::*;

use crate::ethereum_types::U256;

use crate::fsm_input_output::*;

use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;

use boojum::gadgets::non_native_field::implementations::*;

use boojum::gadgets::queue::QueueState;

use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;

use cs_derive::*;

pub mod input;
pub use self::input::*;

pub mod secp256r1;

pub const MEMORY_QUERIES_PER_CALL: usize = 5;

// use crate::ecrecover::naf_abs_div2_table::*;
// use crate::ecrecover::decomp_table::*;

pub mod baseline;
// pub mod new_optimized;

// characteristics of the base field for secp curve
use self::secp256r1::fq::Fq as Secp256Fq;
// order of group of points for secp curve
use self::secp256r1::fr::Fr as Secp256Fr;
// some affine point
use self::secp256r1::PointAffine as Secp256Affine;

type Secp256BaseNNFieldParams = NonNativeFieldOverU16Params<Secp256Fq, 17>;
type Secp256ScalarNNFieldParams = NonNativeFieldOverU16Params<Secp256Fr, 17>;

type Secp256BaseNNField<F> = NonNativeFieldOverU16<F, Secp256Fq, 17>;
type Secp256ScalarNNField<F> = NonNativeFieldOverU16<F, Secp256Fr, 17>;

fn secp256r1_base_field_params() -> Secp256BaseNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

fn secp256r1_scalar_field_params() -> Secp256ScalarNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

// re-exports for integration
pub use self::baseline::{
    secp256r1_verify_function_entry_point, Secp256r1VerifyPrecompileCallParams,
};