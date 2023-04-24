use cs_derive::*;

use super::*;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::cs::Variable;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::num::Num;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::allocatable::CSAllocatableExt;
use boojum::gadgets::traits::encodable::CircuitEncodable;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::u32::UInt32;
use boojum::{field::SmallField, gadgets::u256::UInt256};
use boojum::cs::traits::cs::DstBuffer;
use boojum::gadgets::traits::castable::WitnessCastable;
use ethereum_types::U256;

#[derive(Derivative, CSAllocatable, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct DecommitQuery<F: SmallField> {
    pub code_hash: UInt256<F>,
    pub page: UInt32<F>,
    pub is_first: Boolean<F>,
    pub timestamp: UInt32<F>,
}

pub const DECOMMIT_QUERY_PACKED_WIDTH: usize = 8;

impl<F: SmallField> CircuitEncodable<F, DECOMMIT_QUERY_PACKED_WIDTH> for DecommitQuery<F> {
    fn encode<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> [Variable; DECOMMIT_QUERY_PACKED_WIDTH] {
        debug_assert!(F::CAPACITY_BITS >= 56);

        // we assume that page bytes are known, so it'll be nop anyway
        let page_bytes = self.page.decompose_into_bytes(cs);

        let timestamp_bytes = self.timestamp.decompose_into_bytes(cs);

        let v0 = Num::linear_combination(
            cs,
            &[
                (self.code_hash.inner[0].get_variable(), F::ONE),
                (page_bytes[0].get_variable(), F::from_u64_unchecked(1u64 << 32)),
                (page_bytes[1].get_variable(), F::from_u64_unchecked(1u64 << 40)),
                (page_bytes[2].get_variable(), F::from_u64_unchecked(1u64 << 48)),
            ],
        )
        .get_variable();

        let v1 = Num::linear_combination(
            cs,
            &[
                (self.code_hash.inner[1].get_variable(), F::ONE),
                (page_bytes[3].get_variable(), F::from_u64_unchecked(1u64 << 32)),
                (
                    timestamp_bytes[0].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (
                    timestamp_bytes[1].get_variable(),
                    F::from_u64_unchecked(1u64 << 48),
                ),
            ],
        )
        .get_variable();

        let v2 = Num::linear_combination(
            cs,
            &[
                (self.code_hash.inner[2].get_variable(), F::ONE),
                (
                    timestamp_bytes[2].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
                (
                    timestamp_bytes[3].get_variable(),
                    F::from_u64_unchecked(1u64 << 40),
                ),
                (self.is_first.get_variable(), F::from_u64_unchecked(1u64 << 48)),
            ],
        )
        .get_variable();

        let v3 = self.code_hash.inner[3].get_variable();
        let v4 = self.code_hash.inner[4].get_variable();
        let v5 = self.code_hash.inner[5].get_variable();
        let v6 = self.code_hash.inner[6].get_variable();
        let v7 = self.code_hash.inner[7].get_variable();

        [v0, v1, v2, v3, v4, v5, v6, v7]
    }
}

impl<F: SmallField> CSAllocatableExt<F> for DecommitQuery<F> {
    const INTERNAL_STRUCT_LEN: usize = 11;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        let code_hash: U256 = WitnessCastable::cast_from_source(
            [
                values[0],
                values[1],
                values[2],
                values[3],
                values[4],
                values[5],
                values[6],
                values[7],
            ]
        );

        let page: u32 = WitnessCastable::cast_from_source(values[8]);
        let is_first: bool = WitnessCastable::cast_from_source(values[9]);
        let timestamp: u32 = WitnessCastable::cast_from_source(values[10]);

        Self::Witness {
            code_hash,
            page,
            is_first,
            timestamp,
        }
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        [
            self.code_hash.inner[0].get_variable(),
            self.code_hash.inner[1].get_variable(),
            self.code_hash.inner[2].get_variable(),
            self.code_hash.inner[3].get_variable(),
            self.code_hash.inner[4].get_variable(),
            self.code_hash.inner[5].get_variable(),
            self.code_hash.inner[6].get_variable(),
            self.code_hash.inner[7].get_variable(),
            self.page.get_variable(),
            self.is_first.get_variable(),
            self.timestamp.get_variable(),
        ]
    }
    fn set_internal_variables_values(_witness: Self::Witness, _dst: &mut DstBuffer<'_, '_, F>) {
        todo!();
    }
}
