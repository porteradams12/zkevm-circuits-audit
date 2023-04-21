use super::*;

pub mod input;

use crate::fsm_input_output::ClosedFormInputCompactForm;

use crate::base_structures::{
    log_query::{LogQuery, LogQueryWitness, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::{gates::*, traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::{
    boolean::Boolean,
    impls::lc::linear_combination_collapse,
    num::Num,
    poseidon::CircuitRoundFunction,
    queue::*,
    traits::{
        allocatable::*,
        encodable::{CircuitEncodable, CircuitEncodableExt},
        selectable::Selectable,
        witnessable::*,
    },
    u16::UInt16,
    u160::*,
    u256::*,
    u32::UInt32,
    u8::UInt8,
};

use zkevm_opcode_defs::system_params::*;

use crate::{
    demux_log_queue::StorageLogQueue,
    fsm_input_output::{circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH, *},
    storage_validity_by_grand_product::input::*,
};

// we make a generation aware memory that store all the old and new values
// for a current storage cell. There are largely 3 possible sequences that we must be aware of
// - write_0, .. .... without rollback of the current write
// - write_0, ..., rollback_0, read_0, ... - in this case we must issue and explicit read, even though it's not the first one
// - read_0, ..., - same as above

// We use extra structure with timestamping. Even though we DO have
// timestamp field in LogQuery, such timestamp is the SAME
// for "forward" and "rollback" items, while we do need to have them
// on different timestamps

const TIMESTAMPED_STORAGE_LOG_ENCODING_LEN: usize = 20;

use cs_derive::*;

#[derive(Derivative, CSAllocatable)]
#[derivative(Clone, Debug)]
pub struct TimestampedStorageLogRecord<F: SmallField> {
    pub record: LogQuery<F>,
    pub timestamp: UInt32<F>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq(bound = ""))]
#[serde(bound = "")]
pub struct TimestampedStorageLogRecordWitness<F: SmallField> {
    pub timestamp: u32,
    pub record: LogQueryWitness<F>,
}

pub const EXTENDED_TIMESTAMP_ENCODING_ELEMENT: usize = 19;
pub const EXTENDED_TIMESTAMP_ENCODING_OFFSET: usize = 8;

impl<F: SmallField> TimestampedStorageLogRecord<F> {
    pub fn append_timestamp_to_raw_query_encoding<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        original_encoding: &[Variable; 20],
        timestamp: &UInt32<F>,
    ) -> [Variable; 20] {
        let encoding = Num::linear_combination(
            cs,
            &[
                (
                    &original_encoding[EXTENDED_TIMESTAMP_ENCODING_ELEMENT],
                    F::one(),
                ),
                (&timestamp.inner[0], F::from_u64_unchecked(1u64 << 8)),
                (&timestamp.inner[1], F::from_u64_unchecked(1u64 << 16)),
                (&timestamp.inner[2], F::from_u64_unchecked(1u64 << 24)),
                (&timestamp.inner[3], F::from_u64_unchecked(1u64 << 32)),
            ],
        )
        .get_variable();

        let mut result = *original_encoding;
        result[EXTENDED_TIMESTAMP_ENCODING_ELEMENT] = encoding;
        Ok(result)
    }
}

impl<F: SmallField> TimestampedStorageLogRecord<F> {
    pub fn pack<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> [Num<F>; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN] {
        let original_encoding = self.record.pack(cs)?;

        Self::append_timestamp_to_raw_query_encoding(cs, &original_encoding, &self.timestamp)
    }
}

impl<F: SmallField> CircuitEncodable<F, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<F>
{
    fn encode<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> [Num<F>; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN] {
        let packed = self.pack(cs)?;

        Ok(packed)
    }
}

impl<F: SmallField> CircuitEncodableExt<F, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<F>
{
}

pub fn sort_and_deduplicate_storage_access_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 2, 3, 4>,
>(
    cs: &mut CS,
    closed_form_input: Option<StorageDeduplicatorInstanceWitness<F>>,
    round_function: &R,
    limit: usize,
) -> Num<F> {
    // let columns3 = vec![
    //     PolyIdentifier::VariablesPolynomial(0),
    //     PolyIdentifier::VariablesPolynomial(1),
    //     PolyIdentifier::VariablesPolynomial(2),
    // ];

    // if cs.get_table(VM_BITWISE_LOGICAL_OPS_TABLE_NAME).is_err() {
    //     let name = VM_BITWISE_LOGICAL_OPS_TABLE_NAME;
    //     let bitwise_logic_table = LookupTableApplication::new(
    //         name,
    //         BitwiseLogicTable::new(&name, 8),
    //         columns3.clone(),
    //         None,
    //         true,
    //     );
    //     cs.add_table(bitwise_logic_table)?;
    // };

    // inscribe_default_range_table_for_bit_width_over_first_three_columns(cs, 16)?;

    let structured_input_witness = closed_form_input.closed_form_input;
    let unsorted_queue_witness = closed_form_input.unsorted_queue_witness;
    let intermediate_sorted_queue_witness = closed_form_input.intermediate_sorted_queue_witness;

    let mut structured_input = StorageDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    )?;

    let unsorted_queue_from_passthrough = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .head_state,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .tail_state,
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .num_items,
    )?;

    let unsorted_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .num_items,
    )?;

    // passthrought must be trivial
    unsorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let mut unsorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &unsorted_queue_from_passthrough,
        &unsorted_queue_from_fsm_input,
    )?;

    if let Some(wit) = unsorted_queue_witness {
        unsorted_queue.witness = wit;
    }

    // same logic from sorted
    let intermediate_sorted_queue_from_passthrough = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        2,
        3,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .head_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .num_items,
    )?;

    let intermediate_sorted_queue_from_fsm_input = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        2,
        3,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .num_items,
    )?;

    // passthrought must be trivial
    intermediate_sorted_queue_from_passthrough
        .head_state
        .enforce_equal(cs, &Num::zero())?;

    let mut intermediate_sorted_queue = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        2,
        3,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::conditionally_select(
        cs,
        &structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough,
        &intermediate_sorted_queue_from_fsm_input,
    )?;

    if let Some(wit) = intermediate_sorted_queue_witness {
        intermediate_sorted_queue.witness = wit;
    }

    // for final sorted queue it's easier

    let empty_final_sorted_queue = StorageLogQueue::<F, R>::empty();
    let final_sorted_queue_from_fsm_input = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .head_state,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .tail_state,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .num_items,
    )?;

    let mut final_sorted_queue = StorageLogQueue::conditionally_select(
        cs,
        &structured_input.start_flag,
        &empty_final_sorted_queue,
        &final_sorted_queue_from_fsm_input,
    )?;

    // we can always ensure this
    unsorted_queue
        .len()
        .inner
        .enforce_equal(cs, &intermediate_sorted_queue.len().inner)?;

    // get challenges for permutation argument

    let mut fs_input = vec![];
    fs_input.push(unsorted_queue_from_passthrough.get_tail_state());
    fs_input.push(unsorted_queue_from_passthrough.len().inner);
    fs_input.push(intermediate_sorted_queue_from_passthrough.get_tail_state());
    fs_input.push(intermediate_sorted_queue_from_passthrough.len().inner);

    // this is a permutation proof through the grand product
    let mut sponge_state = variable_length_absorb_into_empty_state(cs, &fs_input, round_function)?;

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..NUM_PERMUTATION_ARG_CHALLENGES {
        if taken == 2 {
            // run round
            sponge_state = round_function.round_function(cs, sponge_state)?;
            taken = 0;
        }

        let challenge = sponge_state[taken];
        fs_challenges.push(challenge);

        taken += 1;
    }

    let fs_challenges: [Num<F>; NUM_PERMUTATION_ARG_CHALLENGES] = fs_challenges.try_into().unwrap();

    let initial_lhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(F::one()),
        &structured_input.hidden_fsm_input.lhs_accumulator,
    )?;

    let initial_rhs = Num::conditionally_select(
        cs,
        &structured_input.start_flag,
        &Num::Constant(F::one()),
        &structured_input.hidden_fsm_input.rhs_accumulator,
    )?;

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let previous_packed_key = <[Num<F>; 2]>::conditionally_select(
        cs,
        &structured_input.start_flag,
        &[Num::zero(); 2],
        &structured_input.hidden_fsm_input.previous_packed_key,
    )?;

    let cycle_idx = UInt32::conditionally_select(
        cs,
        &structured_input.start_flag,
        &UInt32::zero(),
        &structured_input.hidden_fsm_input.cycle_idx,
    )?;

    let (
        new_lhs,
        new_rhs,
        cycle_idx,
        previous_packed_key,
        previous_key,
        previous_address,
        previous_timestamp,
        this_cell_has_explicit_read_and_rollback_depth_zero,
        this_cell_base_value,
        this_cell_current_value,
        this_cell_current_depth,
        previous_shard_id,
    ) = sort_and_deduplicate_storage_access_inner(
        cs,
        initial_lhs,
        initial_rhs,
        &mut unsorted_queue,
        &mut intermediate_sorted_queue,
        &mut final_sorted_queue,
        structured_input.start_flag,
        cycle_idx,
        fs_challenges,
        previous_packed_key,
        structured_input.hidden_fsm_input.previous_key,
        structured_input.hidden_fsm_input.previous_address,
        structured_input.hidden_fsm_input.previous_timestamp,
        structured_input
            .hidden_fsm_input
            .this_cell_has_explicit_read_and_rollback_depth_zero,
        structured_input.hidden_fsm_input.this_cell_base_value,
        structured_input.hidden_fsm_input.this_cell_current_value,
        structured_input.hidden_fsm_input.this_cell_current_depth,
        structured_input.hidden_fsm_input.previous_shard_id,
        round_function,
        limit,
    )?;

    let unsorted_is_empty = unsorted_queue.is_empty(cs)?;
    let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty)?;

    let completed = unsorted_is_empty.and(cs, sorted_is_empty)?;
    Num::conditionally_enforce_equal(cs, &completed, &new_lhs, &new_rhs)?;

    // form the input/output

    structured_input.hidden_fsm_output.cycle_idx = cycle_idx;
    structured_input.hidden_fsm_output.previous_packed_key = previous_packed_key;
    structured_input.hidden_fsm_output.previous_key = previous_key;
    structured_input.hidden_fsm_output.previous_address = previous_address;
    structured_input.hidden_fsm_output.previous_timestamp = previous_timestamp;
    structured_input
        .hidden_fsm_output
        .this_cell_has_explicit_read_and_rollback_depth_zero =
        this_cell_has_explicit_read_and_rollback_depth_zero;
    structured_input.hidden_fsm_output.this_cell_base_value = this_cell_base_value;
    structured_input.hidden_fsm_output.this_cell_current_value = this_cell_current_value;
    structured_input.hidden_fsm_output.this_cell_current_depth = this_cell_current_depth;
    structured_input.hidden_fsm_output.previous_shard_id = previous_shard_id;

    structured_input.hidden_fsm_output.lhs_accumulator = new_lhs;
    structured_input.hidden_fsm_output.rhs_accumulator = new_rhs;

    structured_input
        .hidden_fsm_output
        .current_unsorted_queue_state = unsorted_queue.into_state();
    structured_input
        .hidden_fsm_output
        .current_intermediate_sorted_queue_state = intermediate_sorted_queue.into_state();

    structured_input.completion_flag = completed;

    let final_queue_for_observable_output = CircuitQueue::conditionally_select(
        cs,
        &completed,
        &final_sorted_queue,
        &CircuitQueue::empty(),
    )?;

    structured_input.observable_output.final_sorted_queue_state =
        final_queue_for_observable_output.into_state();

    structured_input
        .hidden_fsm_output
        .current_final_sorted_queue_state = final_sorted_queue.into_state();

    if let Some(circuit_result) = structured_input.create_witness() {
        if let Some(passed_input) = structured_input_witness {
            assert_eq!(circuit_result, passed_input);
        }
    }

    use crate::fsm_input_output::ClosedFormInputCompactForm;
    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function)?;

    // dbg!(compact_form.create_witness());
    let input_committment = commit_encodable_item(cs, &compact_form, round_function)?;
    let input_committment_value = input_committment.get_value();
    let public_input = Num::<F>::alloc_input(cs, || Ok(input_committment_value.grab()?))?;
    public_input.enforce_equal(cs, &input_committment.get_variable())?;

    Ok(public_input)
}

const NUM_PERMUTATION_ARG_CHALLENGES: usize = TIMESTAMPED_STORAGE_LOG_ENCODING_LEN + 1;

pub fn sort_and_deduplicate_storage_access_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 2, 3, 4>,
>(
    cs: &mut CS,
    mut lhs: Num<F>,
    mut rhs: Num<F>,
    original_queue: &mut StorageLogQueue<F, R>,
    intermediate_sorted_queue: &mut CircuitQueue<
        F,
        TimestampedStorageLogRecord<F>,
        2,
        3,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >,
    sorted_queue: &mut StorageLogQueue<F, R>,
    is_start: Boolean<F>,
    mut cycle_idx: UInt32<F>,
    fs_challenges: [Num<F>; NUM_PERMUTATION_ARG_CHALLENGES],
    mut previous_packed_key: [Num<F>; 2],
    mut previous_key: UInt256<F>,
    mut previous_address: UInt160<F>,
    mut previous_timestamp: UInt32<F>,
    mut this_cell_has_explicit_read_and_rollback_depth_zero: Boolean<F>,
    mut this_cell_base_value: UInt256<F>,
    mut this_cell_current_value: UInt256<F>,
    mut this_cell_current_depth: UInt32<F>,
    mut previous_shard_id: UInt8<F>,
    round_function: &R,
    limit: usize,
) -> (
    Num<F>,
    Num<F>,
    UInt32<F>,
    [Num<F>; 2],
    UInt256<F>,
    UInt160<F>,
    UInt32<F>,
    Boolean<F>,
    UInt256<F>,
    UInt256<F>,
    UInt32<F>,
    UInt8<F>,
) {
    assert!(limit <= u32::MAX as usize);

    // we can recreate it here, there are two cases:
    // - we are 100% empty, but it's the only circuit in this case
    // - otherwise we continue, and then it's not trivial
    let no_work = original_queue.is_empty(cs);
    let mut previous_item_is_trivial = no_work.or(cs, is_start);

    let additive_part = *fs_challenges.last().unwrap();

    // we simultaneously pop, accumulate partial product,
    // and decide whether or not we should move to the next cell

    // to ensure uniqueness we place timestamps in a addition to the

    const PACKED_WIDTHS: [usize; 2] = [192, 232];

    for _cycle in 0..limit {
        let original_timestamp = cycle_idx;
        // increment it immediatelly
        let new_cycle_idx = cycle_idx.increment_unchecked(cs)?;
        cycle_idx = new_cycle_idx;

        let original_is_empty = original_queue.is_empty(cs)?;
        let sorted_is_empty = intermediate_sorted_queue.is_empty(cs)?;
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty)?;

        let should_pop = original_is_empty.not();
        let item_is_trivial = original_is_empty;

        let original_encoding = original_queue.pop_first_encoding_only::<_, _, 2, 3>(
            cs,
            &should_pop,
            round_function,
        )?;
        let (sorted_item, sorted_encoding) = intermediate_sorted_queue
            .pop_first_and_return_encoding(cs, &should_pop, round_function)?;
        let extended_original_encoding =
            TimestampedStorageLogRecord::append_timestamp_to_raw_query_encoding(
                cs,
                &original_encoding,
                &original_timestamp,
            )?;

        assert_eq!(extended_original_encoding.len(), sorted_encoding.len());
        assert_eq!(extended_original_encoding.len(), fs_challenges.len() - 1);

        // accumulate into product

        let mut lhs_lc = Vec::with_capacity(extended_original_encoding + 1);
        let mut rhs_lc = Vec::with_capacity(extended_original_encoding + 1);
        for ((original_el, sorted_el), challenge) in extended_original_encoding
            .into_iter()
            .zip(sorted_encoding.into_iter())
            .zip(fs_challenges.iter())
        {
            let lhs_contribution = original_el.mul(cs, &challenge)?;
            let rhs_contribution = sorted_el.mul(cs, &challenge)?;

            lhs_lc.push((&lhs_contribution, F::one()));
            rhs_lc.push((&rhs_contribution, F::one()));
        }

        lhs_lc.push((&additive_part, F::one()));
        rhs_lc.push((&additive_part, F::one()));

        let lhs_contribution = linear_combination_collapse(cs, lhs_lc, None);
        let rhs_contribution = linear_combination_collapse(cs, rhs_lc, None);

        let lhs_candidate = lhs.mul(cs, &lhs_contribution)?;
        let rhs_candidate = rhs.mul(cs, &rhs_contribution)?;

        lhs = Num::conditionally_select(cs, &should_pop, &lhs_candidate, &lhs)?;
        rhs = Num::conditionally_select(cs, &should_pop, &rhs_candidate, &rhs)?;

        let TimestampedStorageLogRecord { record, timestamp } = sorted_item;

        // now resolve a logic about sorting itself
        let packed_key = pack_key(
            cs,
            (record.shard_id.clone(), record.address.clone(), record.key),
        )?;

        // ensure sorting
        let (keys_are_equal, previous_key_is_greater) =
            prepacked_long_comparison(cs, &previous_packed_key, &packed_key, &PACKED_WIDTHS)?;

        previous_key_is_greater
            .not()
            .conditionally_enforce_true(cs, &item_is_trivial.not())?;

        // if keys are the same then timestamps are sorted
        let (_, previous_timestamp_is_less) = previous_timestamp.sub(cs, &timestamp)?;
        // enforce if keys are the same and not trivial
        let must_enforce = keys_are_equal.and(cs, item_is_trivial.not())?;
        previous_timestamp_is_less.conditionally_enforce_true(cs, &must_enforce)?;

        // we follow the procedure:
        // if keys are different then we finish with a previous one and update parameters
        // else we just update parameters

        // if new cell
        {
            if _cycle == 0 {
                // it must always be true if we start
                keys_are_equal
                    .not()
                    .conditionally_enforce_true(cs, &is_start)?;
            }
            // finish with the old one
            // if somewhere along the way we did encounter a read at rollback depth zero (not important if there were such),
            // and if current rollback depth is 0 then we MUST issue a read

            let value_is_unchanged =
                UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value)?;
            // there may be a situation when as a result of sequence of writes
            // storage slot is CLAIMED to be unchanged. There are two options:
            // - unchanged because we had write - ... - rollback AND we do not have read at depth 0.
            //   In this case we used a temporary value, and the fact that the last action is rollback
            //   all the way to the start (to depth 0), we are not interested in what was an initial value
            // - unchanged because a -> write b -> ... -> write a AND we do or do not have read at depth 0.
            //   In this case we would not need to write IF prover is honest and provides a true witness to "read value"
            //   field at the first write. But we can not rely on this and have to check this fact!
            let current_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
            let unchanged_but_not_by_rollback =
                value_is_unchanged.and(cs, current_depth_is_zero.not())?;
            let issue_protective_read = this_cell_has_explicit_read_and_rollback_depth_zero
                .or(cs, unchanged_but_not_by_rollback)?;
            let should_write = value_is_unchanged.not();

            let query = LogQuery {
                address: previous_address,
                key: previous_key,
                read_value: this_cell_base_value,
                written_value: this_cell_current_value,
                r_w_flag: should_write,
                aux_byte: UInt8::zero(),
                rollback: Boolean::constant(false),
                is_service: Boolean::constant(false),
                shard_id: previous_shard_id,
                tx_number_in_block: UInt16::zero(),
                timestamp: UInt32::zero(),
            };

            // if we did only writes and rollbacks then we don't need to update
            let should_update = issue_protective_read.or(cs, should_write)?;
            let should_push = previous_item_is_trivial
                .not()
                .and(cs, keys_are_equal.not().and(cs, should_update))?;

            sorted_queue.push(cs, &query, &should_push, round_function)?;

            let new_non_trivial_cell = item_is_trivial.not().and(cs, keys_are_equal.not())?;

            // and update as we switch to the new cell with extra logic
            let meaningful_value = UInt256::conditionally_select(
                cs,
                &record.r_w_flag,
                &record.written_value,
                &record.read_value,
            )?;

            // re-update
            this_cell_base_value = UInt256::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &record.read_value,
                &this_cell_base_value,
            )?;

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &meaningful_value,
                &this_cell_current_value,
            )?;

            let rollback_depth_for_new_cell = UInt32::conditionally_select(
                cs,
                &record.r_w_flag,
                &UInt32::from_uint(1),
                &UInt32::zero(),
            )?;

            this_cell_current_depth = UInt32::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &rollback_depth_for_new_cell,
                &this_cell_current_depth,
            )?;

            // we have new non-trivial
            // and if it's read then it's definatelly at depth 0
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                &new_non_trivial_cell,
                &record.r_w_flag.not(),
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            )?;
        }

        // if same cell - update
        {
            let non_trivial_and_same_cell = item_is_trivial.not().and(cs, keys_are_equal)?;
            let non_trivial_read_of_same_cell =
                non_trivial_and_same_cell.and(cs, record.r_w_flag.not())?;
            let non_trivial_write_of_same_cell =
                non_trivial_and_same_cell.and(cs, record.r_w_flag)?;
            let write_no_rollback =
                non_trivial_write_of_same_cell.and(cs, record.rollback.not())?;
            let write_rollback = non_trivial_write_of_same_cell.and(cs, record.rollback)?;

            // update rollback depth the is a result of this action
            this_cell_current_depth = this_cell_current_depth
                .conditionally_increment_unchecked(cs, &write_no_rollback)?;
            this_cell_current_depth =
                this_cell_current_depth.conditionally_decrement_unchecked(cs, &write_rollback)?;

            // check consistency
            let read_is_equal_to_current =
                UInt256::equals(cs, &this_cell_current_value, &record.read_value)?;

            read_is_equal_to_current
                .conditionally_enforce_true(cs, &non_trivial_read_of_same_cell)?;

            // decide to update
            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &write_no_rollback,
                &record.written_value,
                &this_cell_current_value,
            )?;

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                &write_rollback,
                &record.read_value,
                &this_cell_current_value,
            )?;

            let current_rollback_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
            let read_at_rollback_depth_zero_of_same_cell =
                current_rollback_depth_is_zero.and(cs, non_trivial_read_of_same_cell)?;

            this_cell_base_value = UInt256::conditionally_select(
                cs,
                &read_at_rollback_depth_zero_of_same_cell,
                &record.read_value,
                &this_cell_base_value,
            )?;

            // we definately read non-trivial, and that is on depth 0, so set to true
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                &read_at_rollback_depth_zero_of_same_cell,
                &Boolean::constant(true),
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            )?;
        }

        // always update counters
        previous_shard_id = record.shard_id;
        previous_address = record.address;
        previous_key = record.key;
        previous_item_is_trivial = item_is_trivial;
        previous_timestamp = timestamp;
        previous_packed_key = packed_key;
    }

    // finalization step - out of cycle, and only if we are done just yet
    {
        let queues_exhausted = original_queue.is_empty(cs)?;

        // cell state is final
        let value_is_unchanged =
            UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value)?;
        let current_depth_is_zero = this_cell_current_depth.is_zero(cs)?;
        let unchanged_but_not_by_rollback =
            value_is_unchanged.and(cs, current_depth_is_zero.not())?;
        let issue_protective_read = this_cell_has_explicit_read_and_rollback_depth_zero
            .or(cs, unchanged_but_not_by_rollback)?;
        let should_write = value_is_unchanged.not();

        let query = LogQuery {
            address: previous_address,
            key: previous_key,
            read_value: this_cell_base_value,
            written_value: this_cell_current_value,
            r_w_flag: should_write,
            aux_byte: UInt8::zero(),
            rollback: Boolean::constant(false),
            is_service: Boolean::constant(false),
            shard_id: previous_shard_id,
            tx_number_in_block: UInt16::zero(),
            timestamp: UInt32::zero(),
        };

        // if we did only writes and rollbacks then we don't need to update
        let should_update = issue_protective_read.or(cs, should_write)?;
        let should_push = previous_item_is_trivial
            .not()
            .and(cs, should_update.and(cs, queues_exhausted))?;

        sorted_queue.push(cs, &query, &should_push, round_function)?;

        // reset flag to match simple witness generation convensions
        this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
            cs,
            &queues_exhausted,
            &Boolean::constant(false),
            &this_cell_has_explicit_read_and_rollback_depth_zero,
        )?;
    }

    // output our FSM values

    Ok((
        lhs,
        rhs,
        cycle_idx,
        previous_packed_key,
        previous_key,
        previous_address,
        previous_timestamp,
        this_cell_has_explicit_read_and_rollback_depth_zero,
        this_cell_base_value,
        this_cell_current_value,
        this_cell_current_depth,
        previous_shard_id,
    ))
}

pub fn pack_key<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    key_tuple: (UInt8<F>, UInt160<F>, UInt256<F>),
) -> [Variable; 7] {
    debug_assert!(F::CAPACITY_BITS >= 56);

    // LE packing
    // Attempting to stick to previous packing methods shown in this repo

    let (shard_id, address, key) = key_tuple;
    let key_bytes = key.inner.map(|el| el.decompose_into_bytes(cs));
    let address_bytes = address.inner.map(|el| el.decompose_into_bytes(cs));
    let v0 = Num::linear_combination(
        cs,
        &[
            (key_bytes[0][0].get_variable(), F::one()),
            (
                key_bytes[0][1].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                key_bytes[0][2].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                key_bytes[0][3].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                key_bytes[1][0].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                key_bytes[1][1].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                key_bytes[1][2].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v1 = Num::linear_combination(
        cs,
        &[
            (key_bytes[1][3].get_variable(), F::one()),
            (
                key_bytes[2][0].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                key_bytes[2][1].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                key_bytes[2][2].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                key_bytes[2][3].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                key_bytes[3][0].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                key_bytes[3][1].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v2 = Num::linear_combination(
        cs,
        &[
            (key_bytes[3][2].get_variable(), F::one()),
            (
                key_bytes[3][3].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                key_bytes[4][0].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                key_bytes[4][1].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                key_bytes[4][2].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                key_bytes[4][3].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                key_bytes[5][0].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v3 = Num::linear_combination(
        cs,
        &[
            (key_bytes[5][1].get_variable(), F::one()),
            (
                key_bytes[5][2].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                key_bytes[5][3].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                key_bytes[6][0].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                key_bytes[6][1].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                key_bytes[6][2].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                key_bytes[6][3].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v4 = Num::linear_combination(
        cs,
        &[
            (key_bytes[7][0].get_variable(), F::one()),
            (
                key_bytes[7][1].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                key_bytes[7][2].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                key_bytes[7][3].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                address_bytes[0][1].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                address_bytes[0][1].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                address_bytes[0][2].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v5 = Num::linear_combination(
        cs,
        &[
            (address_bytes[0][3].get_variable(), F::one()),
            (
                address_bytes[1][0].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                address_bytes[1][1].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                address_bytes[2][2].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                address_bytes[1][3].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                address_bytes[2][0].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                address_bytes[2][1].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v6 = Num::linear_combination(
        cs,
        &[
            (address_bytes[2][2].get_variable(), F::one()),
            (
                address_bytes[2][3].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                address_bytes[3][0].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                address_bytes[3][1].get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
            (
                address_bytes[3][2].get_variable(),
                F::from_u64_unchecked(1u64 << 32),
            ),
            (
                address_bytes[3][3].get_variable(),
                F::from_u64_unchecked(1u64 << 40),
            ),
            (
                address_bytes[4][0].get_variable(),
                F::from_u64_unchecked(1u64 << 48),
            ),
        ],
    )
    .get_variable();

    let v7 = Num::linear_combination(
        cs,
        &[
            (address_bytes[4][1].get_variable(), F::one()),
            (
                address_bytes[4][2].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                address_bytes[4][3].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (
                shard_id.inner.get_variable(),
                F::from_u64_unchecked(1u64 << 24),
            ),
        ],
    )
    .get_variable();

    [v0, v1, v2, v3, v4, v5, v6, v7]
}
