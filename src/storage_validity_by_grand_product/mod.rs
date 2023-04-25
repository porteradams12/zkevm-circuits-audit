use super::*;

pub mod input;

use crate::fsm_input_output::ClosedFormInputCompactForm;

use crate::base_structures::{
    log_query::{LogQuery, LogQueryWitness, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::DstBuffer;
use boojum::cs::{gates::*, traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::traits::castable::WitnessCastable;
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
    u160::*,
    u256::*,
    u32::UInt32,
    u8::UInt8,
};

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

use std::sync::Arc;

#[derive(Derivative, CSAllocatable)]
#[derivative(Clone, Debug)]
pub struct TimestampedStorageLogRecord<F: SmallField> {
    pub record: LogQuery<F>,
    pub timestamp: UInt32<F>,
}

pub const EXTENDED_TIMESTAMP_ENCODING_ELEMENT: usize = 19;
pub const EXTENDED_TIMESTAMP_ENCODING_OFFSET: usize = 8;

impl<F: SmallField> TimestampedStorageLogRecord<F> {
    pub fn append_timestamp_to_raw_query_encoding<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        original_encoding: &[Variable; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN],
        timestamp: &UInt32<F>,
    ) -> [Variable; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN] {
        let timestamp_inner = timestamp.to_le_bytes(cs);
        let encoding = Num::linear_combination(
            cs,
            &[
                (
                    // Original encoding at index 19 is only 8 bits
                    original_encoding[EXTENDED_TIMESTAMP_ENCODING_ELEMENT],
                    F::ONE,
                ),
                (
                    timestamp_inner[0].get_variable(),
                    F::from_u64_unchecked(1u64 << 8),
                ),
                (
                    timestamp_inner[1].get_variable(),
                    F::from_u64_unchecked(1u64 << 16),
                ),
                (
                    timestamp_inner[2].get_variable(),
                    F::from_u64_unchecked(1u64 << 24),
                ),
                (
                    timestamp_inner[3].get_variable(),
                    F::from_u64_unchecked(1u64 << 32),
                ),
            ],
        )
        .get_variable();

        let mut result = *original_encoding;
        result[EXTENDED_TIMESTAMP_ENCODING_ELEMENT] = encoding;
        result
    }
}

impl<F: SmallField> CircuitEncodable<F, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<F>
{
    fn encode<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> [Variable; TIMESTAMPED_STORAGE_LOG_ENCODING_LEN] {
        let original_encoding = self.record.encode(cs);

        Self::append_timestamp_to_raw_query_encoding(cs, &original_encoding, &self.timestamp)
    }
}

impl<F: SmallField> CSAllocatableExt<F> for TimestampedStorageLogRecord<F>
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    const INTERNAL_STRUCT_LEN: usize = 37;

    // NOTE(julesdesmit): using Self::INTERNAL_STRUCT_LEN here causes some kind of cyclic dependency issue
    fn witness_from_set_of_values(values: [F; 37]) -> Self::Witness {
        let record_values = [F::ZERO; <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
        record_values
            .copy_from_slice(&values[..<LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]);
        let record =
            <LogQuery<F> as CSAllocatableExt<F>>::witness_from_set_of_values(record_values);
        let other_timestamp: u32 = WitnessCastable::cast_from_source(values[36]);

        Self::Witness {
            record,
            timestamp: other_timestamp,
        }
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
        todo!()
    }

    fn flatten_as_variables(&self) -> [F; 37] {
        [
            self.record.address.inner[0].get_variable(),
            self.record.address.inner[1].get_variable(),
            self.record.address.inner[2].get_variable(),
            self.record.address.inner[3].get_variable(),
            self.record.address.inner[4].get_variable(),
            self.record.key.inner[0].get_variable(),
            self.record.key.inner[1].get_variable(),
            self.record.key.inner[2].get_variable(),
            self.record.key.inner[3].get_variable(),
            self.record.key.inner[4].get_variable(),
            self.record.key.inner[5].get_variable(),
            self.record.key.inner[6].get_variable(),
            self.record.key.inner[7].get_variable(),
            self.record.read_value.inner[0].get_variable(),
            self.record.read_value.inner[1].get_variable(),
            self.record.read_value.inner[2].get_variable(),
            self.record.read_value.inner[3].get_variable(),
            self.record.read_value.inner[4].get_variable(),
            self.record.read_value.inner[5].get_variable(),
            self.record.read_value.inner[6].get_variable(),
            self.record.read_value.inner[7].get_variable(),
            self.record.written_value.inner[0].get_variable(),
            self.record.written_value.inner[1].get_variable(),
            self.record.written_value.inner[2].get_variable(),
            self.record.written_value.inner[3].get_variable(),
            self.record.written_value.inner[4].get_variable(),
            self.record.written_value.inner[5].get_variable(),
            self.record.written_value.inner[6].get_variable(),
            self.record.written_value.inner[7].get_variable(),
            self.record.aux_byte.get_variable(),
            self.record.rw_flag.get_variable(),
            self.record.rollback.get_variable(),
            self.record.is_service.get_variable(),
            self.record.shard_id.get_variable(),
            self.record.tx_number_in_block.get_variable(),
            self.record.timestamp.get_variable(),
            self.timestamp.get_variable(),
        ]
    }

    fn set_internal_variables_values(_witness: Self::Witness, _dst: &mut DstBuffer<'_, '_, F>) {
        todo!();
    }
}

impl<F: SmallField> CircuitEncodableExt<F, TIMESTAMPED_STORAGE_LOG_ENCODING_LEN>
    for TimestampedStorageLogRecord<F>
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
}

pub fn sort_and_deduplicate_storage_access_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    closed_form_input: StorageDeduplicatorInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; 1]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let structured_input_witness = closed_form_input.closed_form_input;
    let unsorted_queue_witness = closed_form_input.unsorted_queue_witness;
    let intermediate_sorted_queue_witness = closed_form_input.intermediate_sorted_queue_witness;

    let mut structured_input = StorageDeduplicatorInputOutput::alloc_ignoring_outputs(
        cs,
        structured_input_witness.clone(),
    );

    let unsorted_queue_from_passthrough_state = QueueState {
        head: structured_input
            .observable_input
            .unsorted_log_queue_state
            .head,
        tail: structured_input
            .observable_input
            .unsorted_log_queue_state
            .tail,
    };

    let unsorted_queue_from_fsm_input_state = QueueState {
        head: structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .head,
        tail: structured_input
            .hidden_fsm_input
            .current_unsorted_queue_state
            .tail,
    };

    // passthrought must be trivial
    unsorted_queue_from_passthrough_state.enforce_trivial_head(cs);

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &unsorted_queue_from_passthrough_state,
        &unsorted_queue_from_fsm_input_state,
    );
    let mut unsorted_queue = StorageLogQueue::<F, R>::from_state(cs, state);

    unsorted_queue.witness = Arc::new(CircuitQueueWitness::from_inner_witness(
        unsorted_queue_witness,
    ));

    // same logic from sorted
    let intermediate_sorted_queue_from_passthrough = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .head,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail
            .tail,
        structured_input
            .observable_input
            .intermediate_sorted_queue_state
            .tail
            .length,
    );

    let intermediate_sorted_queue_from_fsm_input = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .tail
            .tail,
        structured_input
            .hidden_fsm_input
            .current_intermediate_sorted_queue_state
            .tail
            .length,
    );

    // passthrought must be trivial
    intermediate_sorted_queue_from_passthrough.enforce_trivial_head(cs);

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &intermediate_sorted_queue_from_passthrough.into_state(),
        &intermediate_sorted_queue_from_fsm_input.into_state(),
    );
    let mut intermediate_sorted_queue = CircuitQueue::<
        F,
        TimestampedStorageLogRecord<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >::from_state(cs, state);

    intermediate_sorted_queue.witness = Arc::new(CircuitQueueWitness::from_inner_witness(
        intermediate_sorted_queue_witness,
    ));

    // for final sorted queue it's easier

    let empty_final_sorted_queue = StorageLogQueue::<F, R>::empty(cs);
    let final_sorted_queue_from_fsm_input = StorageLogQueue::<F, R>::from_raw_parts(
        cs,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .head,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .tail
            .tail,
        structured_input
            .hidden_fsm_input
            .current_final_sorted_queue_state
            .tail
            .length,
    );

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &empty_final_sorted_queue.into_state(),
        &final_sorted_queue_from_fsm_input.into_state(),
    );
    let mut final_sorted_queue = StorageLogQueue::<F, R>::from_state(cs, state);

    // we can always ensure this
    UInt32::equals(
        cs,
        &unsorted_queue.length,
        &intermediate_sorted_queue.length,
    );

    // get challenges for permutation argument

    let mut fs_input = vec![];
    fs_input.extend(
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .tail
            .tail,
    );
    fs_input.push(
        structured_input
            .observable_input
            .unsorted_log_queue_state
            .tail
            .length
            .into_num(),
    );
    fs_input.extend(intermediate_sorted_queue_from_passthrough.tail);
    fs_input.push(intermediate_sorted_queue_from_passthrough.length.into_num());

    // this is a permutation proof through the grand product
    let mut state = R::create_empty_state(cs);
    let length = Num::allocate(cs, F::from_u64_unchecked(fs_input.len() as u64)).get_variable();
    R::apply_length_specialization(cs, &mut state, length);
    for chunk in fs_input.array_chunks() {
        let padding_els = 12 - chunk.len();
        let input_fixed_len: [Num<F>; 12] = if padding_els == 0 {
            chunk.try_into().expect("length must match")
        } else {
            let tmp = Num::allocated_constant(cs, F::ONE);
            let it = chunk
                .iter()
                .chain(std::iter::repeat(&tmp).take(padding_els));

            it.copied()
                .collect::<Vec<_>>()
                .as_slice()
                .try_into()
                .expect("length must match")
        };

        // Create an array of variables so that we can continue hashing into the appropriate state.
        let mut input_fixed_len_variable = [Variable::placeholder(); 12];
        input_fixed_len_variable
            .iter_mut()
            .enumerate()
            .for_each(|(i, e)| *e = input_fixed_len[i].get_variable());
        state = R::compute_round_function(cs, input_fixed_len_variable);
    }

    let mut taken = 0; // up to absorbtion length
    let mut fs_challenges = vec![];
    for _ in 0..NUM_PERMUTATION_ARG_CHALLENGES {
        if taken == 2 {
            // run round
            state = R::compute_round_function(cs, state);
            taken = 0;
        }

        let challenge = state[taken];
        fs_challenges.push(challenge);

        taken += 1;
    }

    let mut fs_challenges_nums = [Num::zero(cs); NUM_PERMUTATION_ARG_CHALLENGES];
    fs_challenges_nums
        .iter_mut()
        .zip(fs_challenges)
        .for_each(|(e, v)| *e = Num::from_variable(v));

    let one = Num::allocated_constant(cs, F::ONE);
    let initial_lhs = Num::conditionally_select(
        cs,
        structured_input.start_flag,
        &one,
        &structured_input.hidden_fsm_input.lhs_accumulator,
    );

    let initial_rhs = Num::conditionally_select(
        cs,
        structured_input.start_flag,
        &one,
        &structured_input.hidden_fsm_input.rhs_accumulator,
    );

    // there is no code at address 0 in our case, so we can formally use it for all the purposes
    let zeros = [Num::<F>::zero(cs); 8];
    let previous_packed_key = <[Num<F>; 8]>::conditionally_select(
        cs,
        structured_input.start_flag,
        &zeros,
        &structured_input.hidden_fsm_input.previous_packed_key,
    );

    let zero = UInt32::zero(cs);
    let cycle_idx = UInt32::conditionally_select(
        cs,
        structured_input.start_flag,
        &zero,
        &structured_input.hidden_fsm_input.cycle_idx,
    );

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
        fs_challenges_nums,
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
    );

    let unsorted_is_empty = unsorted_queue.is_empty(cs);
    let sorted_is_empty = intermediate_sorted_queue.is_empty(cs);

    Boolean::enforce_equal(cs, &unsorted_is_empty, &sorted_is_empty);

    let completed = unsorted_is_empty.and(cs, sorted_is_empty);
    Num::conditionally_enforce_equal(cs, completed, &new_lhs, &new_rhs);

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

    let empty_queue_state = QueueState::empty(cs);
    let state = QueueState::conditionally_select(
        cs,
        completed,
        &final_sorted_queue.into_state(),
        &empty_queue_state,
    );
    let final_queue_for_observable_output = CircuitQueue::<
        F,
        LogQuery<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        LOG_QUERY_PACKED_WIDTH,
        R,
    >::from_state(cs, state);

    structured_input.observable_output.final_sorted_queue_state =
        final_queue_for_observable_output.into_state();

    structured_input
        .hidden_fsm_output
        .current_final_sorted_queue_state = final_sorted_queue.into_state();

    if let Some(circuit_result) = structured_input.witness_hook(&*cs)() {
        assert_eq!(circuit_result, structured_input_witness);
    }

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);

    // dbg!(compact_form.create_witness());
    let input_committment =
        commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_committment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_committment
}

const NUM_PERMUTATION_ARG_CHALLENGES: usize = TIMESTAMPED_STORAGE_LOG_ENCODING_LEN + 1;

pub fn sort_and_deduplicate_storage_access_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    mut lhs: Num<F>,
    mut rhs: Num<F>,
    original_queue: &mut StorageLogQueue<F, R>,
    intermediate_sorted_queue: &mut CircuitQueue<
        F,
        TimestampedStorageLogRecord<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        TIMESTAMPED_STORAGE_LOG_ENCODING_LEN,
        R,
    >,
    sorted_queue: &mut StorageLogQueue<F, R>,
    is_start: Boolean<F>,
    mut cycle_idx: UInt32<F>,
    fs_challenges: [Num<F>; NUM_PERMUTATION_ARG_CHALLENGES],
    mut previous_packed_key: [Num<F>; 8],
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
    [Num<F>; 8],
    UInt256<F>,
    UInt160<F>,
    UInt32<F>,
    Boolean<F>,
    UInt256<F>,
    UInt256<F>,
    UInt32<F>,
    UInt8<F>,
)
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
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

    const PACKED_WIDTHS: [usize; 8] = [56, 56, 56, 56, 56, 56, 56, 32];

    for _cycle in 0..limit {
        let original_timestamp = cycle_idx;
        // increment it immediatelly
        unsafe {
            let new_cycle_idx = cycle_idx.increment_unchecked(cs);
            cycle_idx = new_cycle_idx;
        }

        let original_is_empty = original_queue.is_empty(cs);
        let sorted_is_empty = intermediate_sorted_queue.is_empty(cs);
        Boolean::enforce_equal(cs, &original_is_empty, &sorted_is_empty);

        let should_pop = original_is_empty.negated(cs);
        let item_is_trivial = original_is_empty;

        let (_, original_encoding) = original_queue.pop_front(cs, should_pop);
        let (sorted_item, sorted_encoding) = intermediate_sorted_queue.pop_front(cs, should_pop);
        let extended_original_encoding =
            TimestampedStorageLogRecord::append_timestamp_to_raw_query_encoding(
                cs,
                &original_encoding,
                &original_timestamp,
            );

        assert_eq!(extended_original_encoding.len(), sorted_encoding.len());
        assert_eq!(extended_original_encoding.len(), fs_challenges.len() - 1);

        // accumulate into product
        let extended_original_encoding = extended_original_encoding
            .iter()
            .map(|v| Num::from_variable(*v))
            .collect::<Vec<Num<F>>>();
        let sorted_encoding = sorted_encoding
            .iter()
            .map(|v| Num::from_variable(*v))
            .collect::<Vec<Num<F>>>();

        let mut lhs_lc = Vec::with_capacity(extended_original_encoding.len() + 1);
        let mut rhs_lc = Vec::with_capacity(extended_original_encoding.len() + 1);
        for ((original_el, sorted_el), challenge) in extended_original_encoding
            .into_iter()
            .zip(sorted_encoding.into_iter())
            .zip(fs_challenges.iter())
        {
            let lhs_contribution = original_el.mul(cs, &challenge);
            let rhs_contribution = sorted_el.mul(cs, &challenge);

            lhs_lc.push((lhs_contribution.get_variable(), F::ONE));
            rhs_lc.push((rhs_contribution.get_variable(), F::ONE));
        }

        lhs_lc.push((additive_part.get_variable(), F::ONE));
        rhs_lc.push((additive_part.get_variable(), F::ONE));

        let lhs_lc = Num::linear_combination(cs, &lhs_lc);
        let rhs_lc = Num::linear_combination(cs, &rhs_lc);

        let lhs_candidate = lhs.mul(cs, &lhs_lc);
        let rhs_candidate = rhs.mul(cs, &rhs_lc);

        lhs = Num::conditionally_select(cs, should_pop, &lhs_candidate, &lhs);
        rhs = Num::conditionally_select(cs, should_pop, &rhs_candidate, &rhs);

        let TimestampedStorageLogRecord { record, timestamp } = sorted_item;

        // now resolve a logic about sorting itself
        let packed_key = pack_key(
            cs,
            (record.shard_id.clone(), record.address.clone(), record.key),
        );

        // ensure sorting
        let (keys_are_equal, previous_key_is_greater) =
            prepacked_long_comparison(cs, &previous_packed_key, &packed_key, &PACKED_WIDTHS);

        let not_item_is_trivial = item_is_trivial.negated(cs);
        previous_key_is_greater
            .negated(cs)
            .conditionally_enforce_true(cs, not_item_is_trivial);

        // if keys are the same then timestamps are sorted
        let (_, previous_timestamp_is_less, _) = previous_timestamp.overflowing_sub(cs, timestamp);
        // enforce if keys are the same and not trivial
        let must_enforce = keys_are_equal.and(cs, not_item_is_trivial);
        previous_timestamp_is_less.conditionally_enforce_true(cs, must_enforce);

        // we follow the procedure:
        // if keys are different then we finish with a previous one and update parameters
        // else we just update parameters

        // if new cell
        {
            if _cycle == 0 {
                // it must always be true if we start
                keys_are_equal
                    .negated(cs)
                    .conditionally_enforce_true(cs, is_start);
            }
            // finish with the old one
            // if somewhere along the way we did encounter a read at rollback depth zero (not important if there were such),
            // and if current rollback depth is 0 then we MUST issue a read

            let value_is_unchanged =
                UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value);
            // there may be a situation when as a result of sequence of writes
            // storage slot is CLAIMED to be unchanged. There are two options:
            // - unchanged because we had write - ... - rollback AND we do not have read at depth 0.
            //   In this case we used a temporary value, and the fact that the last action is rollback
            //   all the way to the start (to depth 0), we are not interested in what was an initial value
            // - unchanged because a -> write b -> ... -> write a AND we do or do not have read at depth 0.
            //   In this case we would not need to write IF prover is honest and provides a true witness to "read value"
            //   field at the first write. But we can not rely on this and have to check this fact!
            let current_depth_is_zero = this_cell_current_depth.is_zero(cs);
            let not_current_depth_is_zero = current_depth_is_zero.negated(cs);
            let unchanged_but_not_by_rollback =
                value_is_unchanged.and(cs, not_current_depth_is_zero);
            let issue_protective_read = this_cell_has_explicit_read_and_rollback_depth_zero
                .or(cs, unchanged_but_not_by_rollback);
            let should_write = value_is_unchanged.negated(cs);

            let query = LogQuery {
                address: previous_address,
                key: previous_key,
                read_value: this_cell_base_value,
                written_value: this_cell_current_value,
                rw_flag: should_write,
                aux_byte: UInt8::zero(cs),
                rollback: Boolean::allocated_constant(cs, false),
                is_service: Boolean::allocated_constant(cs, false),
                shard_id: previous_shard_id,
                tx_number_in_block: UInt32::zero(cs),
                timestamp: UInt32::zero(cs),
            };

            // if we did only writes and rollbacks then we don't need to update
            let should_update = issue_protective_read.or(cs, should_write);
            let not_keys_are_equal = keys_are_equal.negated(cs);
            let not_keys_are_equal_and_should_update = not_keys_are_equal.and(cs, should_update);
            let should_push = previous_item_is_trivial
                .negated(cs)
                .and(cs, not_keys_are_equal_and_should_update);

            sorted_queue.push(cs, query, should_push);

            let new_non_trivial_cell = item_is_trivial.negated(cs).and(cs, not_keys_are_equal);

            // and update as we switch to the new cell with extra logic
            let meaningful_value = UInt256::conditionally_select(
                cs,
                record.rw_flag,
                &record.written_value,
                &record.read_value,
            );

            // re-update
            this_cell_base_value = UInt256::conditionally_select(
                cs,
                new_non_trivial_cell,
                &record.read_value,
                &this_cell_base_value,
            );

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                new_non_trivial_cell,
                &meaningful_value,
                &this_cell_current_value,
            );

            let one = UInt32::allocated_constant(cs, 1);
            let zero = UInt32::zero(cs);
            let rollback_depth_for_new_cell =
                UInt32::conditionally_select(cs, record.rw_flag, &one, &zero);

            this_cell_current_depth = UInt32::conditionally_select(
                cs,
                new_non_trivial_cell,
                &rollback_depth_for_new_cell,
                &this_cell_current_depth,
            );

            // we have new non-trivial
            // and if it's read then it's definatelly at depth 0
            let not_rw_flag = record.rw_flag.negated(cs);
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                new_non_trivial_cell,
                &not_rw_flag,
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            );
        }

        // if same cell - update
        {
            let not_rw_flag = record.rw_flag.negated(cs);
            let non_trivial_and_same_cell = item_is_trivial.negated(cs).and(cs, keys_are_equal);
            let non_trivial_read_of_same_cell = non_trivial_and_same_cell.and(cs, not_rw_flag);
            let non_trivial_write_of_same_cell = non_trivial_and_same_cell.and(cs, record.rw_flag);
            let not_rollback = record.rollback.negated(cs);
            let write_no_rollback = non_trivial_write_of_same_cell.and(cs, not_rollback);
            let write_rollback = non_trivial_write_of_same_cell.and(cs, record.rollback);

            // update rollback depth the is a result of this action
            let one = UInt32::allocated_constant(cs, 1);
            let (incremented_depth, _) = this_cell_current_depth.add_no_overflow(cs, one);
            this_cell_current_depth = UInt32::conditionally_select(
                cs,
                write_no_rollback,
                &incremented_depth,
                &this_cell_current_depth,
            );
            let (decremented_depth, _) = this_cell_current_depth.sub_no_overflow(cs, one);
            this_cell_current_depth = UInt32::conditionally_select(
                cs,
                write_rollback,
                &this_cell_current_depth,
                &decremented_depth,
            );

            // check consistency
            let read_is_equal_to_current =
                UInt256::equals(cs, &this_cell_current_value, &record.read_value);

            read_is_equal_to_current.conditionally_enforce_true(cs, non_trivial_read_of_same_cell);

            // decide to update
            this_cell_current_value = UInt256::conditionally_select(
                cs,
                write_no_rollback,
                &record.written_value,
                &this_cell_current_value,
            );

            this_cell_current_value = UInt256::conditionally_select(
                cs,
                write_rollback,
                &record.read_value,
                &this_cell_current_value,
            );

            let current_rollback_depth_is_zero = this_cell_current_depth.is_zero(cs);
            let read_at_rollback_depth_zero_of_same_cell =
                current_rollback_depth_is_zero.and(cs, non_trivial_read_of_same_cell);

            this_cell_base_value = UInt256::conditionally_select(
                cs,
                read_at_rollback_depth_zero_of_same_cell,
                &record.read_value,
                &this_cell_base_value,
            );

            // we definately read non-trivial, and that is on depth 0, so set to true
            let constant_true = Boolean::allocated_constant(cs, true);
            this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
                cs,
                read_at_rollback_depth_zero_of_same_cell,
                &constant_true,
                &this_cell_has_explicit_read_and_rollback_depth_zero,
            );
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
        let queues_exhausted = original_queue.is_empty(cs);

        // cell state is final
        let value_is_unchanged =
            UInt256::equals(cs, &this_cell_current_value, &this_cell_base_value);
        let current_depth_is_zero = this_cell_current_depth.is_zero(cs);
        let not_current_depth_is_zero = current_depth_is_zero.negated(cs);
        let unchanged_but_not_by_rollback = value_is_unchanged.and(cs, not_current_depth_is_zero);
        let issue_protective_read = this_cell_has_explicit_read_and_rollback_depth_zero
            .or(cs, unchanged_but_not_by_rollback);
        let should_write = value_is_unchanged.negated(cs);

        let query = LogQuery {
            address: previous_address,
            key: previous_key,
            read_value: this_cell_base_value,
            written_value: this_cell_current_value,
            rw_flag: should_write,
            aux_byte: UInt8::zero(cs),
            rollback: Boolean::allocated_constant(cs, false),
            is_service: Boolean::allocated_constant(cs, false),
            shard_id: previous_shard_id,
            tx_number_in_block: UInt32::zero(cs),
            timestamp: UInt32::zero(cs),
        };

        // if we did only writes and rollbacks then we don't need to update
        let should_update = issue_protective_read.or(cs, should_write);
        let should_update_and_queues_exhausted = should_update.and(cs, queues_exhausted);
        let should_push = previous_item_is_trivial
            .negated(cs)
            .and(cs, should_update_and_queues_exhausted);

        sorted_queue.push(cs, query, should_push);

        // reset flag to match simple witness generation convensions
        let constant_false = Boolean::allocated_constant(cs, false);
        this_cell_has_explicit_read_and_rollback_depth_zero = Boolean::conditionally_select(
            cs,
            queues_exhausted,
            &constant_false,
            &this_cell_has_explicit_read_and_rollback_depth_zero,
        );
    }

    // output our FSM values

    (
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
    )
}

pub fn pack_key<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    key_tuple: (UInt8<F>, UInt160<F>, UInt256<F>),
) -> [Num<F>; 8] {
    debug_assert!(F::CAPACITY_BITS >= 56);

    // LE packing
    // Attempting to stick to previous packing methods shown in this repo

    let (shard_id, address, key) = key_tuple;
    let key_bytes = key.inner.map(|el| el.decompose_into_bytes(cs));
    let address_bytes = address.inner.map(|el| el.decompose_into_bytes(cs));
    let v0 = Num::linear_combination(
        cs,
        &[
            (key_bytes[0][0].get_variable(), F::ONE),
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
    );

    let v1 = Num::linear_combination(
        cs,
        &[
            (key_bytes[1][3].get_variable(), F::ONE),
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
    );

    let v2 = Num::linear_combination(
        cs,
        &[
            (key_bytes[3][2].get_variable(), F::ONE),
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
    );

    let v3 = Num::linear_combination(
        cs,
        &[
            (key_bytes[5][1].get_variable(), F::ONE),
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
    );

    let v4 = Num::linear_combination(
        cs,
        &[
            (key_bytes[7][0].get_variable(), F::ONE),
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
    );

    let v5 = Num::linear_combination(
        cs,
        &[
            (address_bytes[0][3].get_variable(), F::ONE),
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
    );

    let v6 = Num::linear_combination(
        cs,
        &[
            (address_bytes[2][2].get_variable(), F::ONE),
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
    );

    let v7 = Num::linear_combination(
        cs,
        &[
            (address_bytes[4][1].get_variable(), F::ONE),
            (
                address_bytes[4][2].get_variable(),
                F::from_u64_unchecked(1u64 << 8),
            ),
            (
                address_bytes[4][3].get_variable(),
                F::from_u64_unchecked(1u64 << 16),
            ),
            (shard_id.get_variable(), F::from_u64_unchecked(1u64 << 24)),
        ],
    );

    [v0, v1, v2, v3, v4, v5, v6, v7]
}

/// Check that a == b and a > b by performing a long subtraction b - a with borrow.
/// Both a and b are considered as least significant word first
#[track_caller]
pub fn prepacked_long_comparison<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &[Num<F>],
    b: &[Num<F>],
    width_data: &[usize],
) -> (Boolean<F>, Boolean<F>) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), width_data.len());

    let mut minus_one = F::ONE;
    minus_one.negate();

    let mut previous_borrow = Boolean::allocated_constant(cs, false);
    let mut limbs_are_equal = vec![];

    for ((a, b), width) in a.iter().zip(b.iter()).zip(width_data.iter()) {
        let (result_witness, borrow_witness) = {
            use num_integer::Integer;
            use num_traits::Zero;

            let a = a.witness_hook(&*cs)().unwrap().as_raw_u64();
            let b = b.witness_hook(&*cs)().unwrap().as_raw_u64();
            let borrow_guard = 1u64 << width;

            let tmp =
                borrow_guard.clone() + b - a - previous_borrow.witness_hook(&*cs)().unwrap() as u64;
            let (q, r) = tmp.div_rem(&borrow_guard);

            let borrow = q.is_zero();
            let wit = F::from_u64_unchecked(r);

            (wit, borrow)
        };

        let borrow = Boolean::allocate(cs, borrow_witness);
        let intermediate_result = Num::allocate(cs, result_witness);
        intermediate_result.constraint_bit_length_as_bytes(cs, *width);

        let intermediate_is_zero = intermediate_result.is_zero(cs);
        limbs_are_equal.push(intermediate_is_zero);

        // b - a - previous_borrow + 2^X * borrow = intermediate

        let result = Num::<F>::linear_combination(
            cs,
            &[
                (b.get_variable(), F::ONE),
                (a.get_variable(), minus_one),
                (previous_borrow.get_variable(), minus_one),
                (intermediate_result.get_variable(), minus_one),
                (borrow.get_variable(), F::from_u64_unchecked(1u64 << width)),
            ],
        )
        .get_variable();
        ZeroCheckGate::check_if_zero(cs, result);

        previous_borrow = borrow;
    }

    let final_borrow = previous_borrow;
    let eq = Boolean::multi_and(cs, &limbs_are_equal);

    (eq, final_borrow)
}
