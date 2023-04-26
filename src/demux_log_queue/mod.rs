use super::*;

pub mod input;

use crate::fsm_input_output::ClosedFormInputCompactForm;

use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::{gates::*, traits::cs::ConstraintSystem};
use boojum::field::SmallField;
use boojum::gadgets::{
    boolean::Boolean,
    num::Num,
    poseidon::CircuitRoundFunction,
    queue::*,
    traits::{
        allocatable::CSAllocatableExt, encodable::CircuitEncodableExt, selectable::Selectable,
    },
    u160::*,
    u32::UInt32,
};

use zkevm_opcode_defs::system_params::*;

use crate::{
    demux_log_queue::input::*,
    fsm_input_output::{circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH, *},
};

use crate::base_structures::log_query::LogQueryQueue;

pub type StorageLogQueue<F, R> = LogQueryQueue::<F, 8, 12, 4, R>;
pub type StorageLogQueueWitness<F> = CircuitQueueWitness<F, LogQuery<F>, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH>;

pub fn demultiplex_storage_logs_enty_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: LogDemuxerCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH] 
where [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]: {
    let LogDemuxerCircuitInstanceWitness {
        closed_form_input,
        initial_queue_witness,
    } = witness;

    let mut structured_input =
        LogDemuxerInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());

    let queue_states_from_fsm = [
        &structured_input.hidden_fsm_input.initial_log_queue_state,
        &structured_input.hidden_fsm_input.storage_access_queue_state,
        &structured_input.hidden_fsm_input.events_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .l1messages_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .keccak256_access_queue_state,
        &structured_input.hidden_fsm_input.sha256_access_queue_state,
        &structured_input
            .hidden_fsm_input
            .ecrecover_access_queue_state,
    ];

    let [
        _initial_log_queue_state_from_fsm,
        storage_access_queue_state_from_fsm,
        events_access_queue_state_from_fsm,
        l1messages_access_queue_state_from_fsm,
        keccak256_access_queue_state_from_fsm,
        sha256_access_queue_state_from_fsm,
        ecrecover_access_queue_state_from_fsm,
    ]: [CircuitQueue<F, LogQuery<F>, 8, 12, 4, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH, R>; 7]= queue_states_from_fsm.map(|el| {
        StorageLogQueue::from_raw_parts(
            cs,
            el.head,
            el.tail.tail,
            el.tail.length,
        )
    });

    let storage_access_queue_state_from_fsm = storage_access_queue_state_from_fsm;
    let events_access_queue_state_from_fsm = events_access_queue_state_from_fsm;
    let l1messages_access_queue_state_from_fsm = l1messages_access_queue_state_from_fsm;
    let keccak256_access_queue_state_from_fsm = keccak256_access_queue_state_from_fsm;
    let sha256_access_queue_state_from_fsm = sha256_access_queue_state_from_fsm;
    let ecrecover_access_queue_state_from_fsm = ecrecover_access_queue_state_from_fsm;

    let initial_queue_from_passthrough: CircuitQueue<
        F,
        LogQuery<F>,
        8,
        12,
        4,
        QUEUE_STATE_WIDTH,
        LOG_QUERY_PACKED_WIDTH,
        R,
    > = StorageLogQueue::from_raw_parts(
        cs,
        structured_input
            .observable_input
            .initial_log_queue_state
            .head,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail
            .tail,
        structured_input
            .observable_input
            .initial_log_queue_state
            .tail
            .length,
    );

    // passthrough must be trivial
    let zero_num = Num::zero(cs);
    for el in initial_queue_from_passthrough.head.iter() {
        Num::enforce_equal(cs, el, &zero_num);
    }

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &initial_queue_from_passthrough.into_state(),
        &structured_input.hidden_fsm_input.initial_log_queue_state,
    );
    let mut initial_queue =
        StorageLogQueue::<F, R>::from_raw_parts(cs, state.head, state.tail.tail, state.tail.length);
    use std::sync::Arc;
    let initial_queue_witness = CircuitQueueWitness::from_inner_witness(initial_queue_witness);
    initial_queue.witness = Arc::new(initial_queue_witness);
    // for the rest it's just select between empty or from FSM

    let queue_states_from_fsm = [
        storage_access_queue_state_from_fsm,
        events_access_queue_state_from_fsm,
        l1messages_access_queue_state_from_fsm,
        keccak256_access_queue_state_from_fsm,
        sha256_access_queue_state_from_fsm,
        ecrecover_access_queue_state_from_fsm,
    ];

    let empty_state = QueueState::empty(cs);
    let [storage_access_queue, events_access_queue, l1messages_access_queue, keccak256_access_queue, sha256_access_queue, ecrecover_access_queue] =
        queue_states_from_fsm.map(|el| {
            let state = QueueState::conditionally_select(
                cs,
                structured_input.start_flag,
                &empty_state,
                &el.into_state(),
            );
            StorageLogQueue::<F, R>::from_raw_parts(
                cs,
                state.head,
                state.tail.tail,
                state.tail.length,
            )
        });

    let mut storage_access_queue = storage_access_queue;
    let mut events_access_queue = events_access_queue;
    let mut l1messages_access_queue = l1messages_access_queue;
    let mut keccak256_access_queue = keccak256_access_queue;
    let mut sha256_access_queue = sha256_access_queue;
    let mut ecrecover_access_queue = ecrecover_access_queue;

    let input_queues = [
        &mut storage_access_queue,
        &mut events_access_queue,
        &mut l1messages_access_queue,
        &mut keccak256_access_queue,
        &mut sha256_access_queue,
        &mut ecrecover_access_queue,
    ];

    demultiplex_storage_logs_inner(cs, &mut initial_queue, input_queues, limit);
    use boojum::gadgets::traits::allocatable::CSPlaceholder;
    // form the final state
    structured_input.observable_output = LogDemuxerOutputData::placeholder(cs);

    let completed = initial_queue.is_empty(cs);
    structured_input.completion_flag = completed;

    structured_input.hidden_fsm_output.initial_log_queue_state = initial_queue.into_state();

    structured_input
        .hidden_fsm_output
        .storage_access_queue_state = storage_access_queue.into_state();

    structured_input.hidden_fsm_output.events_access_queue_state = events_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .l1messages_access_queue_state = l1messages_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .keccak256_access_queue_state = keccak256_access_queue.into_state();

    structured_input.hidden_fsm_output.sha256_access_queue_state = sha256_access_queue.into_state();

    structured_input
        .hidden_fsm_output
        .ecrecover_access_queue_state = ecrecover_access_queue.into_state();

    // copy into observable output

    structured_input
        .observable_output
        .storage_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input
            .hidden_fsm_output
            .storage_access_queue_state,
        &structured_input
            .observable_output
            .storage_access_queue_state,
    );
    structured_input.observable_output.events_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.events_access_queue_state,
        &structured_input.observable_output.events_access_queue_state,
    );
    structured_input
        .observable_output
        .l1messages_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input
            .hidden_fsm_output
            .l1messages_access_queue_state,
        &structured_input
            .observable_output
            .l1messages_access_queue_state,
    );
    structured_input
        .observable_output
        .keccak256_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input
            .hidden_fsm_output
            .keccak256_access_queue_state,
        &structured_input
            .observable_output
            .keccak256_access_queue_state,
    );
    structured_input.observable_output.sha256_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.sha256_access_queue_state,
        &structured_input.observable_output.sha256_access_queue_state,
    );
    structured_input
        .observable_output
        .ecrecover_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input
            .hidden_fsm_output
            .ecrecover_access_queue_state,
        &structured_input
            .observable_output
            .ecrecover_access_queue_state,
    );

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);

    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}

pub const NUM_SEPARATE_QUEUES: usize = 6;

#[repr(u64)]
pub enum LogType {
    RollupStorage,
    PorterStorage,
    Events,
    L1Messages,
    KeccakCalls,
    Sha256Calls,
    ECRecoverCalls,
}

pub fn demultiplex_storage_logs_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    storage_log_queue: &mut StorageLogQueue<F, R>,
    output_queues: [&mut StorageLogQueue<F, R>; NUM_SEPARATE_QUEUES],
    limit: usize,
) where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    assert!(limit <= u32::MAX as usize);

    let [rollup_storage_queue, events_queue, l1_messages_queue, keccak_calls_queue, sha256_calls_queue, ecdsa_calls_queue] =
        output_queues;

    const SYSTEM_CONTRACTS_OFFSET_ADDRESS: u16 = 1 << 15;

    const KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = SYSTEM_CONTRACTS_OFFSET_ADDRESS + 0x10;
    const SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x02; // as in Ethereum
    const ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS: u16 = 0x01; // as in Ethereum

    let keccak_precompile_address = UInt160::allocated_constant(
        cs,
        recompose_address_from_u32x5([
            KECCAK256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u32,
            0,
            0,
            0,
            0,
        ]),
    );

    let sha256_precompile_address = UInt160::allocated_constant(
        cs,
        recompose_address_from_u32x5([SHA256_ROUND_FUNCTION_PRECOMPILE_ADDRESS as u32, 0, 0, 0, 0]),
    );

    let ecrecover_precompile_address = UInt160::allocated_constant(
        cs,
        recompose_address_from_u32x5([
            ECRECOVER_INNER_FUNCTION_PRECOMPILE_ADDRESS as u32,
            0,
            0,
            0,
            0,
        ]),
    );

    for _ in 0..limit {
        let mut execute = storage_log_queue.is_empty(cs);
        execute = execute.negated(cs);
        let popped = storage_log_queue.pop_front(cs, execute);

        let [aux_byte_for_storage, aux_byte_for_event, aux_byte_for_l1_message, aux_byte_for_precompile_call] =
            [STORAGE_AUX_BYTE, EVENT_AUX_BYTE, L1_MESSAGE_AUX_BYTE, PRECOMPILE_AUX_BYTE]
                .map(|byte|
                    Num::from_variable(
                        cs.allocate_constant(
                            F::from_u64_unchecked(byte as u64)
                        )
                    )
                );

        let is_storage_aux_byte =
            Num::equals(cs, &aux_byte_for_storage, &popped.0.aux_byte.into_num());
        let is_event_aux_byte = Num::equals(cs, &aux_byte_for_event, &popped.0.aux_byte.into_num());
        let is_l1_message_aux_byte =
            Num::equals(cs, &aux_byte_for_l1_message, &popped.0.aux_byte.into_num());
        let is_precompile_aux_byte = Num::equals(
            cs,
            &aux_byte_for_precompile_call,
            &popped.0.aux_byte.into_num(),
        );

        let is_keccak_address = UInt160::equals(cs, &keccak_precompile_address, &popped.0.address);
        let is_sha256_address = UInt160::equals(cs, &sha256_precompile_address, &popped.0.address);
        let is_ecrecover_address =
            UInt160::equals(cs, &ecrecover_precompile_address, &popped.0.address);

        let mut is_rollup_shard = popped.0.shard_id.is_zero(cs);

        let execute_rollup_storage =
            Boolean::multi_and(cs, &[is_storage_aux_byte, is_rollup_shard, execute]);
        is_rollup_shard = is_rollup_shard.negated(cs);
        let execute_porter_storage =
            Boolean::multi_and(cs, &[is_storage_aux_byte, is_rollup_shard, execute]);

        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &execute_porter_storage, &boolean_false);
        let execute_event = Boolean::multi_and(cs, &[is_event_aux_byte, execute]);
        let execute_l1_message = Boolean::multi_and(cs, &[is_l1_message_aux_byte, execute]);
        let execute_keccak_call =
            Boolean::multi_and(cs, &[is_precompile_aux_byte, is_keccak_address, execute]);
        let execute_sha256_call =
            Boolean::multi_and(cs, &[is_precompile_aux_byte, is_sha256_address, execute]);
        let execute_ecrecover_call =
            Boolean::multi_and(cs, &[is_precompile_aux_byte, is_ecrecover_address, execute]);

        let bitmask = [
            execute_rollup_storage,
            execute_event,
            execute_l1_message,
            execute_keccak_call,
            execute_sha256_call,
            execute_ecrecover_call,
        ];

        push_with_optimize(
            cs,
            [
                rollup_storage_queue,
                events_queue,
                l1_messages_queue,
                keccak_calls_queue,
                sha256_calls_queue,
                ecdsa_calls_queue,
            ],
            bitmask,
            popped.0,
        );

        let expected_bitmask_bits = [
            is_storage_aux_byte,
            is_event_aux_byte,
            is_l1_message_aux_byte,
            is_precompile_aux_byte,
        ];

        let is_bitmask = check_if_bitmask_and_if_empty(cs, expected_bitmask_bits);

        is_bitmask.conditionally_enforce_true(cs, execute);
    }
}

pub fn push_with_optimize<
    F: SmallField,
    CS: ConstraintSystem<F>,
    EL: CircuitEncodableExt<F, N>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const T: usize,
    const N: usize,
    R: CircuitRoundFunction<F, AW, SW, CW>,
    const NUM_QUEUE: usize,
>(
    cs: &mut CS,
    mut queues: [&mut CircuitQueue<F, EL, AW, SW, CW, T, N, R>; NUM_QUEUE],
    bitmask: [Boolean<F>; NUM_QUEUE],
    value_encoding: EL,
) where
    [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let mut states = queues.iter().map(|x| x.into_state());
    let mut state = states.next().unwrap();

    for (bit, next_state) in bitmask.iter().skip(1).zip(states) {
        state = QueueState::conditionally_select(cs, *bit, &next_state, &state);
    }

    let mut exec_queue = CircuitQueue::<F, EL, AW, SW, CW, T, N, R>::from_raw_parts(
        cs,
        state.head,
        state.tail.tail,
        state.tail.length,
    );

    let boolean_true = Boolean::allocated_constant(cs, true);

    exec_queue.push(cs, value_encoding, boolean_true);

    for (bit, queue) in bitmask.into_iter().zip(queues.iter_mut()) {
        queue.head = <[Num<F>; T]>::conditionally_select(cs, bit, &exec_queue.head, &queue.head);
        queue.tail = <[Num<F>; T]>::conditionally_select(cs, bit, &exec_queue.tail, &queue.tail);
        queue.length = UInt32::conditionally_select(cs, bit, &exec_queue.length, &queue.length);
    }
}

pub fn check_if_bitmask_and_if_empty<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    mask: [Boolean<F>; N],
) -> Boolean<F>{
    let lc: [_; N] = mask.map(|el| (el.get_variable(), F::ONE));

    let lc = Num::linear_combination(cs, &lc);

    let one = Num::from_variable(cs.allocate_constant(F::ONE));
    let is_boolean = Num::equals(cs, &lc, &one);

    is_boolean
}
