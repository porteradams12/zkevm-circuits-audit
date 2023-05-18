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
use boojum::gadgets::queue::queue_optimizer::SpongeOptimizer;
use boojum::gadgets::u8::UInt8;
use boojum::gadgets::{
    boolean::Boolean,
    num::Num,
    queue::*,
    traits::{
        allocatable::CSAllocatableExt, encodable::CircuitEncodableExt, selectable::Selectable,
    },
    u160::*,
    u32::UInt32,
};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;

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


    // passthrough must be trivial
    structured_input
        .observable_input
        .initial_log_queue_state.enforce_trivial_head(cs);

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &structured_input
            .observable_input
            .initial_log_queue_state,
        &structured_input.hidden_fsm_input.initial_log_queue_state,
    );
    let mut initial_queue = StorageLogQueue::<F, R>::from_state(cs, state);
    use std::sync::Arc;
    let initial_queue_witness = CircuitQueueWitness::from_inner_witness(initial_queue_witness);
    initial_queue.witness = Arc::new(initial_queue_witness);

    // for the rest it's just select between empty or from FSM
    let queue_states_from_fsm = [
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

    let empty_state = QueueState::empty(cs);
    let [
        mut storage_access_queue, 
        mut events_access_queue, 
        mut l1messages_access_queue, 
        mut keccak256_access_queue, 
        mut sha256_access_queue, 
        mut ecrecover_access_queue
    ] =
        queue_states_from_fsm.map(|el| {
            let state = QueueState::conditionally_select(
                cs,
                structured_input.start_flag,
                &empty_state,
                &el,
            );
            StorageLogQueue::<F, R>::from_state(cs, state)
        });

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

    structured_input.hidden_fsm_output.storage_access_queue_state = storage_access_queue.into_state();

    structured_input.hidden_fsm_output.events_access_queue_state = events_access_queue.into_state();

    structured_input.hidden_fsm_output.l1messages_access_queue_state = l1messages_access_queue.into_state();

    structured_input.hidden_fsm_output.keccak256_access_queue_state = keccak256_access_queue.into_state();

    structured_input.hidden_fsm_output.sha256_access_queue_state = sha256_access_queue.into_state();

    structured_input.hidden_fsm_output.ecrecover_access_queue_state = ecrecover_access_queue.into_state();

    // copy into observable output
    structured_input.observable_output.storage_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.storage_access_queue_state,
        &structured_input.observable_output.storage_access_queue_state,
    );
    structured_input.observable_output.events_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.events_access_queue_state,
        &structured_input.observable_output.events_access_queue_state,
    );
    structured_input.observable_output.l1messages_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.l1messages_access_queue_state,
        &structured_input.observable_output.l1messages_access_queue_state,
    );
    structured_input.observable_output.keccak256_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.keccak256_access_queue_state,
        &structured_input.observable_output.keccak256_access_queue_state,
    );
    structured_input.observable_output.sha256_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.sha256_access_queue_state,
        &structured_input.observable_output.sha256_access_queue_state,
    );
    structured_input.observable_output.ecrecover_access_queue_state = QueueState::conditionally_select(
        cs,
        completed,
        &structured_input.hidden_fsm_output.ecrecover_access_queue_state,
        &structured_input.observable_output.ecrecover_access_queue_state,
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
    let mut optimizer = SpongeOptimizer::<F, R, 8, 12, 4, 7>::new(limit);

    let [
        rollup_storage_queue, 
        events_queue, 
        l1_messages_queue, 
        keccak_calls_queue, 
        sha256_calls_queue, 
        ecdsa_calls_queue
    ] = output_queues;

    let keccak_precompile_address = UInt160::allocated_constant(cs, 
        *zkevm_opcode_defs::system_params::KECCAK256_ROUND_FUNCTION_PRECOMPILE_FORMAL_ADDRESS);
    let sha256_precompile_address = UInt160::allocated_constant(cs, 
        *zkevm_opcode_defs::system_params::SHA256_ROUND_FUNCTION_PRECOMPILE_FORMAL_ADDRESS);
    let ecrecover_precompile_address = UInt160::allocated_constant(cs, 
        *zkevm_opcode_defs::system_params::ECRECOVER_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS);

    for _ in 0..limit {
        let queue_is_empty = storage_log_queue.is_empty(cs);
        let execute = queue_is_empty.negated(cs);
        let popped = storage_log_queue.pop_front(cs, execute);

        let [aux_byte_for_storage, aux_byte_for_event, aux_byte_for_l1_message, aux_byte_for_precompile_call] =
            [STORAGE_AUX_BYTE, EVENT_AUX_BYTE, L1_MESSAGE_AUX_BYTE, PRECOMPILE_AUX_BYTE]
                .map(|byte|
                    UInt8::allocated_constant(cs, byte)
                );

        let is_storage_aux_byte = UInt8::equals(cs, &aux_byte_for_storage, &popped.0.aux_byte);
        let is_event_aux_byte = UInt8::equals(cs, &aux_byte_for_event, &popped.0.aux_byte);
        let is_l1_message_aux_byte = UInt8::equals(cs, &aux_byte_for_l1_message, &popped.0.aux_byte);
        let is_precompile_aux_byte = UInt8::equals(cs, &aux_byte_for_precompile_call, &popped.0.aux_byte,);

        let is_keccak_address = UInt160::equals(cs, &keccak_precompile_address, &popped.0.address);
        let is_sha256_address = UInt160::equals(cs, &sha256_precompile_address, &popped.0.address);
        let is_ecrecover_address = UInt160::equals(cs, &ecrecover_precompile_address, &popped.0.address);

        let is_rollup_shard = popped.0.shard_id.is_zero(cs);
        let execute_rollup_storage =
            Boolean::multi_and(cs, &[is_storage_aux_byte, is_rollup_shard, execute]);
        let is_porter_shard = is_rollup_shard.negated(cs);
        let execute_porter_storage =
            Boolean::multi_and(cs, &[is_storage_aux_byte, is_porter_shard, execute]);

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

        rollup_storage_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_rollup_storage, 
            LogType::RollupStorage as usize, 
            &mut optimizer
        );
        events_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_event, 
            LogType::Events as usize, 
            &mut optimizer
        );
        l1_messages_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_l1_message, 
            LogType::L1Messages as usize, 
            &mut optimizer
        );
        keccak_calls_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_keccak_call, 
            LogType::KeccakCalls as usize, 
            &mut optimizer
        );
        sha256_calls_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_sha256_call, 
            LogType::Sha256Calls as usize, 
            &mut optimizer
        );
        ecdsa_calls_queue.push_with_optimizer(
            cs, 
            popped.0, 
            execute_ecrecover_call, 
            LogType::ECRecoverCalls as usize, 
            &mut optimizer
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

    optimizer.enforce(cs);
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
