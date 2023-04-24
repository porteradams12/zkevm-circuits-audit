#![feature(generic_const_exprs)]
#![feature(array_chunks)]

use derivative::*;

pub mod config;

pub mod base_structures;
pub mod main_vm;
pub mod tables;
pub mod fsm_input_output;
pub mod demux_log_queue;
pub mod storage_application;
pub mod ecrecover;
pub mod sha256_round_function;
pub mod keccak256_round_function;

use boojum::pairing::ff;

pub const fn bit_width_to_bitmask(width: usize) -> u64 {
    (1u64 << width) - 1
}
