#![feature(generic_const_exprs)]
#![feature(array_chunks)]

use derivative::*;

pub mod config;

pub mod base_structures;
pub mod main_vm;
pub mod tables;
pub mod fsm_input_output;
pub mod demux_log_queue;
pub mod code_unpacker_sha256;

pub const fn bit_width_to_bitmask(width: usize) -> u64 {
    (1u64 << width) - 1
}
