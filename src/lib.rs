#![feature(generic_const_exprs)]
#![feature(array_chunks)]
#![feature(box_into_inner)]

use derivative::*;

pub mod config;

pub mod base_structures;
pub mod demux_log_queue;
pub mod ecrecover;
pub mod fsm_input_output;
pub mod main_vm;
pub mod storage_application;
pub mod storage_validity_by_grand_product;
pub mod tables;

use boojum::pairing::ff;

pub const fn bit_width_to_bitmask(width: usize) -> u64 {
    (1u64 << width) - 1
}
