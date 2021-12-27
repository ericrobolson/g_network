#![cfg_attr(not(test), no_std)]

#[cfg(test)]
#[macro_use]
mod test_helpers;
mod types;
mod connection;
#[allow(dead_code)]
mod packet;
#[allow(dead_code)]
mod packet_id;
mod ring_buffer;
mod socket;

use packet::*;
use packet_id::*;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PacketErr {
    ChecksumMismatch,
    WouldOverflow,
}

pub struct Networking {}

pub struct Address;
