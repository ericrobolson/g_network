use crate::{
    packet::Packet,
    socket::{Socket, SocketErr},
};
use std::{borrow::Borrow, cell::RefCell};

/// A simple helper for writing tests.
#[allow(unused_macros)]
macro_rules! describe {
    ($module:tt => {$($test:tt)*}) => {
        mod $module {
            #[allow(unused_imports)]
            use super::*;

            $($test)*
        }
    };
}

/// A test socket.
/// This wraps an actual UDP socket so that the trait can be developed to closely
/// match the std lib.
pub struct TestSocket {
    //socket: std::net::UdpSocket,
    pub packet: RefCell<Vec<u8>>,
}

pub fn socket() -> TestSocket {
    TestSocket::new()
}

impl TestSocket {
    pub fn new() -> Self {
        Self {
            packet: RefCell::new(Packet::new(0.into(), 0.into(), 333).bytes().to_vec()),
        }
    }

    pub fn sent_packet(&self) -> Packet {
        let bytes = self.packet.borrow().clone();
        Packet::from_bytes(&bytes).unwrap()
    }
}

impl Socket for TestSocket {
    fn read(&self, buff: &mut [u8]) -> Result<(), SocketErr> {
        // Write the stored packet to the buff
        let bytes = self.packet.borrow().clone();

        for (idx, byte) in buff.iter_mut().enumerate() {
            *byte = bytes[idx];
        }

        Ok(())
    }
    fn send(&self, bytes: &[u8]) -> Result<(), SocketErr> {
        *self.packet.borrow_mut() = bytes.to_vec();

        //     self.socket.send(bytes).unwrap();
        Ok(())
    }
}
