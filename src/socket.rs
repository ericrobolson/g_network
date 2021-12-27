#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SocketErr {}

/// A minimal socket trait to use with this library.
pub trait Socket {
    /// Attempts to send the bytes on the socket.
    fn send(&self, bytes: &[u8]) -> Result<(), SocketErr>;

    /// Attempts to read off the socket.
    fn read(&self, buff: &mut [u8]) -> Result<(), SocketErr>;
}
