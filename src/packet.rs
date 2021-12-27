use crate::{
    packet_id::{self, PacketId},
    types::AckStatus,
    PacketErr,
};

type AckBitfield = u32;
type Crc32Hash = u32;
type PacketLen = u16;

const ACK_ID_SIZE: usize = core::mem::size_of::<PacketId>();
const PACKET_ID_SIZE: usize = core::mem::size_of::<PacketId>();
const ACK_BITFIELD_SIZE: usize = core::mem::size_of::<AckBitfield>();
const CRC32_HASH_SIZE: usize = core::mem::size_of::<Crc32Hash>();
const PACKET_LEN_SIZE: usize = core::mem::size_of::<PacketLen>();

// the indices of the headers
const PACKET_LEN_START_IDX: usize = 0;
const PACKET_LEN_END_IDX: usize = PACKET_LEN_SIZE;

const CRC32_START_IDX: usize = PACKET_LEN_END_IDX;
const CRC32_END_IDX: usize = CRC32_START_IDX + CRC32_HASH_SIZE;

const PACKET_ID_START_IDX: usize = CRC32_END_IDX;
const PACKET_ID_END_IDX: usize = PACKET_ID_START_IDX + PACKET_ID_SIZE;

const ACK_ID_START_IDX: usize = PACKET_ID_END_IDX;
const ACK_ID_END_IDX: usize = ACK_ID_START_IDX + ACK_ID_SIZE;

const ACK_BITFIELD_START_IDX: usize = ACK_ID_END_IDX;
const ACK_BITFIELD_END_IDX: usize = ACK_BITFIELD_START_IDX + ACK_BITFIELD_SIZE;

/// The size of the header.
const HEADER_SIZE: usize =
    ACK_ID_SIZE + ACK_BITFIELD_SIZE + CRC32_HASH_SIZE + PACKET_ID_SIZE + PACKET_LEN_SIZE;

/// The max packet size to deal with fragmentation.
const MAX_PACKET_SIZE: usize = 420;
/// The maximum size of the contents for the packet.
const MAX_PACKET_CONTENTS: usize = MAX_PACKET_SIZE - HEADER_SIZE;

/// A packet that can be sent over the wire.
/// The packet itself is serialized and deserialized in the little endian format
/// so as to preserve cross platform determinism.
#[derive(Clone, Debug, PartialEq)]
pub struct Packet {
    /// The last packet to ack.
    ack: PacketId,
    /// Previous acks. If the Nth bit is set, that means `ack - n` is acked.
    acks: AckBitfield,
    /// The total contents of the packet. Includes header + user content.
    bytes: [u8; MAX_PACKET_SIZE],
    /// CRC32 hash
    crc32hash: Crc32Hash,
    /// The current length of the packet's bytes.
    len: usize,
    /// The maximum allowed length of the packet.
    packet_capacity: usize,
    /// The packet id.
    packet_id: PacketId,
}

impl Packet {
    /// The max number of packets that can be acked.
    /// Since a u32 is used for storing the acks, we'll limit it to that many values.
    pub(crate) const MAX_ACKS: packet_id::Inner = 32;

    /// The max number of ack'd packets we'll return.
    pub(crate) const ACKD_PACKET_SIZE: usize = 1 + Self::MAX_ACKS as usize;

    /// Acks the given packet if possible.
    pub(crate) fn ack(&mut self, packet: PacketId) {
        // Only set a bit if it's not the original ack
        if packet != self.ack {
            let diff = self.ack - packet;

            // If difference is greater than the max ack window or is the same ack, ignore.
            if diff.inner() <= Self::MAX_ACKS {
                let ack = 1 << (diff.inner() - 1);
                self.acks |= ack;
            }
        }
    }

    /// Returns the id of the packet that was acked
    pub(crate) fn ack_id(&self) -> PacketId {
        self.ack
    }

    /// Returns an array of all ackd packets.
    pub fn ackd_packets(&self) -> [(PacketId, AckStatus); Self::ACKD_PACKET_SIZE] {
        let mut acks = [(0.into(), AckStatus::NotAckd); Self::ACKD_PACKET_SIZE];
        acks[0] = (self.ack_id(), AckStatus::Ackd);

        for idx in 0..Self::MAX_ACKS {
            let shifted_value = if idx == 0 { 1 } else { 1 << idx };

            let is_valid = self.acks & shifted_value != 0;
            let insert_idx = (idx + 1) as usize;
            let ack_status = if is_valid {
                AckStatus::Ackd
            } else {
                AckStatus::NotAckd
            };

            acks[insert_idx] = (self.ack_id().decrement_n(idx as u16 + 1), ack_status);
        }

        acks
    }

    /// Returns an empty buffer that may be used for writing to a packet.
    pub(crate) fn buffer() -> [u8; MAX_PACKET_SIZE] {
        [0; MAX_PACKET_SIZE]
    }

    /// Returns the packets bytes.
    /// NOTE: this does not perform serialization, that is done
    /// as a packet is written.
    /// `write_header()` should also be called before returning the
    /// packet, as that way the CRC32 sumcheck is added in.
    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes[0..self.len]
    }

    /// Returns the contents of the packet.
    pub fn contents(&self) -> &[u8] {
        &self.bytes[HEADER_SIZE..self.len]
    }

    /// Attempts to deserialize the packet
    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self, PacketErr> {
        // Ensure we don't overflow
        if bytes.len() > MAX_PACKET_SIZE {
            return Err(PacketErr::WouldOverflow);
        }

        // Read in the bytes
        let mut packet = Packet::new(0.into(), 0.into(), MAX_PACKET_SIZE);
        for (idx, byte) in bytes.iter().enumerate() {
            packet.bytes[idx] = *byte;
        }

        // Now deserialize all things
        let packet_len = PacketLen::from_le_bytes([
            packet.bytes[PACKET_LEN_START_IDX],
            packet.bytes[PACKET_LEN_END_IDX - 1],
        ]);

        let packet_id: PacketId = packet_id::Inner::from_le_bytes([
            packet.bytes[PACKET_ID_START_IDX],
            packet.bytes[PACKET_ID_END_IDX - 1],
        ])
        .into();

        let ack: PacketId = packet_id::Inner::from_le_bytes([
            packet.bytes[ACK_ID_START_IDX],
            packet.bytes[ACK_ID_END_IDX - 1],
        ])
        .into();

        let acks: AckBitfield = AckBitfield::from_le_bytes([
            packet.bytes[ACK_BITFIELD_START_IDX],
            packet.bytes[ACK_BITFIELD_START_IDX + 1],
            packet.bytes[ACK_BITFIELD_START_IDX + 2],
            packet.bytes[ACK_BITFIELD_END_IDX - 1],
        ])
        .into();

        let crc32hash: Crc32Hash = Crc32Hash::from_le_bytes([
            packet.bytes[CRC32_START_IDX],
            packet.bytes[CRC32_START_IDX + 1],
            packet.bytes[CRC32_START_IDX + 2],
            packet.bytes[CRC32_END_IDX - 1],
        ]);

        // Build up packet
        packet.ack = ack;
        packet.acks = acks;
        packet.crc32hash = crc32hash;
        packet.len = packet_len as usize;
        packet.packet_id = packet_id;

        // Now verify the crc32 matches
        packet.zero_crc32_bytes();
        if crc32fast::hash(&packet.bytes()) != packet.crc32hash {
            Err(PacketErr::ChecksumMismatch)
        } else {
            Ok(packet)
        }
    }

    /// Returns the id of the packet
    pub fn id(&self) -> PacketId {
        self.packet_id
    }

    /// Returns the length of the packet in bytes.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Creates a new packet
    pub(crate) fn new(packet_id: PacketId, ack: PacketId, packet_capacity: usize) -> Self {
        Self {
            ack,
            acks: 0,
            bytes: [0; MAX_PACKET_SIZE],
            crc32hash: 0,
            packet_id,
            len: HEADER_SIZE,
            packet_capacity,
        }
    }

    /// Sets the ack id and clears the acks.
    pub(crate) fn set_ack(&mut self, ack: PacketId) {
        self.acks = 0;
        self.ack = ack;
    }

    /// Writes the given byte to the packet.
    /// It will be converted to little endian before serialization.
    /// Returns the number of bytes remaining for the packet.
    pub fn write(&mut self, byte: u8) -> Result<usize, PacketErr> {
        if self.len() >= self.packet_capacity {
            Err(PacketErr::WouldOverflow)
        } else {
            self.bytes[self.len] = byte.to_le();
            self.len += 1;

            Ok(self.packet_capacity - self.len)
        }
    }

    /// Writes the header to the packet.
    /// This should be called before any serialization happens.
    pub(crate) fn write_header(&mut self) {
        // Write packet len
        {
            let packet_len = (self.len as PacketLen).to_le_bytes();
            let mut idx = PACKET_LEN_START_IDX;
            for byte in packet_len {
                self.bytes[idx] = byte;
                idx += 1;
            }
        }

        // Write packet id
        {
            let packet_id = self.packet_id.inner().to_le_bytes();
            let mut idx = PACKET_ID_START_IDX;
            for byte in packet_id {
                self.bytes[idx] = byte;
                idx += 1;
            }
        }

        // Write ack id
        {
            let ack_id = self.ack.inner().to_le_bytes();
            let mut idx = ACK_ID_START_IDX;
            for byte in ack_id {
                self.bytes[idx] = byte;
                idx += 1;
            }
        }

        // Write ack bitfields
        {
            let ack_bitfield = self.acks.to_le_bytes();
            let mut idx = ACK_BITFIELD_START_IDX;
            for byte in ack_bitfield {
                self.bytes[idx] = byte;
                idx += 1;
            }
        }

        // First zero out all crc32 bytes
        self.zero_crc32_bytes();

        // Hash the contents
        let hash = crc32fast::hash(&self.bytes());

        // Write CRC32 hash
        {
            let hash = hash.to_le_bytes();
            let mut idx = CRC32_START_IDX;
            for byte in hash {
                self.bytes[idx] = byte;
                idx += 1;
            }
        }
    }

    /// Zeroes out all CRC32 bytes.
    pub(crate) fn zero_crc32_bytes(&mut self) {
        for idx in CRC32_START_IDX..CRC32_END_IDX {
            self.bytes[idx] = 0;
        }
    }
}

pub(crate) fn make_acks(id: PacketId) -> [(PacketId, AckStatus); Packet::ACKD_PACKET_SIZE] {
    let mut acks = [(0.into(), AckStatus::NotAckd); Packet::ACKD_PACKET_SIZE];
    let mut ack = id.increment();
    for (id, _) in acks.iter_mut() {
        ack = ack.decrement();
        *id = ack;
    }

    acks
}

#[cfg(test)]
mod tests {
    use super::*;

    mod ack {
        use super::*;

        #[test]
        fn ack_packet_n1_sets_first_bit() {
            let ack = 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 1;

            packet.ack((ack - 1).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_2n_sets_second_bit() {
            let n = 2;
            let ack = 4444;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b_0010;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_4n_sets_fourth_bit() {
            let n = 4;
            let ack = packet_id::Inner::MAX;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b_1000;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_8n_sets_eighth_bit() {
            let n = 8;
            let ack = packet_id::Inner::MAX;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b_1000_0000;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_16n_sets_sixteenth_bit() {
            let n = 16;
            let ack = 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b_1000_0000_0000_0000;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_32n_sets_32nd_bit() {
            let n = 32;
            let ack = 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b_1000_0000_0000_0000_0000_0000_0000_0000;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_33n_does_nothing() {
            let n = 33;
            let ack = 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_packet_does_not_modify_existing() {
            let n = 2;
            let ack = 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let mut expected = packet.clone();
            expected.acks = 0b0011;

            packet.acks = expected.acks;

            packet.ack((ack - n).into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_greater_than_original_does_nothing() {
            let ack = 0;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let expected = packet.clone();

            packet.ack(1.into());
            assert_eq!(expected, packet);
        }

        #[test]
        fn ack_is_original_ack_does_nothing() {
            let ack = 0;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let original = packet.clone();

            packet.ack(ack.into());
            assert_eq!(original, packet);
        }

        #[test]
        fn ack_outside_window_does_nothing() {
            let ack = Packet::MAX_ACKS + 1;

            let mut packet = Packet::new(3.into(), ack.into(), 40);

            let original = packet.clone();

            packet.ack(0.into());
            assert_eq!(original, packet);
        }
    }

    describe!(ackd_packets => {


        #[test]
        fn ack_id_returns(){
            let ack: PacketId = 44.into();
            let packet = Packet::new(0.into(), ack, 333);

            let mut expected = make_acks(ack);
            expected[0].1 = AckStatus::Ackd;
            assert_eq!(expected, packet.ackd_packets());
        }

        #[test]
        fn adds_single_bitflag(){
            let ack: PacketId = 44.into();

            let mut packet = Packet::new(0.into(), ack, 333);
            let mut expected = make_acks(ack);

            // Set initial ack
            expected[0].1 = AckStatus::Ackd;
            expected[1].1 = AckStatus::Ackd;

            packet.ack(ack.decrement());

            assert_eq!(expected, packet.ackd_packets());
        }

        #[test]
        fn adds_two_bitflags(){
            let ack: PacketId = 44.into();

            let mut packet = Packet::new(0.into(), ack, 333);
            let mut expected = make_acks(ack);

            // Set initial ack
            expected[0].1 = AckStatus::Ackd;

            let ack_1 = ack.decrement();
            expected[1].1 = AckStatus::Ackd;
            packet.ack(ack_1);


            let ack_3 = ack.decrement().decrement().decrement();
            expected[3].1 = AckStatus::Ackd;
            packet.ack(ack_3);


            assert_eq!(expected, packet.ackd_packets());
        }

        #[test]
        fn returns_bit_flags(){
            let ack: PacketId = 44.into();

            for idx in 0..Packet::MAX_ACKS{
                let mut packet = Packet::new(0.into(), ack, 333);
                let mut expected = make_acks(ack);

                // Set initial ack
                expected[0].1 = AckStatus::Ackd;

                // Increment idx for next one
                let next_idx = idx + 1;

                // Now set a flag
                let next_ack = ack.decrement_n(next_idx);
                expected[next_idx as usize].1 = AckStatus::Ackd;
                packet.ack(next_ack);


                assert_eq!(expected, packet.ackd_packets());
            }
        }
    });

    mod bytes {
        use super::*;

        #[test]
        fn returns_expected() {
            let mut packet = Packet::new(0.into(), 22.into(), 33);
            let size = 10;
            for _ in 0..size {
                packet.write(3).unwrap();
            }

            assert_eq!(&packet.bytes[0..HEADER_SIZE + size], packet.bytes())
        }
    }

    mod contents {
        use super::*;

        #[test]
        fn returns_expected() {
            let mut packet = Packet::new(0.into(), 22.into(), 33);
            let size = 10;
            let mut bytes = vec![];
            for i in 0..size {
                packet.write(i as u8).unwrap();
                bytes.push(i as u8);
            }

            assert_eq!(&bytes, packet.contents())
        }
    }

    mod from_bytes {
        use super::*;
        fn packet(content_len: usize) -> Packet {
            let mut packet = Packet::new(34.into(), 37.into(), MAX_PACKET_SIZE);
            for _ in 0..content_len {
                packet.write(34).unwrap();
            }
            packet
        }

        #[test]
        fn would_overflow_returns_error() {
            let bytes = [0; MAX_PACKET_SIZE + 1];
            assert_eq!(Err(PacketErr::WouldOverflow), Packet::from_bytes(&bytes));
        }

        #[test]
        fn at_capacity_returns_expected() {
            let mut packet = packet(MAX_PACKET_CONTENTS);
            packet.write_header();

            let mut result = Packet::from_bytes(packet.bytes()).unwrap();

            // We don't actually care about the checksums,
            // as if it deserializes they pass.
            // Reset them for this test.
            packet.zero_crc32_bytes();
            result.crc32hash = 0;

            assert_eq!(packet.clone(), result);
        }

        #[test]
        fn less_than_capacity_returns_expected() {
            let mut packet = packet(33);
            packet.write_header();

            let mut result = Packet::from_bytes(packet.bytes()).unwrap();

            // We don't actually care about the checksums,
            // as if it deserializes they pass.
            // Reset them for this test.
            packet.zero_crc32_bytes();
            result.crc32hash = 0;

            assert_eq!(packet.clone(), result);
        }

        #[test]
        fn invalid_checksum_returns_error() {
            let mut packet = packet(33);
            packet.write_header();

            packet.bytes[HEADER_SIZE + 3] = 255;

            let result = Packet::from_bytes(packet.bytes());

            assert_eq!(Err(PacketErr::ChecksumMismatch), result);
        }
    }

    mod len {
        use super::*;

        #[test]
        fn new_packet_has_header_as_len() {
            let packet = Packet::new(0.into(), 0.into(), 33);
            assert_eq!(HEADER_SIZE, packet.len())
        }

        #[test]
        fn writing_modifies_len() {
            let mut packet = Packet::new(0.into(), 0.into(), 33);
            let num_writes = 13;
            for _ in 0..num_writes {
                packet.write(0).unwrap();
            }

            assert_eq!(HEADER_SIZE + num_writes, packet.len())
        }
    }

    mod new {
        use super::*;

        #[test]
        fn returns_expected() {
            let packet_capacity = 100;
            let packet_id: PacketId = 34.into();
            let ack_id: PacketId = 3333.into();

            let expected = Packet {
                ack: ack_id,
                acks: 0,
                bytes: [0; MAX_PACKET_SIZE],
                crc32hash: 0,
                len: HEADER_SIZE,
                packet_capacity,
                packet_id,
            };

            let actual = Packet::new(packet_id, ack_id, packet_capacity);
            assert_eq!(expected, actual);
        }
    }

    mod set_ack {
        use super::*;

        #[test]
        fn set_ack_clears_ackd_bits() {
            let ack = 3.into();
            let mut packet = Packet::new(0.into(), ack, 333);
            packet.ack(ack.decrement());
            packet.ack(ack.decrement().decrement());

            packet.set_ack(ack.increment());
            assert_eq!(ack.increment(), packet.ack);
            assert_eq!(0, packet.acks);
        }
    }

    mod write {
        use super::*;

        #[test]
        fn would_not_overflow_returns_remaining_len() {
            let capacity = 300;
            let mut packet = Packet::new(0.into(), 0.into(), capacity);
            let idx = packet.len();
            let result = packet.write(1);

            assert_eq!(Ok(packet.packet_capacity - HEADER_SIZE - 1), result);
            assert_eq!(HEADER_SIZE + 1, packet.len);
            assert_eq!(1, packet.bytes[idx]);
        }

        #[test]
        fn boundary_does_not_overflow() {
            let capacity = 300;
            let mut packet = Packet::new(0.into(), 0.into(), capacity);
            packet.len = capacity - 1;
            let idx = packet.len();
            let result = packet.write(1);

            assert_eq!(Ok(0), result);
            assert_eq!(capacity, packet.len);
            assert_eq!(1, packet.bytes[idx]);
        }

        #[test]
        fn overflow_does_nothing() {
            let capacity = 300;
            let mut packet = Packet::new(0.into(), 0.into(), capacity);
            packet.len = capacity;
            let result = packet.write(1);

            assert_eq!(Err(PacketErr::WouldOverflow), result);
        }

        #[test]
        fn packet_writes_little_endian() {
            let capacity = 300;
            let mut packet = Packet::new(0.into(), 0.into(), capacity);
            let idx = packet.len();

            let byte: u8 = 233_u8.to_be();

            let result = packet.write(byte);

            assert_eq!(Ok(packet.packet_capacity - HEADER_SIZE - 1), result);
            assert_eq!(HEADER_SIZE + 1, packet.len);
            assert_eq!(233_u8.to_le(), packet.bytes[idx]);
        }
    }

    mod write_header {
        use super::*;

        #[test]
        fn packet_len_is_written() {
            let mut packet = Packet::new(0.into(), 1.into(), 111);
            let writes = 33;
            for i in 0..writes {
                packet.write(i).unwrap();
            }

            packet.write_header();

            let packet_len: PacketLen = PacketLen::from_le_bytes([
                packet.bytes[PACKET_LEN_START_IDX],
                packet.bytes[PACKET_LEN_END_IDX - 1],
            ]);

            assert_eq!(HEADER_SIZE as PacketLen + writes as PacketLen, packet_len);
        }

        #[test]
        fn packet_id_is_written() {
            let id: PacketId = 3443.into();
            let mut packet = Packet::new(id, 1.into(), 111);

            packet.write_header();

            let packet_id = packet_id::Inner::from_le_bytes([
                packet.bytes[PACKET_ID_START_IDX],
                packet.bytes[PACKET_ID_END_IDX - 1],
            ]);

            assert_eq!(id.inner().to_le(), packet_id);
            assert_eq!(id, packet_id.into());
        }

        #[test]
        fn ack_id_is_written() {
            let ack: PacketId = 34343.into();
            let mut packet = Packet::new(0.into(), ack, 111);

            packet.write_header();

            let ack_id = packet_id::Inner::from_le_bytes([
                packet.bytes[ACK_ID_START_IDX],
                packet.bytes[ACK_ID_END_IDX - 1],
            ]);

            assert_eq!(ack.inner().to_le(), ack_id);
            assert_eq!(ack, ack_id.into());
        }

        #[test]
        fn bitfields_are_written() {
            let ack: PacketId = 34343.into();
            let mut packet = Packet::new(0.into(), ack, 111);

            packet.ack(ack.decrement());
            packet.ack(ack.decrement().decrement());
            packet.ack(ack.decrement().decrement().decrement().decrement());

            packet.write_header();

            let bitfield = AckBitfield::from_le_bytes([
                packet.bytes[ACK_BITFIELD_START_IDX],
                packet.bytes[ACK_BITFIELD_START_IDX + 1],
                packet.bytes[ACK_BITFIELD_START_IDX + 2],
                packet.bytes[ACK_BITFIELD_END_IDX - 1],
            ]);

            assert_eq!(packet.acks.to_le(), bitfield);
        }

        #[test]
        fn hash_is_written() {
            let ack: PacketId = 34343.into();
            let mut packet = Packet::new(0.into(), ack, 111);

            packet.ack(ack.decrement());
            packet.ack(ack.decrement().decrement());
            packet.ack(ack.decrement().decrement().decrement().decrement());

            let expected = {
                let mut clone = packet.clone();
                clone.write_header();
                clone.zero_crc32_bytes();
                crc32fast::hash(clone.bytes())
            };

            packet.write_header();

            let crc = Crc32Hash::from_le_bytes([
                packet.bytes[CRC32_START_IDX],
                packet.bytes[CRC32_START_IDX + 1],
                packet.bytes[CRC32_START_IDX + 2],
                packet.bytes[CRC32_END_IDX - 1],
            ]);

            assert_eq!(expected, crc);
        }
    }

    mod zero_crc32_bytes {
        use super::*;

        #[test]
        fn bytes_are_zeroed() {
            let mut packet = Packet::new(0.into(), 1.into(), 444);

            for i in CRC32_START_IDX..CRC32_END_IDX {
                packet.bytes[i] = i as u8;
            }

            packet.zero_crc32_bytes();

            for i in CRC32_START_IDX..CRC32_END_IDX {
                assert_eq!(0, packet.bytes[i])
            }
        }
    }
}
