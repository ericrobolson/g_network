use crate::{
    packet::Packet,
    packet_id::{self, PacketId},
    ring_buffer::RingBuffer,
    socket::{Socket, SocketErr},
    types::*,
    PacketErr,
};

#[derive(Copy, Clone, Debug, PartialEq)]
enum DeliveryStatus {
    Delivered { notified: bool },
    Dropped { notified: bool },
    InFlight,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Notification {
    pub packet: PacketId,
    pub status: AckStatus,
}

const BUFFER_SIZE: usize = 1024;

/// An abstraction for a connection.
/// Inspired by https://gafferongames.com/post/reliable_ordered_messages/
pub struct Connection<TSocket>
where
    TSocket: Socket,
{
    received_packet_buffer: RingBuffer<bool, BUFFER_SIZE>,
    sent_packet_sequence_buffer: RingBuffer<Option<DeliveryStatus>, BUFFER_SIZE>,
    next_packet_id: PacketId,
    latest_ack_id: PacketId,
    next_id_to_poll: PacketId,
    /// The socket to use for sending data
    socket: TSocket,
    /// The capacity for the packet
    packet_capacity: usize,
}
impl<TSocket> Connection<TSocket>
where
    TSocket: Socket,
{
    /// Generates a new packet
    pub fn generate_packet(&mut self) -> Packet {
        let packet = Packet::new(
            self.next_packet_id,
            self.latest_ack_id,
            self.packet_capacity,
        );

        self.next_packet_id = self.next_packet_id.increment();
        packet
    }

    /// Read off the acks for the packet.
    fn handle_acks(&mut self, packet: &Packet) {
        // Mark the ackd packet as acked.
        self.sent_packet_sequence_buffer.insert(
            packet.ack_id().usize(),
            Some(DeliveryStatus::Delivered { notified: false }),
        );

        for (id, status) in packet.ackd_packets() {
            match status {
                AckStatus::Ackd => {
                    let status = self.sent_packet_sequence_buffer.get_mut(id.usize());

                    match status {
                        Some(DeliveryStatus::InFlight) => {
                            *status = Some(DeliveryStatus::Delivered { notified: false });
                        }
                        _ => {}
                    }
                }
                AckStatus::NotAckd => {}
            }
        }
    }

    /// Marks in flight packets outside of the ack window as dropped.
    fn mark_in_flight_as_dropped(&mut self) {
        let end_of_buffer = self.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
        let mut last_polled = self.next_id_to_poll;
        while last_polled != end_of_buffer {
            let idx = last_polled.usize();
            match self.sent_packet_sequence_buffer.get_mut(idx) {
                Some(status) => match status {
                    DeliveryStatus::InFlight => {
                        *status = DeliveryStatus::Dropped { notified: false }
                    }
                    _ => {}
                },
                None => {}
            }

            // go to next one
            last_polled = last_polled.increment();
        }
    }

    /// Creates a new connection
    pub fn new(packet_capacity: usize, socket: TSocket) -> Self {
        Self {
            /// This will ensure that we only start acking valid packets.
            latest_ack_id: PacketId::from(0).decrement(),
            /// This ensures that we start polling at the proper id.
            next_id_to_poll: packet_id::Inner::MAX.into(),
            /// The next packet to send off.
            next_packet_id: 0.into(),
            /// The capacity for each packet.
            packet_capacity,
            /// The received packets.
            received_packet_buffer: RingBuffer::new(),
            /// The sent packets and the delivery status.
            sent_packet_sequence_buffer: RingBuffer::new(),
            /// The socket handle.
            socket,
        }
    }

    /// Checks the connection for any notification events.
    /// Generally you will want to call this until a None is returned to ensure that the buffer doesn't
    /// have garbage clog it up.
    /// TODO: tests
    pub fn poll_notification(&mut self) -> Option<Notification> {
        let mut poll_id = self.next_id_to_poll;
        let mut next_id_to_poll = None;
        let mut notification = None;

        // Iterate through all the sent packets until we hit one that has a
        // delivery we should communicate.
        while self.latest_ack_id != poll_id && notification.is_none() {
            let idx = poll_id.usize();

            // Check the status if it exists
            if let Some(status) = self.sent_packet_sequence_buffer.get_mut(idx) {
                match status {
                    // We'll want to revisit this status later on, so we'll keep processing
                    // but mark the id if it's the next place to start at.
                    DeliveryStatus::InFlight => {
                        if next_id_to_poll.is_none() {
                            next_id_to_poll = Some(poll_id);
                        }
                    }
                    DeliveryStatus::Delivered { notified } => {
                        if *notified == false {
                            *notified = true;
                            notification = Some(Notification {
                                packet: poll_id,
                                status: AckStatus::Ackd,
                            });
                        }
                    }
                    DeliveryStatus::Dropped { notified } => {
                        if *notified == false {
                            *notified = true;
                            notification = Some(Notification {
                                packet: poll_id,
                                status: AckStatus::NotAckd,
                            });
                        }
                    }
                }
            }

            // Update the next id to start at
            if notification.is_some() && next_id_to_poll.is_none() {
                next_id_to_poll = Some(poll_id);
                break;
            }

            // Check the next one if nothing has happened
            poll_id = poll_id.increment();
        }

        // Update the next spot to poll at.
        if let Some(next_id_to_poll) = next_id_to_poll {
            self.next_id_to_poll = next_id_to_poll;
        }

        // If we're notifying that a packet was ackd or not, remove it so we don't duplicate the notification.
        if let Some(notification) = notification {
            self.sent_packet_sequence_buffer
                .insert(notification.packet.usize(), None);
        }

        notification
    }

    /// Attempts to receive a packet
    /// TODO: tests + implement
    pub fn receive(&mut self) -> Result<Option<Packet>, PacketErr> {
        // TODO: if notification queue is full, don't poll.
        let mut buff = Packet::buffer();
        match self.socket.read(&mut buff) {
            Ok(_) => {
                match Packet::from_bytes(&buff) {
                    Ok(packet) => {
                        // Read in sequence from the packet header
                        let ack_id = packet.ack_id();

                        // Walk between previous highest insert sequence and new one, clearing out entries.
                        // This ensures that old entries are nuked in the event of catastrophic packet loss.
                        let mut clear_id = self.latest_ack_id.increment();
                        while ack_id.is_greater(clear_id) {
                            self.received_packet_buffer.insert(clear_id.usize(), false);
                            clear_id = clear_id.increment();
                        }

                        // If sequence is more recent than the previous most recent received packet sequence number,
                        // update the most recent received packet sequence number.
                        // We'll only return the most recent packets.
                        let mut return_packet = false;
                        if ack_id.is_greater(self.latest_ack_id) {
                            self.latest_ack_id = ack_id;
                            return_packet = true;

                            // Insert an entry for this packet in the received packet sequence buffer
                            self.received_packet_buffer.insert(ack_id.usize(), true);
                        }

                        self.handle_acks(&packet);
                        self.mark_in_flight_as_dropped();

                        // Return the packet if it should be processed
                        if return_packet {
                            return Ok(Some(packet));
                        } else {
                            return Ok(None);
                        }
                    }
                    Err(_) => todo!(),
                }

                todo!()
            }
            Err(_) => todo!(),
        }
    }

    /// Sets the acks for the given packet based on the connection.
    fn set_acks(&self, packet: &mut Packet) {
        // Generate ack from last received packet number
        packet.set_ack(self.latest_ack_id);

        // Generate ack bits, starting at the packet just before the last ack id.
        let mut ack_packet = self.latest_ack_id.decrement();
        for _ in 0..Packet::MAX_ACKS {
            // Get the status from the buffer
            let ackd = self.received_packet_buffer.get(ack_packet.usize());
            if ackd {
                packet.ack(ack_packet);
            }

            // Decrement the packet to get the next bit
            ack_packet = ack_packet.decrement();
        }
    }

    /// Sends the given packet.
    pub fn send_packet(&mut self, mut packet: Packet) -> Result<(), SocketErr> {
        // Ack algorithm from https://gafferongames.com/post/reliable_ordered_messages/

        // Insert an entry for for the current send packet sequence number in the sent packet sequence buffer with
        // data indicating that it hasn’t been acked yet
        self.sent_packet_sequence_buffer
            .insert(packet.id().usize(), Some(DeliveryStatus::InFlight));

        // Set the acks on the packet
        self.set_acks(&mut packet);

        // Write the header
        packet.write_header();

        // Finally send it off
        match self.socket.send(packet.bytes()) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::make_acks;
    use crate::test_helpers::*;

    const CAPACITY: usize = 1000;
    fn conn() -> Connection<TestSocket> {
        Connection::new(CAPACITY, socket())
    }

    describe!(generate_packet => {
        #[test]
        fn adds_new_packet() {
            let mut conn = conn();
            let packet = conn.generate_packet();

            assert_eq!(packet.id().increment(), conn.next_packet_id);
        }
    });

    describe!(handle_acks => {
        #[test]
        fn marks_ack_id_as_ackd() {
            let mut conn = conn();
            let sent_packet = conn.generate_packet();
            conn.send_packet(sent_packet.clone()).unwrap();

            let packet = Packet::new(444.into(), sent_packet.id(), 333);
            conn.handle_acks(&packet);
            assert_eq!(Some(DeliveryStatus::Delivered{notified: false}), conn.sent_packet_sequence_buffer.get(packet.ack_id().usize()))
        }

        #[test]
        fn ack_bits_not_marked_as_delivered_if_status_is_none() {
            let mut conn = conn();
            let sent_packet = conn.generate_packet();
            conn.send_packet(sent_packet.clone()).unwrap();

            // Ensure that if status is None, it does nothing.
            let original_packet = Packet::new(444.into(), sent_packet.id(), 333);
            let mut ack_flag_id = original_packet.ack_id();
            for _ in 0..Packet::MAX_ACKS{
                let mut packet = original_packet.clone();
                ack_flag_id = ack_flag_id.decrement();
                packet.ack(ack_flag_id);

                conn.handle_acks(&packet);
                assert_eq!(None, conn.sent_packet_sequence_buffer.get(ack_flag_id.usize()))
            }
        }

        #[test]
        fn ack_bits_not_marked_as_delivered_if_status_is_some_delivered() {
            let mut conn = conn();
            let sent_packet = conn.generate_packet();
            conn.send_packet(sent_packet.clone()).unwrap();

            // Ensure that if status is None, it does nothing.
            let original_packet = Packet::new(444.into(), sent_packet.id(), 333);
            let mut ack_flag_id = original_packet.ack_id();
            for notified in [true, false]{
                for _ in 0..Packet::MAX_ACKS{
                    let mut packet = original_packet.clone();
                    ack_flag_id = ack_flag_id.decrement();
                    packet.ack(ack_flag_id);

                    let status = Some(DeliveryStatus::Delivered{notified});
                    *conn.sent_packet_sequence_buffer
                        .get_mut(ack_flag_id.usize()) = status;

                    conn.handle_acks(&packet);
                    assert_eq!(status, conn.sent_packet_sequence_buffer.get(ack_flag_id.usize()))
                }
            }
        }

        #[test]
        fn ack_bits_not_marked_as_delivered_if_status_is_some_dropped() {
            let mut conn = conn();
            let sent_packet = conn.generate_packet();
            conn.send_packet(sent_packet.clone()).unwrap();

            // Ensure that if status is None, it does nothing.
            let original_packet = Packet::new(444.into(), sent_packet.id(), 333);
            let mut ack_flag_id = original_packet.ack_id();
            for notified in [true, false]{
                for _ in 0..Packet::MAX_ACKS{
                    let mut packet = original_packet.clone();
                    ack_flag_id = ack_flag_id.decrement();
                    packet.ack(ack_flag_id);

                    let status = Some(DeliveryStatus::Dropped{notified});
                    *conn.sent_packet_sequence_buffer
                        .get_mut(ack_flag_id.usize()) = status;

                    conn.handle_acks(&packet);
                    assert_eq!(status, conn.sent_packet_sequence_buffer.get(ack_flag_id.usize()))
                }
            }
        }


        #[test]
        fn ack_bits_marked_as_delivered_if_status_is_some_in_flight() {
            let mut conn = conn();
            let sent_packet = conn.generate_packet();
            conn.send_packet(sent_packet.clone()).unwrap();

            // Ensure that if status is None, it does nothing.
            let original_packet = Packet::new(444.into(), sent_packet.id(), 333);
            let mut ack_flag_id = original_packet.ack_id();
            for _ in 0..Packet::MAX_ACKS{
                let mut packet = original_packet.clone();
                ack_flag_id = ack_flag_id.decrement();
                packet.ack(ack_flag_id);

                let status = Some(DeliveryStatus::InFlight);
                *conn.sent_packet_sequence_buffer
                    .get_mut(ack_flag_id.usize()) = status;

                conn.handle_acks(&packet);
                assert_eq!(Some(DeliveryStatus::Delivered{notified: false}), conn.sent_packet_sequence_buffer.get(ack_flag_id.usize()))
            }
        }
    });

    describe!(mark_in_flight_as_dropped => {
        #[test]
        fn no_inflight_does_nothing() {
            let mut conn = conn();

            let statuses = [
                DeliveryStatus::Delivered{notified: true},
                DeliveryStatus::Delivered{notified: false},
                DeliveryStatus::Dropped{notified: true},
                DeliveryStatus::Dropped{notified: false}
            ];

            for status in statuses{
                for idx in 0..BUFFER_SIZE{
                    *conn.sent_packet_sequence_buffer.get_mut(idx) = Some(status);
                }
                let expected = conn.sent_packet_sequence_buffer.clone();
                conn.mark_in_flight_as_dropped();

                assert_eq!(expected, conn.sent_packet_sequence_buffer);
            }
        }

        #[test]
        fn leaves_window_packets_alone() {
            let mut conn = conn();
            conn.latest_ack_id = 1.into();
            conn.next_id_to_poll = conn.latest_ack_id.decrement_n(66);

            let mut idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
            while idx != conn.latest_ack_id {
                conn.sent_packet_sequence_buffer.insert(idx.usize(), Some(DeliveryStatus::InFlight));
                idx = idx.increment();
            }

            let expected = conn.sent_packet_sequence_buffer.clone();
            conn.mark_in_flight_as_dropped();
            assert_eq!(expected, conn.sent_packet_sequence_buffer);
        }

        #[test]
        fn marks_single_packet_ouside_buffer_as_dropped() {
            let mut conn = conn();
            conn.latest_ack_id = 1.into();
            conn.next_id_to_poll = conn.latest_ack_id.decrement_n(66);

            // Set window ones
            let mut idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
            while idx != conn.latest_ack_id {
                conn.sent_packet_sequence_buffer.insert(idx.usize(), Some(DeliveryStatus::InFlight));
                idx = idx.increment();
            }

            let mut expected = conn.sent_packet_sequence_buffer.clone();
            // Now add some that should be dropped
            let end_idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
            let mut idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 2);
            conn.next_id_to_poll = idx;
            while idx != end_idx{
                conn.sent_packet_sequence_buffer.insert(idx.usize(), Some(DeliveryStatus::InFlight));
                expected.insert(idx.usize(), Some(DeliveryStatus::Dropped{notified: false}));
                idx = idx.increment();
            }
            conn.mark_in_flight_as_dropped();
            assert_eq!(expected, conn.sent_packet_sequence_buffer);
        }

        #[test]
        fn markes_packets_outside_of_window_as_dropped() {
            let mut conn = conn();
            conn.latest_ack_id = 1.into();
            conn.next_id_to_poll = conn.latest_ack_id.decrement_n(66);

            // Set window ones
            let mut idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
            while idx != conn.latest_ack_id {
                conn.sent_packet_sequence_buffer.insert(idx.usize(), Some(DeliveryStatus::InFlight));
                idx = idx.increment();
            }

            let mut expected = conn.sent_packet_sequence_buffer.clone();
            // Now add some that should be dropped
            let end_idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 1);
            let mut idx = conn.latest_ack_id.decrement_n(Packet::MAX_ACKS + 88);
            conn.next_id_to_poll = idx;
            while idx != end_idx{
                conn.sent_packet_sequence_buffer.insert(idx.usize(), Some(DeliveryStatus::InFlight));
                expected.insert(idx.usize(), Some(DeliveryStatus::Dropped{notified: false}));
                idx = idx.increment();
            }
            conn.mark_in_flight_as_dropped();
            assert_eq!(expected, conn.sent_packet_sequence_buffer);
        }
    });

    describe!(new => {
        #[test]
        fn returns_expected() {
            let conn = conn();

            assert_eq!(PacketId::from(0).decrement(),conn.latest_ack_id);
            assert_eq!(packet_id::Inner::MAX, conn.next_id_to_poll.inner());
            assert_eq!(PacketId::from(0), conn.next_packet_id);
            assert_eq!(CAPACITY, conn.packet_capacity);
            assert_eq!(RingBuffer::new(), conn.received_packet_buffer);
            assert_eq!(RingBuffer::new(), conn.sent_packet_sequence_buffer);
        }
    });

    describe!(poll_notification => {
        #[test]
        fn tests() {
            todo!("Test")
        }
    });

    describe!(receive => {
        #[test]
        fn tests() {
            todo!("Test")
        }
    });

    describe!(send_packet => {
        #[test]
        fn sets_packet_status_to_inflight() {
            let mut conn = conn();
            let packet = conn.generate_packet();

            let status_idx = packet.id().usize();
            conn.send_packet(packet).unwrap();
            assert_eq!(Some(DeliveryStatus::InFlight), conn.sent_packet_sequence_buffer.get(status_idx));
        }

        #[test]
        fn sets_ack_id_to_last_ack() {
            let mut conn = conn();
            let packet = conn.generate_packet();

            conn.send_packet(packet).unwrap();
            assert_eq!(conn.latest_ack_id, conn.socket.sent_packet().ack_id());
        }

        #[test]
        fn generates_ack_bits() {
            let mut conn = conn();
            let packet = conn.generate_packet();


            // Sets first ack id
            let ack = conn.latest_ack_id;
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            let mut expected = make_acks(ack);

            expected[0].1 = AckStatus::Ackd;

            // Sets second ack id
            let ack = ack.decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[1].1 = AckStatus::Ackd;

            // Sets fourth ack id
            let ack = ack.decrement().decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[3].1 = AckStatus::Ackd;

            conn.send_packet(packet).unwrap();

            let packet = conn.socket.sent_packet();

            assert_eq!(conn.latest_ack_id, packet.ack_id());
            assert_eq!(expected, packet.ackd_packets());
        }

        #[test]
        fn writes_header() {
            let mut conn = conn();
            let mut packet = conn.generate_packet();

            // Sets first ack id
            let ack = conn.latest_ack_id;
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            let mut expected = make_acks(ack);

            expected[0].1 = AckStatus::Ackd;

            // Sets second ack id
            let ack = ack.decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[1].1 = AckStatus::Ackd;

            // Sets fourth ack id
            let ack = ack.decrement().decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[3].1 = AckStatus::Ackd;


            conn.send_packet(packet.clone()).unwrap();

            conn.set_acks(&mut packet);
            packet.write_header();
            packet.zero_crc32_bytes();

            assert_eq!(packet.bytes(), conn.socket.sent_packet().bytes());
        }
    });

    describe!(set_acks => {

        #[test]
        fn sets_latest_id(){
            let mut conn = conn();
            let mut packet = conn.generate_packet();

            conn.set_acks(&mut packet);

            assert_eq!(conn.latest_ack_id, packet.ack_id());
        }
        #[test]
        fn sets_received_bits(){
            let mut conn = conn();
            let mut packet = conn.generate_packet();


            // Sets first ack id
            let ack = conn.latest_ack_id;
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            let mut expected = make_acks(ack);

            expected[0].1 = AckStatus::Ackd;

            // Sets second ack id
            let ack = ack.decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[1].1 = AckStatus::Ackd;

            // Sets fourth ack id
            let ack = ack.decrement().decrement();
            let ackd = conn.received_packet_buffer.get_mut(ack.usize());
            *ackd = true;
            expected[3].1 = AckStatus::Ackd;


            conn.set_acks(&mut packet);


            assert_eq!(conn.latest_ack_id, packet.ack_id());
            assert_eq!(expected, packet.ackd_packets());
        }

         #[test]
        fn sets_all_received_bits(){
            // Sets first ack id
            for i in 0..Packet::ACKD_PACKET_SIZE{
                let mut conn = conn();
                let mut packet = conn.generate_packet();


                // Set initial ack
                let ack = conn.latest_ack_id;
                let ackd = conn.received_packet_buffer.get_mut(ack.usize());
                *ackd = true;
                let mut expected = make_acks(ack);
                expected[0].1 = AckStatus::Ackd;

                // Set nth ack
                let ack = conn.latest_ack_id.decrement_n(i as u16);
                let ackd = conn.received_packet_buffer.get_mut(ack.usize());
                *ackd = true;
                expected[i].1 = AckStatus::Ackd;


                conn.set_acks(&mut packet);


                assert_eq!(conn.latest_ack_id, packet.ack_id());
                assert_eq!(expected, packet.ackd_packets());
            }
        }
    });
}
