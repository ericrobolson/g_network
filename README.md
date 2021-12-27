A non-guaranteed communication layer. This does not provide encrypted communication or a verbose packet modification check. 

Based off of Tribes.

Roadmap
- [x] Implement packet id
- [x] Implement packet and acks
- [x] Implement packet writer
- [x] Implement checksums, use crc32?
- [x] Implement ring buffer
- [ ] Implement + test connection 
- [ ] https://gafferongames.com/post/reliable_ordered_messages/
- [ ] Implement sending over wire
- [ ] Implement configurable soak tests. Do one that's like 99.9% loss, one that's super laggy, etc.
- [ ] Implement different addresses/multiple peers and connections to other pcs
- [ ] Reexport things from the lib
