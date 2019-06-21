# tftp-client-coq

Simple TFTP client written in Coq (with IO handling in OCaml) as an assesment for MIMUW Computer-Aided Verification course. The program is written as state machine that reacts on two kinds of events: new packet income and timeout signal from OCaml.
The implementation should follow [RFC1350](https://tools.ietf.org/html/rfc1350) standard.

### Example usage

Downloading a file
```
ocamlrun main.byte -h 127.0.0.1 -m w file.txt
```

Uploading a file
```
ocamlrun main.byte -h 127.0.0.1 -m r file.txt
```

Proven/constrained stuff:

 - 16 bits bounds checks for datagram naturals
 - 8 bits bounds checks for ascii to nat conversions
 - Error code bounds and embedding
 - Packet sender control (for instance, there is no such thing as "WRQ sent by server")
 - Reading/Writing mode packet control (for instance, it is impossible to send WRQ in downloading mode)
 - Packet opcode bounds and embedding
 - Additional string appending and splitting lemmas
 - Reading/Writing mode event control (for instance, it is impossible to receive ACK in Reading mode)
 - Error state will persist regardless of events
 - Any event that occured after final state leads to an error state
 - Receiving block smaller than 512 bytes causes transition to final state
 - The communication port (beside initial) doesn't change
 - After receiving nth block that is not final client will wait for (n+1)th 
 - After receiving data block the correct ACK will be sent
 - After reaching the end of file the writing state becomes finalized
 - After receiving ACK last sent block and there is any data left, the next block will be sent and the state will move on
 - After receiving ACK for previous block the previous block will be retransmitted and the state will persist
 
 
