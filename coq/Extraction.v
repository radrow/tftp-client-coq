Require Import ExtrOcamlString.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlIntConv.

Require Import Helpers.
Require Import Packet.
Require Import TFTP.

Extraction Language OCaml.
Set Extraction Optimize.

Extraction Blacklist String.
Extraction "TFTP"
           init_read_packet_serialized
           init_write_packet_serialized
           init_read_state
           init_write_state
           handle_unparsed_event_read
           handle_unparsed_event_write
           n_of_int
           int_of_n
.
