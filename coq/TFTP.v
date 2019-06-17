Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Compare.
Require Import Program.

Require Import Packet.
Require Import Helpers.


Open Scope string_scope.
Open Scope nat_scope.


Definition max_timeouts : N := 5.


Inductive unparsed_event : Set :=
| UTimeout : unparsed_event
| UPacket : N -> string -> unparsed_event
.


Inductive event : mode -> Set :=
| Timeout : forall m, event m
| Packet : forall m, N -> packet Server m -> event m
.


Inductive read_state : Set :=
(* timeouts, filename *)
| ReadingInit : N -> string -> read_state
(* timouts, port, block waiting for, read data*)
| Reading : N -> N -> N16 -> string -> read_state
| ReadingFinished : string -> read_state
| ReadingError : error -> string -> read_state
.

Definition working_port_read (st : read_state) : option N :=
  match st with
  | Reading _ p _ _ => Some p
  | _ => None
  end.

Definition init_read_state (filename : string) : read_state := ReadingInit 0 filename.
Definition init_read_packet (filename : string) : packet Client Read := RRQ filename.
Definition init_read_packet_serialized (filename : string) :=
  serialize_packet (init_read_packet filename).


Inductive write_state : Set :=
(* timeouts, filename, buffer *)
| WritingInit : N -> string -> string -> write_state
(* timouts, port, last acked block, prev_data, buffer*)
| Writing : N -> N -> N16 -> string -> string -> write_state
| WritingFinished : write_state
| WritingError : error -> string -> write_state
.

Definition working_port_write (st : write_state) : option N :=
  match st with
  | Writing _ p _ _ _ => Some p
  | _ => None
  end.

Definition init_write_state (filename : string) (data : string) : write_state :=
  WritingInit 0 filename data.
Definition init_write_packet (filename : string) : packet Client Write := WRQ filename.
Definition init_write_packet_serialized (filename : string) :=
  serialize_packet (init_write_packet filename).


Definition state (m : mode) : Set :=
  match m with
  | Read => read_state
  | Write => write_state
  end.


Fixpoint split_string_at (n : nat) (s : string) : (string * string) :=
  match s, n with
  | EmptyString, _ => (EmptyString, EmptyString)
  | _, O => (EmptyString, s)
  | String c rest, S nn =>
    let (popres, leftres) := split_string_at nn rest
    in (String c popres, leftres)
  end.

Theorem split_string_at_length : forall (s : string) (n : nat),
    let (s1, s2) := split_string_at n s in String.length s1 <= n.
Proof.
  induction s.
  * destruct n; simpl; omega.
  * destruct n.
    ** simpl; omega.
    ** simpl.
       remember (split_string_at n s) as X.
       destruct X.
       simpl.
       pose proof (IHs n).
       rewrite <- HeqX in H.
       omega.
Qed.

Theorem split_string_at_sum : forall (s : string) (n : nat),
    let (s1, s2) := split_string_at n s in String.append s1 s2 = s.
Proof.
  induction s.
  * destruct n; simpl; trivial.
  * destruct n.
    ** simpl; trivial.
    ** simpl.
       remember (split_string_at n s) as X.
       destruct X.
       simpl.
       pose proof (IHs n).
       rewrite <- HeqX in H.
       rewrite H.
       trivial.
Qed.

Definition pop_block (s : string) : (string * string) := split_string_at 512 s.


Open Scope N_scope.

Definition handle_event_read (ev : event Read) (st : state Read) :
  (state Read * option (packet Client Read)).
  refine (
      let timeout_err := (ReadingError NotDefined "Timeout", None) in
      let block_ord_err := (ReadingError NotDefined "Bad block order",
                            Some (ERROR Client Read IllegalOP "Bad block order")) in
      let make_ack port data b_received :=
          match N_of_nat (String.length data) <? 512 with
          | true => (ReadingFinished data, None)
          | false =>
            match N_to_N16 (N16_to_N b_received + 1) with
            | None => (ReadingError NotDefined "Block number overflow",
                      Some (ERROR Client Read NotDefined "Block number overflow"))
            | Some bs => (Reading 0 port bs data,
                         Some (ACK Client b_received))
            end
          end in
      match ev with
      | Timeout Read =>
        match st with
        | ReadingInit timeouts filename =>
          if max_timeouts <=? timeouts
          then timeout_err
          else (ReadingInit (timeouts + 1) filename,
                Some (init_read_packet filename))
        | Reading timeouts port block rdata =>
          if max_timeouts <=? timeouts
          then timeout_err
          else (Reading (timeouts + 1) port block rdata,
                Some (ACK Client block))
        | _ => (ReadingError NotDefined "Timeout after finish", None)
        end
      | Packet Read port p =>
        match p in packet s m return s = Server -> m = Read -> (state Read * option (packet Client Read)) with
        | DATA Server block_sent data =>
          fun _ _ =>
            match st with
            | ReadingInit _ _ =>
              if N16_to_N block_sent =? 1
              then make_ack port data (exist _ 1 eq_refl)
              else block_ord_err
            | Reading _ reading_port block_next _ =>
              if reading_port =? port
              then if N16_to_N block_next =? N16_to_N block_sent
                   then make_ack port data block_sent
                   else if N16_to_N block_sent <? N16_to_N block_next
                        then (st, None)
                        else block_ord_err
              else (st, None)
            | ReadingFinished _ => (ReadingError IllegalOP "Data after finish", None)
            | ReadingError _ _ => (st, None)
            end
        | ERROR Server Read err msg => fun _ _ => (ReadingError err msg, None)
        | _ => _
        end eq_refl eq_refl
      end
    );
    [ | | |destruct s| | ]; congruence.
Defined.

Fact read_error_after_error :
  forall (ev : event _) (er_in : error) (msg_in : string),
  exists (er_out : error) (msg_out : string),
    fst (handle_event_read ev (ReadingError er_in msg_in)) = ReadingError er_out msg_out.
Proof.
  intros.
  dependent destruction ev.
  * simpl; eexists; eexists; trivial.
  * dependent destruction p.
    ** simpl. do 2 eexists. auto.
    ** simpl. do 2 eexists. auto.
Qed.

Fact read_error_after_finito :
  forall (ev : event _) (last_data : string),
  exists (er_out : error) (msg_out : string),
    fst (handle_event_read ev (ReadingFinished last_data)) = ReadingError er_out msg_out.
Proof.
  intros.
  dependent destruction ev.
  * simpl; eexists; eexists; trivial.
  * dependent destruction p.
    ** simpl. do 2 eexists. auto.
    ** simpl. do 2 eexists. auto.
Qed.


Definition handle_unparsed_event_read (ev : unparsed_event) (st : read_state): (read_state * option (string * option N)) :=
  let pev :=
      match ev with
      | UTimeout => Some (Timeout Read)
      | UPacket port str =>
        match run_deserializer str (finalize_deserializer deserialize_packet) with
        | None => None
        | Some p => Some (Packet Read port p)
        end
      end
  in match pev with
     | None =>
       (st, Some (serialize_packet (ERROR Client Read IllegalOP "No parse"), working_port_read st))
     | Some e =>
       let (new_st, p_send) := handle_event_read e st
       in match p_send with
          | None => (new_st, None)
          | Some p_ser => (new_st, Some (serialize_packet p_ser, working_port_read new_st))
          end
     end.


Definition handle_event_write (ev : event Write) (st : state Write) :
  (state Write * option (packet Client Write)).
  refine (
      let timeout_err := (WritingError NotDefined "Timeout",
                          Some (ERROR Client Write NotDefined "Timeout")) in
      let block_ord_err := (WritingError NotDefined "Bad block order",
                            Some (ERROR Client Write IllegalOP "Bad block order")) in
      let overflow_err := (WritingError NotDefined "Block number overflow",
                           Some (ERROR Client Write NotDefined "Block number overflow")) in
      let make_data port buf prev_block :=
          let (data, rest_buf) := pop_block buf
          in if String.eqb data ""
             then (WritingFinished, None)
             else match N_to_N16 (N16_to_N prev_block + 1) with
                  | Some next_block => ( Writing 0 port prev_block data rest_buf,
                                        Some (DATA Client next_block data)
                                      )
                  | None => overflow_err
                  end in
      match ev with
           | Timeout Write =>
             match st with
             | WritingInit timeouts filename data =>
               if max_timeouts <=? timeouts
               then timeout_err
               else (WritingInit (timeouts + 1) filename data,
                     Some (init_write_packet filename))
             | Writing timeouts port block prev_data rdata =>
               if max_timeouts <=? timeouts
               then timeout_err
               else (Writing (timeouts + 1) port block prev_data rdata,
                     Some (DATA Client block prev_data))
             | _ => (WritingError NotDefined "Timeout after finish", None)
             end
           | Packet Write port p => 
             match p in packet s m
                   return s = Server -> m = Write -> (state Write * option (packet Client Write))
             with
             | ACK Server block_acked =>
               fun _ _ =>
                 match st with
                 | WritingInit _ _ buf =>
                   if N16_to_N block_acked =? 0
                   then make_data port buf (exist _ 0 eq_refl) 
                   else block_ord_err
                 | Writing _  writing_port prev_block prev_data buf =>
                   if writing_port =? port
                   then if N16_to_N block_acked =? (N16_to_N prev_block) + 1
                        then match N_to_N16 (N16_to_N prev_block + 1) with
                             | None => (WritingError NotDefined "Block number overflow",
                                       Some (ERROR Client Write NotDefined "Block number overflow"))
                             | Some bs16 => make_data port buf bs16
                             end
                        else if N16_to_N block_acked =? N16_to_N prev_block
                             then (st, Some (DATA Client block_acked prev_data))
                             else if N16_to_N block_acked <? N16_to_N prev_block
                                  then (st, None)
                                  else block_ord_err
                   else (st, None)
                 | WritingError _ _ => (st, None)
                 | WritingFinished => (WritingError NotDefined "ACK after finish", None)
                 end
             | ERROR Server Write err msg => fun _ _ => (WritingError err msg, None)
             | _ => _
             end eq_refl eq_refl
           end
         );
  [ |destruct s|destruct s| | | ]; congruence.
Defined.


Fact write_error_after_error :
  forall (ev : event _) (er_in : error) (msg_in : string),
  exists (er_out : error) (msg_out : string),
    fst (handle_event_write ev (WritingError er_in msg_in)) = WritingError er_out msg_out.
Proof.
  intros.
  dependent destruction ev.
  * simpl; eexists; eexists; trivial.
  * dependent destruction p.
    ** simpl. do 2 eexists. auto.
    ** simpl. do 2 eexists. auto.
Qed.

Fact write_error_after_finito :
  forall (ev : event _),
  exists (er_out : error) (msg_out : string),
    fst (handle_event_write ev WritingFinished) = WritingError er_out msg_out.
Proof.
  intros.
  dependent destruction ev.
  * simpl; eexists; eexists; trivial.
  * dependent destruction p.
    ** simpl. do 2 eexists. auto.
    ** simpl. do 2 eexists. auto.
Qed.


Definition handle_unparsed_event_write (ev : unparsed_event) (st : write_state): (write_state * option (string * option N)) :=
  let pev :=
      match ev with
      | UTimeout => Some (Timeout Write)
      | UPacket port str =>
        match run_deserializer str (finalize_deserializer deserialize_packet) with
        | None => None
        | Some p => Some (Packet Write port p)
        end
      end
  in match pev with
     | None =>
       (st, Some (serialize_packet (ERROR Client Write IllegalOP "No parse"), working_port_write st))
     | Some e =>
       let (new_st, p_send) := handle_event_write e st
       in match p_send with
          | None => (new_st, None)
          | Some p_ser => (new_st, Some (serialize_packet p_ser, working_port_write new_st))
          end
     end.