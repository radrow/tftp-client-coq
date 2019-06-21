Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Compare.
Require Import Coq.Init.Nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
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
          | true => (ReadingFinished data, Some (ACK Client b_received))
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

Proposition read_error_after_error :
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

Proposition read_error_after_finito :
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

Proposition finito_after_small_block :
  forall (data : string) (st : read_state) (filename : string) (last_data : string) (block_sent : N16) (tout : N) (port : N),
    (N.of_nat (length data) < 512) /\ ((st = ReadingInit tout filename /\ block_sent = exist _ 1 eq_refl) \/ st = Reading tout port block_sent last_data) ->
    fst (handle_event_read (Packet Read port (DATA Server block_sent data)) st)
    = ReadingFinished data.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H0.
  * rewrite H0.
    rewrite H1.
    simpl.
    case_eq (N.of_nat (length data) <? 512).
    ** intuition.
    ** intro. exfalso. apply N.ltb_lt in H. congruence.
  * rewrite H0.
    simpl.
    case_eq (port =? port).
    ** intro.
       case_eq (N16_to_N block_sent =? N16_to_N block_sent).
       *** intro.
           case_eq (N.of_nat (length data) <? 512).
           **** intuition.
           **** intro. exfalso. apply N.ltb_lt in H. congruence.
       *** intro.
           exfalso.
           assert (N16_to_N block_sent = N16_to_N block_sent).
           trivial.
           apply N.eqb_eq in H3. congruence.
    ** intro.
       exfalso.
       assert (port = port). trivial. apply N.eqb_eq in H2. congruence.
Qed.

Proposition read_port_invariant : 
  forall (st : read_state) (port : N) (tout : N) (block : N16) (prev_data : string) (buf : string) (ev : event Read),
    st = Reading tout port block buf ->
    let mport := working_port_read (fst (handle_event_read ev st))
    in mport = None \/ mport = Some port.
Proof.
  intros. unfold mport.
  rewrite H.
  dependent destruction ev.
  * simpl.
    destruct (max_timeouts <=? tout);
      simpl; [left|right]; reflexivity.
  * dependent destruction p; simpl.
    ** case_eq (port =? n); intro.
       *** case_eq (N16_to_N block =? N16_to_N n0);
             case_eq (N.of_nat (length s0) <? 512); intros.
           **** simpl. left. reflexivity.
           **** destruct (N_to_N16 (N16_to_N n0 + 1)).
  + simpl. right. apply N.eqb_eq in H0. rewrite H0. reflexivity.
  + simpl. left. reflexivity.
    **** case_eq (N16_to_N n0 <? N16_to_N block); intro; simpl; [right|left]; reflexivity.
    **** case_eq (N16_to_N n0 <? N16_to_N block); intro; simpl; [right|left]; reflexivity.
    *** simpl. right. reflexivity.
    ** simpl. left. reflexivity.
Qed.


Proposition read_block_incr :
  forall (data : string) (st : read_state) (filename : string) (last_data : string) (block_sent : N16) (tout : N) (port : N) (next_block : N16),
    N.of_nat (length data) = 512 /\ st = Reading tout port block_sent last_data /\ N16_to_N block_sent + 1 = N16_to_N next_block /\ (N16_to_N block_sent + 1 < 256*256) ->
    fst (handle_event_read (Packet Read port (DATA Server block_sent data)) st)
    = Reading 0 port next_block data.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H1.
  rewrite H0.
  simpl.
  case_eq (port =? port); intro.
  * case_eq (N16_to_N block_sent =? N16_to_N block_sent); intro.
    ** case_eq (N.of_nat (length data) <? 512); intro.
       *** exfalso. apply N.ltb_lt in H5. zify. omega.
       *** cut (exists proof, N_to_N16 (N16_to_N block_sent + 1) = Some (exist _ (N16_to_N block_sent + 1) proof)).
           **** intro. destruct H6. rewrite H6. simpl.
                assert ((exist (fun n : N => n < 65536) (N16_to_N block_sent + 1) x) = next_block).
  + assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N block_sent + 1) x) = N16_to_N block_sent + 1).
    ++ destruct block_sent. simpl. reflexivity.
    ++ apply N16_to_N_injection. assumption.
  + rewrite H7. reflexivity.
           **** apply safe_N16_incr. assumption.
    ** assert (N16_to_N block_sent = N16_to_N block_sent). reflexivity.
       apply N.eqb_eq in H5. congruence.
  * assert (port = port). reflexivity.
    apply N.eqb_eq in H4. congruence.
Qed.


Proposition ack_received : forall (data : string) (st : read_state) (filename : string) (last_data : string) (block_sent : N16) (tout : N) (port : N),
    st = Reading tout port block_sent last_data /\  (N16_to_N block_sent + 1 < 256*256) -> 
    snd (handle_event_read (Packet Read port (DATA Server block_sent data)) st)
    = Some (ACK Client block_sent).
Proof.
  intros.
  destruct H.
  rewrite H.
  simpl.
  case_eq (port =? port).
  * intro.
    case_eq (N16_to_N block_sent =? N16_to_N block_sent).
    ** intro.
       case_eq (N.of_nat (length data) <? 512).
       *** intro.
           apply N.ltb_lt in H3.
           simpl.
           reflexivity.
       *** intros.
           cut (exists x, N_to_N16 (N16_to_N block_sent + 1) = Some x); revert H1.
           **** intros.
                destruct H4.
                rewrite H4.
                simpl.
                reflexivity.
           **** intro. apply safe_N16_incr_any. assumption.
    ** intro.
       exfalso.
       assert (N16_to_N block_sent = N16_to_N block_sent).
       trivial.
       apply N.eqb_eq in H3.
       congruence.
  * intro.
    exfalso.
    assert (port = port).
    trivial.
    apply N.eqb_eq in H2.
    congruence.
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
          in match N_to_N16 (N16_to_N prev_block + 1) with
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
                   then if String.eqb buf ""
                        then (WritingFinished, None)
                        else if N16_to_N block_acked =? (N16_to_N prev_block) + 1
                             then match N_to_N16 (N16_to_N prev_block + 1) with
                                  | None => overflow_err
                                  | Some bs16 => make_data port buf bs16
                                  end
                             else if N16_to_N block_acked =? N16_to_N prev_block
                                  then match N_to_N16 (N16_to_N prev_block + 1) with
                                  | None => overflow_err
                                  | Some bs16 => (st, Some (DATA Client bs16 prev_data))
                                  end
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


Proposition write_error_after_error :
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

Proposition write_error_after_finito :
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


Proposition finito_after_empty_data :
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (prev_data : string),
    st = Writing tout port prev_block prev_data "" ->
    fst (handle_event_write (Packet Write port (ACK Server prev_block)) st) = WritingFinished.
Proof.
  intros.
  rewrite H.
  simpl.
  case_eq (port =? port); intros.
  * case_eq (N16_to_N prev_block =? N16_to_N prev_block + 1); intros; simpl; reflexivity.
  * exfalso. assert ((port =? port) = true). apply N.eqb_eq. trivial. congruence.
Qed.

Proposition write_port_invariant : 
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (prev_data : string) (buf : string) (ev : event Write),
    st = Writing tout port prev_block prev_data buf ->
    let mport := working_port_write (fst (handle_event_write ev st))
    in mport = None \/ mport = Some port.
Proof.
  intros. unfold mport.
  rewrite H.
  dependent destruction ev.
  * simpl.
    destruct (max_timeouts <=? tout);
      simpl; [left|right]; reflexivity.
  * dependent destruction p.
    ** destruct buf.
       *** simpl.
           destruct (port =? n); simpl; [left|right]; reflexivity.
       *** simpl.
           case_eq (port =? n); intro.
           **** destruct (N16_to_N n0 =? N16_to_N prev_block + 1).
                + destruct (N_to_N16 (N16_to_N prev_block + 1)).
                  ++ destruct (N_to_N16 (N16_to_N n1 + 1));
                [apply N.eqb_eq in H0; rewrite <- H0; right | left];
                unfold working_port_write; destruct (pop_block (String a buf)); simpl; reflexivity.
                  ++ destruct (N_to_N16 (N16_to_N prev_block + 1)); simpl; left; reflexivity.
                + destruct (N16_to_N n0 =? N16_to_N prev_block).
                  ++ destruct (N_to_N16 (N16_to_N prev_block + 1));
                     simpl; [right|left]; reflexivity.
                  ++ destruct (N16_to_N n0 <? N16_to_N prev_block);
                       simpl; [right|left]; reflexivity.
           **** simpl. right. reflexivity.
    ** simpl. left. reflexivity.
Qed.


Proposition block_number_incr :
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (prev_data : string) (prev_buf : string) (next_block : N16),
    st = Writing tout port prev_block prev_data prev_buf /\ prev_buf <> "" /\
    N16_to_N prev_block + 2 < 256*256 /\ N16_to_N prev_block + 1 = N16_to_N next_block ->
    exists (new_data : string) (new_buf : string),
    fst (handle_event_write (Packet Write port (ACK Server next_block)) st) =
    Writing 0 port next_block new_data new_buf.
Proof.
  intros.
  destruct H; destruct H0; destruct H1.
  rewrite H.
  simpl.
  case_eq (port =? port); intro.
  * case_eq (String.eqb prev_buf ""); intro.
    ** apply String.eqb_eq in H4. congruence.
    ** case_eq (N16_to_N next_block =? N16_to_N prev_block + 1); intro.
       *** cut (exists proof, N_to_N16 (N16_to_N prev_block + 1) = Some (exist _ (N16_to_N prev_block + 1) proof)).
           **** intro.
                destruct H6.
                rewrite H6.
                cut (N16_to_N (exist (fun n : N => n < 256 * 256) (N16_to_N prev_block + 1) x) + 1 < 256*256).
  + intro. apply safe_N16_incr in H7. simpl.
    cut ( N16_to_N prev_block + 1 + 1 < 256 * 256).
    ++ intro.
       assert (exists xxx, N_to_N16 (N16_to_N prev_block + 1 + 1) = Some (exist _ (N16_to_N prev_block + 1 + 1) xxx)).
       +++ rewrite H2. rewrite H2 in H8.
           unfold N_to_N16. exists H8.
           cut (
               (fun pf : (N16_to_N next_block + 1 ?= 256 * 256) = Lt =>
                 Some (exist (fun n : N => n < 256 * 256) (N16_to_N next_block + 1) pf)) =
                 (fun pf : (N16_to_N next_block + 1 ?= 256 * 256) = Lt =>
                   Some (exist (fun n : N => n < 256 * 256) (N16_to_N next_block + 1) H8))
             ).
           ++++ intros ->.
                generalize (eq_refl ( N16_to_N next_block + 1 ?= 256 * 256)).
                revert H8.
                case_eq (N16_to_N next_block + 1 ?= 256 * 256);
                  intros; unfold N.lt in H1; congruence + reflexivity.
           ++++ extensionality pf.
                f_equal.
                f_equal.
                apply UIP_dec.
                decide equality.
       +++ destruct H9. rewrite H9. simpl.
           assert ((exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = next_block).
           ++++ assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = N16_to_N next_block).
  - assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = N16_to_N prev_block + 1).
    -- destruct N16_to_N; simpl; reflexivity.
    -- rewrite H10. assumption.
  - destruct next_block.
    revert H10.
    generalize ((exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x)).
    generalize (exist (fun n : N => n < 256 * 256) x1 l).
    simpl.
    remember N16_to_N_injection as XX.
    unfold N16 in XX.
    cut ( forall s s0 : {n : N | n < 256 * 256}, N16_to_N s0 = N16_to_N s -> s0 = s).
    -- simpl. intro. assumption.
    -- intuition.
       ++++ rewrite H10. destruct (pop_block prev_buf). simpl. exists s. exists s0. reflexivity.
    ++ zify. omega.
    + simpl. zify. omega.
      **** apply safe_N16_incr. zify. omega.
      *** do 2 eexists.
          case_eq (N16_to_N next_block =? N16_to_N prev_block); intro.
          **** exfalso. apply eq_sym in H2. apply N.eqb_eq in H2. congruence.
          **** case_eq (N16_to_N next_block <? N16_to_N prev_block); intro;
                 (exfalso; apply eq_sym in H2; apply N.eqb_eq in H2; congruence).
      * exfalso.
        assert (port = port). reflexivity.
        apply N.eqb_eq in H4.
        congruence.
        Unshelve.
        exact "".
        exact "".
Qed.


Proposition block_number_persist :
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (prev_data : string) (prev_buf : string),
    st = Writing tout port prev_block prev_data prev_buf /\ prev_buf <> "" /\
    N16_to_N prev_block + 1 < 256*256 ->
    fst (handle_event_write (Packet Write port (ACK Server prev_block)) st) =
    Writing tout port prev_block prev_data prev_buf.
  intros.
  destruct H; destruct H0.
  rewrite H.
  simpl.
  case_eq (port =? port); intro.
  * case_eq (String.eqb prev_buf ""); intro.
    ** apply String.eqb_eq in H3. congruence.
    ** case_eq (N16_to_N prev_block =? N16_to_N prev_block + 1); intro.
       *** assert (N16_to_N prev_block <> N16_to_N prev_block + 1).
           zify. omega. apply N.eqb_eq in H4. congruence.
       *** case_eq (N16_to_N prev_block =? N16_to_N prev_block); intro.
           **** assert (N16_to_N prev_block + 1 < 256*256).
  + zify. omega.
  + assert (exists proof, N_to_N16 (N16_to_N prev_block + 1) = Some (exist _ (N16_to_N prev_block + 1) proof)).
    ++ apply safe_N16_incr. assumption.
    ++ destruct H7. rewrite H7. simpl. reflexivity.
           **** assert (N16_to_N prev_block = N16_to_N prev_block). reflexivity.
                apply N.eqb_eq in H6. exfalso. congruence.
  * simpl. assert (port =? port = true). apply N.eqb_eq. reflexivity. congruence.
Qed.

Proposition send_next_after_ACK :
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (prev_data : string) (prev_buf : string) (next_block : N16) (sending_block : N16) (new_data : string),
    st = Writing tout port prev_block prev_data prev_buf /\ prev_buf <> "" /\ new_data = fst (pop_block prev_buf) /\ (N16_to_N next_block + 1 = N16_to_N sending_block) /\
    N16_to_N prev_block + 2 < 256*256 /\ N16_to_N prev_block + 1 = N16_to_N next_block ->
    exists (new_data : string) (new_buf : string),
    snd (handle_event_write (Packet Write port (ACK Server next_block)) st) =
    Some (DATA Client sending_block new_data).
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3.
  rewrite H.
  simpl.
  assert (port = port). reflexivity.
  apply N.eqb_eq in H5.
  rewrite H5.
  case_eq (String.eqb prev_buf ""); intro.
  * apply String.eqb_eq in H6. congruence.
  * apply eq_sym in H4. apply N.eqb_eq in H4.
    case_eq (N16_to_N next_block =? N16_to_N prev_block + 1); intro.
    ** assert (N16_to_N prev_block + 1 < 256 * 256). zify. omega.
       revert H8.
       cut (exists proof, N_to_N16 (N16_to_N prev_block + 1) = Some (exist _ (N16_to_N prev_block + 1) proof)).
       *** intro.
           destruct H8.
           rewrite H8.
           cut (N16_to_N (exist (fun n : N => n < 256 * 256) (N16_to_N prev_block + 1) x) + 1 < 256*256).
  + intro. apply safe_N16_incr in H9. simpl.
    cut ( N16_to_N prev_block + 1 + 1 < 256 * 256).
    ++ intro.
       assert (exists xxx, N_to_N16 (N16_to_N prev_block + 1 + 1) = Some (exist _ (N16_to_N prev_block + 1 + 1) xxx)).
       +++ apply N.eqb_eq in H4. rewrite <- H4. rewrite <- H4 in H10.
           unfold N_to_N16. exists H10.
           cut (
               (fun pf : (N16_to_N next_block + 1 ?= 256 * 256) = Lt =>
                 Some (exist (fun n : N => n < 256 * 256) (N16_to_N next_block + 1) pf)) =
                 (fun pf : (N16_to_N next_block + 1 ?= 256 * 256) = Lt =>
                   Some (exist (fun n : N => n < 256 * 256) (N16_to_N next_block + 1) H10))
             ).
           ++++ intros ->.
                generalize (eq_refl ( N16_to_N next_block + 1 ?= 256 * 256)).
                revert H10.
                case_eq (N16_to_N next_block + 1 ?= 256 * 256);
                  intros; unfold N.lt in H1; congruence + reflexivity.
           ++++ extensionality pf.
                f_equal.
                f_equal.
                apply UIP_dec.
                decide equality.
       +++ destruct H11. rewrite H11. simpl.
           assert ((exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = next_block).
           ++++ assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = N16_to_N next_block).
  - assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = N16_to_N prev_block + 1).
    -- destruct N16_to_N; simpl; reflexivity.
    -- rewrite H12. apply N.eqb_eq in H4. apply eq_sym in H4. assumption.
  - destruct next_block.
    revert H12.
    generalize ((exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x)).
    generalize (exist (fun n : N => n < 256 * 256) x1 l).
    simpl.
    remember N16_to_N_injection as XX.
    unfold N16 in XX.
    cut ( forall s s0 : {n : N | n < 256 * 256}, N16_to_N s0 = N16_to_N s -> s0 = s).
    -- simpl. intro. assumption.
    -- intuition.
       ++++ rewrite H12. destruct (pop_block prev_buf). simpl. exists s. exists s0.
            assert ( N_to_N16 (N16_to_N prev_block + 1 + 1) =
                     Some (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1 + 1) x0)
                   ).
            rewrite H11. zify. simpl. reflexivity.
            cut (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1 + 1) x0) =
                  N16_to_N sending_block
                ).
  - intro.
    assert (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1 + 1) x0 =
            sending_block).
    -- revert H15. apply N16_to_N_injection.
    -- rewrite H16. reflexivity.
  - rewrite <- H2. apply N.eqb_eq in H7. rewrite H7.
    destruct prev_block. simpl. reflexivity.
  ++ zify. omega.
    + simpl. zify. omega.
      *** apply safe_N16_incr. zify. omega.
    ** congruence.
Qed.

Proposition resend_after_prev_ack :
  forall (st : write_state) (port : N) (tout : N) (prev_block : N16) (next_block : N16) (prev_data : string) (prev_buf : string),
    st = Writing tout port prev_block prev_data prev_buf /\ prev_buf <> "" /\
    N16_to_N prev_block + 1 < 256*256 /\ N16_to_N prev_block + 1 = N16_to_N next_block ->
    snd (handle_event_write (Packet Write port (ACK Server prev_block)) st) =
    Some (DATA Client next_block prev_data).
  intros.
  destruct H; destruct H0; destruct H1.
  rewrite H.
  simpl.
  case_eq (port =? port); intro.
  * case_eq (String.eqb prev_buf ""); intro.
    ** apply String.eqb_eq in H4. congruence.
    ** case_eq (N16_to_N prev_block =? N16_to_N prev_block + 1); intro.
       *** assert (N16_to_N prev_block <> N16_to_N prev_block + 1).
           zify. omega. apply N.eqb_eq in H5. congruence.
       *** case_eq (N16_to_N prev_block =? N16_to_N prev_block); intro.
           **** simpl.
                assert (exists proof, N_to_N16 (N16_to_N prev_block + 1) = Some (exist _ (N16_to_N prev_block + 1) proof)).
    ++ apply safe_N16_incr. assumption.
    ++ destruct H7. rewrite H7. simpl.
       assert (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x = next_block).
       +++ assert (N16_to_N (exist (fun n : N => n < 65536) (N16_to_N prev_block + 1) x) = N16_to_N next_block).
           ++++ assumption.
           ++++ apply N16_to_N_injection. assumption.
       +++ rewrite H8. simpl. reflexivity.
       **** assert (N16_to_N prev_block = N16_to_N prev_block). reflexivity.
            apply N.eqb_eq in H7. exfalso. congruence.
  * simpl. assert (port =? port = true). apply N.eqb_eq. reflexivity. congruence.
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
