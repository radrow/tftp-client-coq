Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Compare.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import ZArith.
Require Import Coq.Logic.Eqdep_dec.

Require Import Helpers.

Open Scope string_scope.
Open Scope N_scope.


Inductive error : Set :=
| NotDefined : error
| NotFound : error
| AccessViolation : error
| DiskFull : error
| IllegalOP : error
| UnknownTID : error
| FileExists : error
| NoSuchUser : error
.

Definition error_code (e : error) : N :=
  match e with
  | NotDefined => 0
  | NotFound => 1
  | AccessViolation => 2
  | DiskFull => 3
  | IllegalOP => 4
  | UnknownTID => 5
  | FileExists => 6
  | NoSuchUser => 7
  end.

Definition error_from_code (n : N) : (option error):=
  match n with
  | 0 => Some NotDefined
  | 1 => Some NotFound
  | 2 => Some AccessViolation
  | 3 => Some DiskFull
  | 4 => Some IllegalOP
  | 5 => Some UnknownTID
  | 6 => Some FileExists
  | 7 => Some NoSuchUser
  | _ => None
  end.

Fact error_code_range : forall (E : error), error_code(E) <= 7 /\ error_code(E) >= 0.
Proof.
  intros.
  destruct E; simpl; zify; omega.
Qed.

Theorem error_code_embedding : forall (e : error), error_from_code (error_code e) = Some e.
Proof.
  destruct e; trivial.
Qed.

Theorem code_error_embedding : forall (n : N),
    option_prop (fun e => error_code e = n) (error_from_code n).
Proof.
  destruct n; simpl; auto.
  do 3 (destruct p; simpl; auto).
Qed.


Inductive packet : sender -> mode -> Set :=
| RRQ : string -> packet Client Read
| WRQ : string -> packet Client Write
| DATA : forall (s : sender),
    N16 -> string -> packet s ( match s with
                              | Server => Read
                              | Client => Write
                              end )
| ACK : forall (s : sender),
    N16 -> packet s ( match s with
                     | Server => Write
                     | Client => Read
                     end )
| ERROR : forall (s:sender) (m:mode),
    error -> string -> packet s m
.

Definition opcode {s:sender} {m : mode} (p : packet s m) : N :=
  match p with
  | RRQ _ => 1
  | WRQ _ => 2
  | DATA _ _ _ => 3
  | ACK _ _ => 4
  | ERROR _ _ _ _ => 5
  end.

Fact opcode_range : forall (s : sender) (m : mode) (P : packet s m), opcode P <= 5 /\ opcode P >= 1.
Proof.
  intros.
  destruct P; simpl; zify; omega.
Qed.


Definition serialize_opcode {m : mode} (p : packet Client m) : string -> string :=
  fun s => String zero (String (ascii_of_N (opcode p)) s).


Fixpoint string_append (s1 : string) (s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c rest => String c (string_append rest s2)
  end.

Local Open Scope nat_scope.
Theorem string_append_length : forall (s1 : string) (s2 : string),
    String.length (string_append s1 s2) = String.length s1 + String.length s2.
Proof.
  intros.
  induction s1; simpl; auto.
Qed.
Local Close Scope nat_scope.

Theorem string_append_empty : forall (s : string), string_append s EmptyString = s.
Proof.
  intros.
  induction s.
  * trivial.
  * simpl.
    rewrite IHs.
    trivial.
Qed.

Definition serialize_string (ss : string) : string -> string :=
  fun s => string_append ss (String zero s).

Theorem extended_serialize_string : forall (c : ascii) (s : string),
    serialize_string (String c s) "" = String c (serialize_string s "").
  intros. induction s; trivial.
Qed.


Definition serialize_N16 (n : N16) : string -> string :=
  fun s => String (ascii_of_N (N16_to_N n / 256)) (String (ascii_of_N (N16_to_N n)) s).


Definition serialize_packet {m : mode} (p : packet Client m) : string :=
  serialize_opcode p
                   match p with
                   | RRQ file => serialize_string file (serialize_string "octet" "")
                   | WRQ file => serialize_string file (serialize_string "octet" "")
                   | DATA Client block data =>
                     serialize_N16 block data
                   | ACK Client block => serialize_N16 block (String zero "")
                   | ERROR Client _ code msg =>
                     String zero (String (ascii_of_N (error_code code)) (serialize_string msg ""))
                   end.


Definition deserializer (a : Set): Set := string -> (option a * string).


Definition bind_deserializer {a : Set} {b : Set}
           (ds : deserializer a) (cont : a -> deserializer b) : deserializer b :=
  fun s => match ds s with
        | (Some res, ss) => cont res ss
        | (None, ss) => (None, ss)
        end.
Notation "A >>= R ~> B" :=
  (bind_deserializer A (fun R => B)) (at level 80, right associativity).


Definition deserializer_fail {a : Set} : deserializer a := fun s => (None, s).


Definition deserializer_success {a : Set} : a -> deserializer a := fun x s => (Some x, s).


Definition finalize_deserializer {a : Set} (d : deserializer a) : deserializer a :=
  fun s => match d s with
        | (x, EmptyString) => (x, EmptyString)
        | (_, rest) => (None, rest)
        end.


Definition run_deserializer {a : Set} (s : string) (d : deserializer a): option a :=
  match d s with
  | (x, _) => x
  end.


Definition deserializer_ascii : deserializer ascii :=
  fun s => match s with
        | EmptyString => (None, s)
        | String c rest => (Some c, rest)
end.


Lemma N_of_ascii_range : forall (a : ascii), N_of_ascii a < 256.
Proof.
  destruct a as [[|][|][|][|][|][|][|][|]].
  all: simpl; zify; omega.
Qed.

Definition deserialize_N8 : deserializer N8 :=
 fun s => match s with
       | EmptyString => (None, s)
       | String c rest => (Some (exist _ (N_of_ascii c) (N_of_ascii_range c)), rest)
       end.


Definition deserialize_N16 : deserializer N16 :=
  deserialize_N8 >>= a ~> deserialize_N8 >>= b ~> deserializer_success (N16_of_two_N8 a b).


Fixpoint deserialize_data (s : string) : (option string * string) :=
  match s with
  | String c rest => match deserialize_data rest with
                    | (otail, finito) => (
                        match otail with
                        | None => None
                        | Some tail => Some (String c tail) end, finito)
                    end
  | _ => (Some EmptyString, EmptyString)
  end.


Fixpoint deserialize_string (s : string) : (option string * string) :=
  match s with
  | EmptyString => (None, s)
  | String "000" rest => (Some EmptyString, rest)
  | String c rest => match deserialize_string rest with
                    | (otail, finito) => (
                        match otail with
                        | None => None
                        | Some tail => Some (String c tail) end, finito)
                    end
  end.


Definition deserialize_packet {m : mode} : deserializer (packet Server m) :=
  let chuj m x := deserializer_success (ERROR Server m NotDefined x) in
  deserialize_N16 >>= op ~>
                  match N16_to_N op with
                  | 3 => match m with
                        | Read => deserialize_N16 >>= block ~> deserialize_data >>= data ~>
                                                 deserializer_success (DATA Server block data)
                        | Write => deserializer_fail
                        end
                  | 4 => match m with
                        | Write => deserialize_N16 >>= block ~>
                                                  deserializer_success (ACK Server block)
                        | Read => deserializer_fail
                        end
                  | 5 => deserialize_N16 >>= err ~> finalize_deserializer deserialize_string >>= msg ~>
                                        match error_from_code (N16_to_N err) with
                                        | Some type => deserializer_success (ERROR Server m type msg)
                                        | _ => deserializer_fail
                                        end
                  | _ => deserializer_fail
                  end.

Theorem embedding_opcode : forall (m : mode) (p : packet Client m),
    run_deserializer (serialize_opcode p "") (finalize_deserializer deserialize_N16) =
    N_to_N16 (opcode p).
Proof.
  intros.
  destruct m.
  all: (dependent destruction p;
       unfold serialize_opcode;
       unfold run_deserializer;
       unfold finalize_deserializer;
       unfold deserialize_N16;
       unfold N_to_N16;
       unfold N16_of_two_N8;
       simpl;
       apply f_equal;
       apply f_equal;
       apply UIP_dec;
       intros;
       destruct x;
       destruct y;
       intuition;
       right;
       discriminate).
Qed.
