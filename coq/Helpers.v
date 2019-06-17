Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Compare.
Require Import ZArith.


Open Scope N_scope.

Definition option_prop {a : Set} (p : a -> Prop) (o : option a): Prop :=
  match o with
  | None => True
  | Some x => p x
  end.


Inductive mode : Set := Read | Write.

Inductive sender : Set := Server | Client.


Definition N8 := {n : N | n < 256}.

Definition N8_to_N (n : N8) : N := proj1_sig n.


Definition N16 := {n : N | n < 256*256}.

Definition N_to_N16 (n : N) : option N16 :=
  match n ?= 256 * 256 as cmp return (n ?= 256 * 256) = cmp -> option N16 with
  | Lt => fun pf => Some (exist _ n pf)
  | _ => fun _ => None
  end eq_refl.

Definition N16_to_N (n : N16) : N := proj1_sig n.

Theorem two_N8_bounds (a : N8) (b : N8) : N8_to_N a * 256 + N8_to_N b < 256*256.
  destruct a.
  destruct b.
  simpl.
  zify.
  omega.
Qed.

Definition N16_of_two_N8 (a : N8) (b : N8): N16.
  refine (exist _ (N8_to_N a * 256 + N8_to_N b) (two_N8_bounds a b)).
Defined.


Definition fst {a : Set} {b : Set} (p : a * b): a := match p with (x, _) => x end.

Definition snd {a : Set} {b : Set} (p : a * b): b := match p with (_, x) => x end.