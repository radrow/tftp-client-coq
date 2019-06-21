Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.BinNat.
Require Import Coq.Arith.Compare.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
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


Theorem N16_to_N_injection : forall (a : N16) (b : N16), N16_to_N a = N16_to_N b -> a = b.
Proof.
  intros.
  unfold N16_to_N in H.
  unfold proj1_sig in H.
  revert H.
  destruct a.
  destruct b.
  intro.
  revert l.
  revert l0.
  rewrite H.
  intros.
  assert (l0 = l).
  * apply UIP_dec. decide equality.
  * rewrite H0. reflexivity.
Qed.


Lemma safe_N16_incr_any : forall (n16 : N16),
    let n := N16_to_N n16 + 1 in
    (n < 256*256) -> exists (m16 : N16), N_to_N16 n = Some m16.
Proof.
  intros.
  cut (n < 256 * 256).
  * generalize (N16_to_N n16 + 1).
    intros.
    eexists.
    unfold N_to_N16.
    cut (
        (fun pf : (n ?= 256 * 256) = Lt =>
           Some (exist (fun n : N => n < 256 * 256) n pf))
        =
        (fun pf : (n ?= 256 * 256) = Lt =>
           Some (exist (fun n : N => n < 256 * 256) n H))).
    ** intros ->.
       generalize (eq_refl (n ?= 256 * 256)).
       revert H0.
       case_eq (n ?= 256 * 256);
         intros; unfold N.lt in H1; congruence + reflexivity.
    ** extensionality pf.
       f_equal.
       f_equal.
       apply UIP_dec.
       decide equality.
  * zify; omega.
Qed.

Lemma safe_N16_incr : forall (n16 : N16),
    let n := N16_to_N n16 + 1 in
    (n < 256*256) -> exists (H0 : n < 256*256), N_to_N16 n = Some (exist _ n H0).
Proof.
  intros.
  cut (n < 256 * 256).
  * generalize n.
    intros.
    eexists.
    unfold N_to_N16.
    cut (
        (fun pf : (n0 ?= 256 * 256) = Lt =>
           Some (exist (fun n1 : N => n1 < 256 * 256) n0 pf))
        =
        (fun pf : (n0 ?= 256 * 256) = Lt =>
           Some (exist (fun n1 : N => n1 < 256 * 256) n0 H0))).
    ** intros ->.
       generalize (eq_refl (n0 ?= 256 * 256)).
       revert H0.
       case_eq (n0 ?= 256 * 256);
         intros; unfold N.lt in H1; congruence + reflexivity.
    ** extensionality pf.
       f_equal.
       f_equal.
       apply UIP_dec.
       decide equality.
  * zify; omega.
Qed.

Definition N16_of_two_N8 (a : N8) (b : N8): N16.
  refine (exist _ (N8_to_N a * 256 + N8_to_N b) (two_N8_bounds a b)).
Defined.


Definition fst {a : Set} {b : Set} (p : a * b): a := match p with (x, _) => x end.

Definition snd {a : Set} {b : Set} (p : a * b): b := match p with (_, x) => x end.