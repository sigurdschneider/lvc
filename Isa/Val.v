Require Import Arith Util EqDec List.
Require Import OrderedTypeEx Integers.

Set Implicit Arguments.

(** * More or less abstract values *)
(** A file that abstacts over values and (should) provide all necessary operations. Although we concretely instantiate val to int, we maintain this file as interface between our proofs and Integer library. *)

(** Make the value type bitvectors and the default value 0 as a bitvector **)
Definition val := int.
Definition default_val : val := Int.zero.

Instance inst_val_defaulted : Defaulted val := {
  default_el := default_val
}.

(** Default value for true = 1 = 2^1 , false = 0 = 2^0 **)
Definition val_true := Int.one.
Definition val_false := Int.zero.
Lemma val_true_false_neq
  : val_true <> val_false.
Proof.
  eapply Int.one_not_zero.
Qed.

Definition val_zero : val := Int.zero.

Instance inst_eq_dec_val : EqDec val eq.
hnf; intros. eapply Int.eq_dec.
Defined.

(** ** There must be an injection into the booleans *)
Definition val2bool (v: val) : bool := if [ v = val_zero ] then false else true.

Lemma val2bool_true
: val2bool val_true = true.
Proof.
  unfold val2bool.
  cases; eauto.
  exfalso; eauto using val_true_false_neq.
Qed.

Lemma val2bool_false
: val2bool val_false = false.
Proof.
  unfold val2bool.
  cases; eauto.
Qed.

Opaque val.
Opaque default_val.
Opaque val_true.
Opaque val_false.
Opaque val_zero.
Opaque val2bool.
