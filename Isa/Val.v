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

Inductive binop : Type :=
| BinOpAdd
| BinOpSub
| BinOpMul
| BinOpDiv
| BinOpEq.

Instance inst_eq_dec_binop : EqDec binop eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
Qed.

Definition option_lift1 A B (f:A -> B) := fun x => Some (f x).
Definition option_lift2 A B C (f:A -> B -> C) := fun x y => Some (f x y).
Definition bool2val (b:bool) :=
  match b with
  | true => val_true
  | false => val_false
  end.

Definition binop_eval (o:binop) :=
  match o with
      | BinOpAdd => option_lift2 Int.add
      | BinOpSub => option_lift2 Int.sub
      | BinOpMul => option_lift2 Int.mul
      | BinOpDiv => option_lift2 Int.divs
      | BinOpEq => option_lift2 (fun x y => bool2val(Int.eq x y))
    end.

Inductive unop : Type :=
| UnOpToBool
| UnOpNeg.

Instance inst_eq_dec_unop : EqDec unop eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
Qed.

Definition unop_eval (o:unop) :=
  match o with
  | UnOpToBool => option_lift1 (fun a => bool2val(val2bool a))
  | UnOpNeg => option_lift1 Int.notbool
  end.

Opaque val.
Opaque default_val.
Opaque val_true.
Opaque val_false.
Opaque val_zero.
Opaque val2bool.
