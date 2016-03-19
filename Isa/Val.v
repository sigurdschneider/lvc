Require Import Arith Util EqDec List bitvec.
Require Import OrderedTypeEx.

Set Implicit Arguments.

(** * More or less abstract values *)
(** A file that abstacts over values and (should) provide all necessary operations. Although we concretely instantiate val to int, we maintain this file as interface between our proofs and Integer library. *)

(** Make the value type bitvectors and the default value 0 as a bitvector **)
Definition val := bitvec.
Definition default_val : val := (zext (O::nil)).

Opaque val.
Opaque default_val.

(** Default value for true = 1 = 2^1 , false = 0 = 2^0 **)
Definition val_true := (sext (I::nil) I).
Definition val_false := (zext (O::nil)).

Fixpoint eqValList (l1:list bitvec) (l2:list bitvec) :=
match l1, l2 with
| nil, _ => val_false
| _, nil => val_false
| a::l1', b::l2' => bvAnd (eqValList l1' l2') (bvEq a b)
end.

Global Instance inst_val_defaulted : Defaulted val := {
  default_el := default_val
}.

Global Instance inst_eq_dec_val : EqDec val eq.
hnf; intros. change ({x = y} + {x <> y}).
assert (X:forall b1 b2:bit, {b1 = b2} + {b1 <> b2}).
- intros. destruct b1, b2.
  + left; reflexivity.
  + right; firstorder.
  + right; firstorder.
  + left; reflexivity.
- exact (list_eq_dec X x y).
Defined.

(** ** There must be an injection into the booleans *)
Definition val2bool : val -> bool := fun v => toBool  v. (*  match v with 0 => false | _ => true end. *)

Lemma val2bool_true
: val2bool val_true = true.
Proof.
  unfold val_true, val2bool, sext.
  rewrite toBool_I_true; [auto|].
  pose proof K_ge1; auto.
Qed.

Lemma val2bool_false
: val2bool val_false = false.
Proof.
  unfold val2bool, val_false, zext.
  rewrite toBool_O_false; auto.
Qed.

Opaque val2bool.

Inductive ty : Set :=
  Natural : ty.

Global Instance inst_eq_dec_ty : EqDec ty eq.
hnf; intros. change ({x = y} + {x <> y}).
decide equality.
Defined.

Inductive valOfType : val -> ty -> Prop :=
  naturalOfType n : valOfType n Natural.
(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
