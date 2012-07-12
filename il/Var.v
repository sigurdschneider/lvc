Require Import List.
Require Import Util EqDec.

Set Implicit Arguments.

(** * Definitions related to variables *)

(** ** A class for counted types *)
(** A counted type is a type for which an injection to the naturals exists *)
Class Counted (A : Type) := {
  counted     : A -> nat;
  counted_inj : forall (x y : A), counted x = counted y -> x = y;
  incc        : forall (x : A), nat -> A
}.

(** ** Variables *)
(* We take naturals directly as variables *)
Definition var : Type := nat.
Definition default_var : var := 0%nat.

Global Instance inst_defaulted_var : Defaulted var := Build_Defaulted default_var.
Global Instance inst_eq_dec_var : EqDec var eq := nat_eq_eqdec. 
Global Program Instance inst_counted_var : Counted var :=
  Build_Counted (fun x => x) _ (fun x => fun y => x + y).

(** ** Locations *)

Definition loc : Type := nat.
Definition default_loc : loc := 0.
Global Instance inst_eq_dec_loc : EqDec loc eq := nat_eq_eqdec.
Global Instance inst_counted_loc : Counted loc := inst_counted_var.

(** ** Labels **)
(* Labels are used as identifiers for blocks *)
Inductive lab : Type :=
| LabI : nat -> lab.

Definition default_lab := LabI 0.

Lemma eq_dec_lab (x y : lab) :
  {x=y} + {x<>y}.
Proof. 
  repeat decide equality. 
Qed.

(** *** equality of labels is decidable *)
Global Instance inst_eq_dec_lab : EqDec lab eq := {
  equiv_dec := eq_dec_lab
}.

(** *** labels are counted *)
Definition labN (x : lab) : nat :=
  match x with
  | LabI x => x
  end.

Lemma labN_inj (x y : lab) 
  : labN x = labN y -> x = y.
Proof.
  destruct x,y; eauto.
Qed.

Definition labInc (l:lab) (d:nat) := match l with LabI n => LabI (d + n) end.

Global Instance inst_counted_lab : Counted lab :=
  Build_Counted labN labN_inj labInc.

Lemma counted_labI (n : nat) :
  counted (LabI n) = n.
Proof.
  eauto.
Qed.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr") ***
*** End: ***
*)
