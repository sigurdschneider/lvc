Require Import List Omega.
Require Import Util EqDec.
Require Import OrderedTypeEx.

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

Inductive loc : Type :=
  | LocI : nat -> loc.
Definition default_loc : loc := LocI 0.
Global Instance inst_eq_dec_loc : EqDec loc eq.
hnf; intros. destruct x,y. decide (n=n0).
subst; left; reflexivity.
right. intro. inversion H. eauto.
Defined.

Definition locN l :=
  match l with
    | LocI n => n
  end.

Lemma locN_inj (x y : loc)
  : locN x = locN y -> x = y.
Proof.
  destruct x,y; eauto.
Qed.

Definition locInc (l:loc) (d:nat) := match l with LocI n => LocI (d + n) end.

Global Instance inst_counted_loc : Counted loc :=
  Build_Counted locN locN_inj locInc.

(** ** Labels **)
(* Labels are used as identifiers for blocks *)
Inductive lab : Type :=
| LabI : nat -> lab.

Definition default_lab := LabI 0.

Lemma eq_dec_lab (x y : lab) :
  {x=y} + {x<>y}.
Proof.
  repeat decide equality.
Defined.

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

Definition lt (l l':lab) :=
  match l, l' with
    LabI n, LabI m => lt n m
  end.

(** ** [lab] *)
Instance lab_StrictOrder : StrictOrder lt (@eq lab).
econstructor. hnf; intros. destruct x,y,z; simpl in *. omega.
intros. destruct x,y; simpl in *. assert (n <> n0) by omega.
hnf; intros. inv H1. congruence.
Qed.

Fixpoint lab_compare (l l' : lab) :=
  match l, l' with
    | LabI n, LabI m => nat_compare n m
  end.

Program Instance lab_OrderedType : UsualOrderedType lab := {
  SOT_lt := lt;
  SOT_cmp := lab_compare;
  SOT_StrictOrder := lab_StrictOrder
}.
Next Obligation.
  case_eq (lab_compare x y); destruct x,y; simpl; intro Hcomp; constructor.
  eapply nat_compare_eq in Hcomp; eauto.
  apply nat_compare_lt in Hcomp; assumption.
  apply nat_compare_gt in Hcomp; assumption.
Qed.

Instance proper_var (ϱ:var -> var)
: Proper (_eq ==> _eq) ϱ.
Proof.
  intuition.
Qed.

Hint Extern 20 (@Proper
               (@respectful _ _
                            (@_eq _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))
                            (@_eq _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))) ?ϱ) => eapply proper_var.
