Require Import Arith Util EqDec List.
Require Import Containers.OrderedTypeEx Integers.

Set Implicit Arguments.

(** * More or less abstract values *)
(** A file that abstacts over values and (should) provide all necessary operations. Although we concretely instantiate val to int, we maintain this file as interface between our proofs and Integer library. *)

(** Make the value type bitvectors and the default value 0 as a bitvector **)
Definition val := int.
Definition default_val : val := Int.zero.

Instance inst_val_defaulted : Defaulted val := {
  default_el := default_val
}.

Definition val_zero : val := Int.zero.

Instance inst_eq_dec_val : EqDec val eq.
hnf; intros. eapply Int.eq_dec.
Defined.

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

Inductive unop : Type :=
| UnOpToBool
| UnOpNeg.

Instance inst_eq_dec_unop : EqDec unop eq.
Proof.
  hnf; intros. change ({x = y} + {x <> y}).
  decide equality.
Qed.

Declare ML Module "containers_plugin".
Generate OrderedType unop.
Generate OrderedType binop.

Lemma unop_eq_eq x y
  : unop_eq x y -> x = y.
Proof.
  destruct x,y; inversion 1; eauto.
Qed.

Lemma binop_eq_eq x y
  : binop_eq x y -> x = y.
Proof.
  destruct x,y; inversion 1; eauto.
Qed.

Require Coq.Structures.OrderedTypeEx.


Instance Reflexive_eq_int : Reflexive Int.eq.
Proof.
  hnf; intros. hnf. cases; eauto.
  rewrite Int.eq_true in Heq. congruence.
Qed.

Instance Symmetric_eq_int : Symmetric Int.eq.
Proof.
  hnf; intros. rewrite Int.eq_sym; eauto.
Qed.

Instance Transitive_eq_int : Transitive Int.eq.
Proof.
  hnf; intros.
  pose proof (Int.eq_spec x y).
  pose proof (Int.eq_spec y z).
  cases in H1; cases in H2; subst; eauto.
Qed.

Instance Equivalence_eq_int : Equivalence Int.eq.
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Definition int_eq x y := Int.intval x = Int.intval y.

Instance Reflexive_eq_int' : Reflexive int_eq.
Proof.
  hnf; intros. hnf. reflexivity.
Qed.

Instance Symmetric_eq_int' : Symmetric int_eq.
Proof.
  unfold int_eq. hnf; intros. symmetry; eauto.
Qed.

Instance Transitive_eq_int' : Transitive int_eq.
Proof.
  unfold int_eq. hnf; intros. etransitivity; eauto.
Qed.

Instance Equivalence_eq_int' : Equivalence int_eq.
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Instance Transitive_lt_int : Transitive Int.ltu.
Proof.
  hnf. unfold Int.ltu. intros ? ? ? A B.
  cases in A; invc A; eauto.
  cases in B; invc B; eauto.
  destruct Z_StrictOrder.
  specialize (StrictOrder_Transitive _ _ _ l l0).
  rewrite Coqlib.zlt_true; eauto.
Qed.

Instance Irreflexive_lt_int : Irreflexive Int.ltu.
Proof.
  unfold Irreflexive, complement, Reflexive, Int.ltu; intros.
  cases in H; eauto.
  eapply Z.lt_irrefl; eauto.
Qed.

Instance int_eq_eq_lt
  : Proper (int_eq ==> int_eq ==> eq) Int.ltu.
Proof.
  unfold Proper, respectful, Int.ltu, Int.unsigned, int_eq; intros.
  rewrite H, H0. eauto.
Qed.

Instance StrictOrder_lt_int : StrictOrder Int.ltu int_eq.
Proof.
  econstructor; eauto with typeclass_instances.
  - intros ? ? LE EQ.
    rewrite <- EQ in LE.
    eapply (Irreflexive_lt_int x); eauto.
Defined.

Definition int_compare (x y : int) : Datatypes.comparison :=
  Z.compare (Int.intval x) (Int.intval y).

Unset Printing Records.

Lemma compare_spec_int x y
  : compare_spec int_eq Int.ltu x y (int_compare x y).
Proof.
  pose proof (Z.compare_spec (Int.intval x) (Int.intval y)).
  case_eq (int_compare x y); intros EQ; econstructor; unfold int_compare in EQ;
    rewrite EQ in H; inv H; eauto.
  - hnf. unfold Int.ltu.
    rewrite Coqlib.zlt_true; eauto.
  - hnf. unfold Int.ltu.
    rewrite Coqlib.zlt_true; eauto.
Qed.

Require Import ProofIrrelevance.

Lemma compare_spec_int_eq x y
  : int_compare x y = Eq -> x = y.
Proof.
  intros.
  pose proof (compare_spec_int x y). rewrite H in H0.
  inv H0. destruct x,y; compute in H1; subst.
  assert (intrange = intrange0).
  eapply ProofIrrelevance.proof_irrelevance. subst. reflexivity.
Qed.

Instance int_eq_dec : EqDec val int_eq.
hnf; intros. destruct x,y.
eapply Z.eq_dec.
Defined.

Instance int_eq_dec' x y : Computable (int_eq x y).
hnf; intros. destruct x,y.
eapply Z.eq_dec.
Defined.


Instance OrderedType_int : OrderedType int.
Proof.
  eapply (Build_OrderedType _ int_eq Int.ltu); eauto with typeclass_instances.
  eapply compare_spec_int.
Defined.



Definition option_lift1 A B (f:A -> B) := fun x => Some (f x).
Definition option_lift2 A B C (f:A -> B -> C) := fun x y => Some (f x y).

Definition val_true := Int.one.
Definition val_false := Int.zero.

Lemma val_true_false_neq
  : val_true <> val_false.
Proof.
  eapply Int.one_not_zero.
Qed.

Lemma val_true_false_nequiv
  : val_true =/= val_false.
Proof.
  inversion 1.
Qed.

Definition bool2val (b:bool) :=
  match b with
  | true => val_true
  | false => val_false
  end.


Definition val2bool (v: val) : bool := if [ v === val_zero ] then false else true.

Lemma val2bool_true
: val2bool val_true = true.
Proof.
  unfold val2bool.
  cases; eauto.
  exfalso; eauto using val_true_false_nequiv.
Qed.

Lemma val2bool_false
: val2bool val_false = false.
Proof.
  unfold val2bool.
  cases; eauto.
Qed.


Definition binop_eval (o:binop) :=
  match o with
      | BinOpAdd => option_lift2 Int.add
      | BinOpSub => option_lift2 Int.sub
      | BinOpMul => option_lift2 Int.mul
      | BinOpDiv => fun x y => if [ y === val_zero] then None else (Some (Int.divs x y))
      | BinOpEq => option_lift2 (fun x y => bool2val(Int.eq x y))
    end.

Lemma binop_eval_div_zero x y
  : y === val_zero
    <-> binop_eval BinOpDiv x y = None.
Proof.
  intros; simpl; cases; split; intros; eauto; exfalso; congruence.
Qed.

Lemma binop_eval_div_nonzero x y
  : y =/= val_zero
    -> exists v, binop_eval BinOpDiv x y = Some v.
Proof.
  intros; simpl; cases; eauto.
  exfalso; eauto.
Qed.

Lemma binop_eval_not_div op x y
  : op <> BinOpDiv
    -> exists v, binop_eval op x y = Some v.
Proof.
  intros; destruct op; simpl; unfold option_lift2; eauto.
  congruence.
Qed.

Definition unop_eval (o:unop) :=
  match o with
  | UnOpToBool => option_lift1 (fun a => bool2val(val2bool a))
  | UnOpNeg => option_lift1 Int.notbool
  end.

Lemma unop_eval_total op x
  : exists v, unop_eval op x = Some v.
Proof.
  intros; destruct op; simpl; unfold option_lift1; eauto.
Qed.

Lemma binop_eval_equiv
  : Proper (eq ==> equiv ==> equiv ==> equiv ) binop_eval.
Proof.
  unfold Proper, respectful; intros; subst.
  destruct y, x0,x1,y0,y1; compute in H0, H1; subst; simpl; unfold option_lift2;
    try reflexivity.
Qed.

Lemma unop_eval_equiv
  : Proper (eq ==> equiv ==> equiv ) unop_eval.
Proof.
  unfold Proper, respectful; intros; subst.
  destruct y, x0,y0; compute in H0; subst; simpl; unfold option_lift1;
    try reflexivity.
Qed.

Lemma unop_eval_equiv'
  : Proper (equiv ==> equiv ==> equiv ) unop_eval.
Proof.
  unfold Proper, respectful; intros; subst.
  destruct x0,y0; inv H; compute in H0; subst; simpl; unfold option_lift1;
    try reflexivity.
Qed.

Opaque val.
Opaque default_val.
Opaque val_true.
Opaque val_false.
Opaque val_zero.
Opaque val2bool.
