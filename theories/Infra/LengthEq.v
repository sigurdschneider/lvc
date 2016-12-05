Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Import Len.
(*Require Import EqDec AutoIndTac.*)

Set Implicit Arguments.

Inductive length_eq X Y : list X -> list Y -> Type :=
  | LenEq_nil : length_eq nil nil
  | LenEq_cons x XL y YL : length_eq XL YL -> length_eq (x::XL) (y::YL).

Lemma length_eq_refl X (XL:list X)
  : length_eq XL XL.
Proof.
  induction XL; eauto using length_eq.
Qed.

Lemma length_eq_sym X Y (XL:list X) (YL:list Y)
  : length_eq XL YL -> length_eq YL XL.
Proof.
  intros A. induction A;eauto using length_eq.
Qed.

Lemma length_eq_trans X Y Z (XL:list X) (YL:list Y) (ZL:list Z)
  : length_eq XL YL -> length_eq YL ZL -> length_eq XL ZL.
Proof.
  intros A. revert ZL.
  induction A; inversion 1; eauto using length_eq.
Qed.

Lemma length_length_eq X Y (L:list X) (L':list Y)
  : length L = length L' -> length_eq L L'.
Proof.
  revert L'.
  induction L; destruct L'; inversion 1; eauto using length_eq.
Qed.

Lemma length_eq_length X Y (L:list X) (L':list Y)
  : length_eq L L' -> length L = length L'.
Proof.
  revert L'.
  induction L; destruct L'; inversion 1; simpl; eauto.
Qed.

Ltac length_equify :=
  repeat (match goal with
            | [ H : length ?A = length ?B |- _ ] =>
              eapply length_length_eq in H
          end).

Hint Immediate length_eq_length : len.
Hint Resolve length_length_eq : len.
