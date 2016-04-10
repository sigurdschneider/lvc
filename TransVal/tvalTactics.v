Require Import IL Annotation AutoIndTac Exp MoreExp Coherence.
Require Import Util SetOperations Var.

Tactic Notation "setSubst" hyp(A) :=
  hnf in A; simpl in A; cset_tac; eapply A.

Tactic Notation "setSubst2" hyp(A) :=
  hnf; intros; hnf in A;  eapply A; simpl; cset_tac; eauto.

Tactic Notation "destructBin" hyp(A) :=
  destruct A; try destruct A; try destruct A; try destruct A;  try destruct A; try destruct A.

Tactic Notation "setSubstUnion" hyp(A) :=
  intros; eapply A; simpl;
  eapply list_union_start_swap; cset_tac; eauto.

Tactic Notation "rwsimpl" hyp(R) hyp(H) :=
  rewrite R in H; simpl in H.

Tactic Notation "rwsimplB" hyp (R) hyp (H) :=
  rewrite <- R in H; simpl in H.