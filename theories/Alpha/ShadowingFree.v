Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env IL Annotation Liveness Restrict SetOperations.
Require Import DecSolve RenamedApart LabelsDefined.

Set Implicit Arguments.

(* shadowing free *)
Inductive shadowingFree : set var -> stmt -> Prop :=
  | shadowingFreeExp x e s D
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> shadowingFree {x; D} s
      -> shadowingFree D (stmtLet x e s)
  | shadowingFreeIf D e s t
    : Op.freeVars e ⊆ D
    -> shadowingFree D s
    -> shadowingFree D t
    -> shadowingFree D (stmtIf e s t)
  | shadowingFreeRet D e
    : Op.freeVars e ⊆ D
    -> shadowingFree D (stmtReturn e)
  | shadowingFreeGoto D f Y
    : list_union (List.map Op.freeVars Y) ⊆ D
    -> shadowingFree D (stmtApp f Y)
  | shadowingFreeLet D F t
    : (forall n Zs, get F n Zs -> shadowingFree (of_list (fst Zs) ∪ D) (snd Zs))
      -> (forall n Zs, get F n Zs -> disj (of_list (fst Zs)) D)
      -> shadowingFree D t
      -> shadowingFree D (stmtFun F t).

Lemma shadowingFree_ext s D D'
  : D' [=] D
  -> shadowingFree D s
  -> shadowingFree D' s.
Proof.
  intros EQ SF.
  general induction SF; simpl; econstructor; try setoid_rewrite EQ; eauto with cset.
Qed.

Instance shadowingFree_morphism
: Proper (Equal ==> eq ==> iff) shadowingFree.
Proof.
  unfold Proper, respectful; intros; subst.
  split; eapply shadowingFree_ext; eauto. symmetry; eauto.
Qed.

Lemma renamedApart_shadowing_free s an
  : renamedApart s an -> shadowingFree (fst (getAnn an)) s.
Proof.
  intros. general induction H; simpl; pe_rewrite; eauto using shadowingFree.
  - econstructor; eauto.
    + intros. edestruct get_length_eq; eauto. exploit H1; eauto.
      edestruct H2; eauto; dcr. rewrite H10 in *. eauto.
    + intros. edestruct get_length_eq; eauto. edestruct H2; eauto; dcr. eauto.
Qed.
