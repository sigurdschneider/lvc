Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Liveness Restrict Bisim MoreExp SetOperations.
Require Import DecSolve RenamedApart LabelsDefined.

Set Implicit Arguments.

(* shadowing free *)
Inductive shadowing_free : set var -> stmt -> Prop :=
  | shadowing_freeExp x e s D
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> shadowing_free {x; D} s
      -> shadowing_free D (stmtLet x e s)
  | shadowing_freeIf D e s t
    : Exp.freeVars e ⊆ D
    -> shadowing_free D s
    -> shadowing_free D t
    -> shadowing_free D (stmtIf e s t)
  | shadowing_freeRet D e
    : Exp.freeVars e ⊆ D
    -> shadowing_free D (stmtReturn e)
  | shadowing_freeGoto D f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D
    -> shadowing_free D (stmtApp f Y)
  | shadowing_freeExtern x f Y s D
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> shadowing_free {x; D} s
      -> shadowing_free D (stmtExtern x f Y s)
  | shadowing_freeLet D s t Z
    : of_list Z ∩ D [=] ∅
    -> shadowing_free (of_list Z ∪ D) s
    -> shadowing_free D t
    -> shadowing_free D (stmtFun Z s t).

Lemma shadowing_free_ext s D D'
  : D' [=] D
  -> shadowing_free D s
  -> shadowing_free D' s.
Proof.
  intros EQ SF. general induction SF; simpl; econstructor; try rewrite EQ; eauto.
  - eapply IHSF; eauto.
    rewrite EQ; reflexivity.
  - eapply IHSF; eauto. rewrite EQ; reflexivity.
  - eapply IHSF1; eauto. rewrite EQ. reflexivity.
Qed.

Instance shadowing_free_morphism
: Proper (Equal ==> eq ==> iff) shadowing_free.
Proof.
  unfold Proper, respectful; intros; subst.
  split; eapply shadowing_free_ext; eauto. symmetry; eauto.
Qed.

Lemma renamedApart_shadowing_free s an
  : renamedApart s an -> shadowing_free (fst (getAnn an)) s.
Proof.
  intros. general induction H; simpl; eauto using shadowing_free.
  - econstructor; eauto. rewrite H2 in IHrenamedApart. eauto.
  - rewrite H4 in IHrenamedApart1. rewrite H5 in IHrenamedApart2.
    econstructor; eauto.
  - econstructor; eauto. rewrite H2 in IHrenamedApart; eauto.
  - rewrite H3 in IHrenamedApart1. rewrite H5 in IHrenamedApart2.
    econstructor; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
