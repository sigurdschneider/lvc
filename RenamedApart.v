Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation SetOperations MoreList.

Set Implicit Arguments.

Inductive renamedApart : stmt -> ann (set var * set var) -> Prop :=
  | renamedApartExp x e s D D' D'' an
    : x ∉ D
      -> Exp.freeVars e ⊆ D
      -> renamedApart s an
      -> pe (getAnn an) ({x; D}, D')
      -> D'' [=] {x; D'}
      -> renamedApart (stmtLet x e s) (ann1 (D, D'') an)
  | renamedApartIf  D D' Ds Dt e s t ans ant
    : Exp.freeVars e ⊆ D
      -> Ds ∩ Dt [=] ∅
      -> Ds ∪ Dt [=] D'
      -> renamedApart s ans
      -> renamedApart t ant
      -> pe (getAnn ans) (D, Ds)
      -> pe (getAnn ant) (D, Dt)
      -> renamedApart (stmtIf e s t) (ann2 (D, D') ans ant)
  | renamedApartRet D D' e
    : Exp.freeVars e ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtReturn e) (ann0 (D, D'))
  | renamedApartGoto D D' f Y
    : list_union (List.map Exp.freeVars Y) ⊆ D
      -> D' [=] ∅
      -> renamedApart (stmtApp f Y) (ann0 (D, D'))
  | renamedApartExtern x f Y s D D' D'' an
    : x ∉ D
      -> list_union (List.map Exp.freeVars Y) ⊆ D
      -> renamedApart s an
      -> pe (getAnn an) ({x; D}, D')
      -> D'' [=] {x; D'}
      -> renamedApart (stmtExtern x f Y s) (ann1 (D, D'') an)
  | renamedApartLet D D' s t Ds Dt Z ans ant
    : of_list Z ∩ D [=] ∅
      -> (Ds ++ of_list Z) ∩ Dt [=] ∅
      -> Ds ∪ Dt ∪ of_list Z [=] D'
      -> renamedApart s ans
      -> pe (getAnn ans) (of_list Z ∪ D, Ds)
      -> renamedApart t ant
      -> pe (getAnn ant) (D, Dt)
      -> unique Z
      -> renamedApart (stmtFun Z s t) (ann2 (D,D') ans ant).

Lemma renamedApart_ext s an an'
  : ann_R (@pe _ _) an an'
  -> renamedApart s an
  -> renamedApart s an'.
Proof.
  intros. general induction H0; simpl; invt (ann_R (@pe var _));
          invt (@pe var _); eauto using renamedApart.
  - econstructor. rewrite <- H8; eauto. rewrite <- H8; eauto.
    eapply IHrenamedApart; eauto. rewrite <- H8. rewrite (ann_R_get H9) in H2. eauto.
    rewrite <- H11. eauto.

  - econstructor; eauto. rewrite <- H7; eauto. rewrite <- H12; eauto.
    rewrite <- (ann_R_get H10). rewrite <- H7. eauto.
    rewrite <- (ann_R_get H11). rewrite <- H7. eauto.

  - econstructor; eauto. rewrite <- H5; eauto. rewrite <- H7; eauto.
  - econstructor. rewrite <- H5; eauto. rewrite <- H7; eauto.

  - econstructor. rewrite <- H8; eauto. rewrite <- H8; eauto.
    eapply IHrenamedApart; eauto. rewrite <- H8.
    rewrite <- (ann_R_get H9). eauto. rewrite <- H11; eauto.

  - econstructor; eauto. rewrite <- H8; eauto.
    rewrite <- H13; eauto.
    rewrite <- H8. rewrite <- (ann_R_get H11); eauto.
    rewrite <- H8. rewrite <- (ann_R_get H12); eauto.
Qed.

Instance renamedApart_morphism
: Proper (eq ==> (ann_R (@pe _ _)) ==> iff) renamedApart.
Proof.
  intros x s t A; subst. intros. split; intros.
  eapply renamedApart_ext; eauto.
  eapply renamedApart_ext; try symmetry; eauto.
Qed.

Lemma renamedApart_freeVars s an
  : renamedApart s an -> freeVars s ⊆ fst (getAnn an).
Proof.
  intros. general induction H; simpl; eauto.
  - rewrite H0, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite H, IHrenamedApart1, IHrenamedApart2. rewrite H4, H5; simpl.
    cset_tac; intuition.
  - rewrite H0, IHrenamedApart, H2; simpl. cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. inv H3; inv H5; simpl.
    rewrite H10, H13. cset_tac; intuition.
Qed.

Lemma renamedApart_occurVars s an
  : renamedApart s an -> definedVars s [=] snd (getAnn an).
Proof.
  intros. general induction H; simpl; eauto.
  - rewrite H3, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. rewrite H4, H5; simpl; eauto.
  - cset_tac; intuition; eauto.
  - cset_tac; intuition; eauto.
  - rewrite H3, IHrenamedApart, H2. simpl.
    clear_all; cset_tac; intuition.
  - rewrite IHrenamedApart1, IHrenamedApart2. rewrite H3, H5; simpl. eauto.
Qed.

Definition pminus (D'':set var) (s:set var * set var) :=
  match s with
    | pair s s' => (s \ D'', s')
  end.

Instance pminus_morphism
: Proper (Equal ==> (@pe _ _) ==> (@pe _ _) ) pminus.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; econstructor. rewrite H1, <- H. reflexivity.
  eauto.
Qed.

Instance mapAnn_pminus_morphism G'
  : Proper (ann_R (@pe _ _) ==> ann_R (@pe _ _)) (mapAnn (pminus G')).
Proof.
  unfold Proper, respectful; intros.
  general induction H; simpl.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
Qed.

Lemma renamedApart_minus D an an' s
  : notOccur D s
    -> renamedApart s an
    -> ann_R (@pe _ _) an' (mapAnn (pminus D) an)
    -> renamedApart s an'.
Proof.
  intros ? ? PE. general induction H0; invt notOccur; try rewrite PE; simpl in * |- *.
  - eapply Exp.notOccur_disj_freeVars in H10.
    econstructor.
    + revert H; clear_all; cset_tac; intuition.
    + revert H10 H0; clear_all; cset_tac; intuition; eauto.
    + eapply IHrenamedApart; eauto.
    + rewrite getAnn_mapAnn. inv H2; simpl.
      rewrite H11, H12. econstructor.
      revert H8 H10; clear_all; cset_tac; intuition; cset_tac; eauto.
      reflexivity.
    + rewrite H3; reflexivity.
  - eapply Exp.notOccur_disj_freeVars in H8.
    econstructor; [|eapply H0| | | | |].
    + revert H H8; clear_all; cset_tac; intuition; cset_tac; eauto.
    + rewrite H1; reflexivity.
    + eapply IHrenamedApart1; eauto; try reflexivity.
    + eapply IHrenamedApart2; eauto; try reflexivity.
    + rewrite getAnn_mapAnn. inv H2; simpl. rewrite H11, H12; reflexivity.
    + rewrite getAnn_mapAnn. inv H3; simpl. rewrite H11, H12; reflexivity.
  - eapply Exp.notOccur_disj_freeVars in H3.
    econstructor; eauto.
    revert H H3; clear_all; cset_tac; intuition; cset_tac; eauto.
  - econstructor; eauto.
    edestruct (list_union_disjunct (List.map Exp.freeVars Y)) as [? _].
    exploit H2; intros.
    rewrite meet_comm.
    edestruct map_get_4; eauto; dcr; subst.
    eapply Exp.notOccur_disj_freeVars; eauto.
    revert H X; clear_all; cset_tac; intuition; eauto.
  - eapply list_union_notOccur in H8.
    econstructor.
    + revert H; clear_all; cset_tac; intuition.
    + revert H8 H0; clear_all; cset_tac; intuition; eauto.
    + eapply IHrenamedApart; eauto.
    + rewrite getAnn_mapAnn. inv H2; simpl.
      rewrite H9, H12. econstructor.
      revert H H10; clear_all; cset_tac; intuition; cset_tac; eauto.
      reflexivity.
    + rewrite H3; reflexivity.
  - econstructor; try eapply H0; eauto.
    + revert H H9; clear_all; cset_tac; intuition; eauto.
    + rewrite getAnn_mapAnn; simpl. inv H2; simpl.
      rewrite H12, H13. constructor; try reflexivity.
      revert H9; clear_all; cset_tac; intuition; eauto.
    + rewrite getAnn_mapAnn; simpl. inv H3; simpl.
      rewrite H12, H13. reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
