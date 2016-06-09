Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForward UnreachableCodeAnalysis UnreachableCode Subterm.

Set Implicit Arguments.

Lemma forward_getAnn (sT:stmt) (Dom : stmt -> Type) `{BoundedSemiLattice (Dom sT)}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL a an
  : ann_R eq (fst (@forward sT Dom _ _ f ZL s ST (setTopAnn an a))) an
    -> getAnn an = a.
Proof.
  intros. destruct s, an; inv H1; simpl in *; eauto;
  repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; inv H2; eauto.
Qed.

Lemma setTopAnn_eta A (an:ann A) a
  : getAnn an = a
    -> setTopAnn an a = an.
Proof.
  intros; destruct an; simpl in *; subst; eauto.
Qed.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} ftransform ZL st ST a.

Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : ann_R eq (fst (forward ?unreachable_code_transform ?ZL ?s ?ST (setTopAnn ?sa ?a))) ?sa |- _ ] =>
           let X := fresh "H" in
           match goal with
           | [ H' : getAnn sa = a |- _ ] => fail 1
           | _ => exploit (forward_getAnn _ _ _ _ _ H) as X
           end
         end; rewrite setTopAnn_eta in *; try eassumption.

Lemma PIR2_fstNoneOrR_inv_left A B C
  : PIR2 (fstNoneOrR impb) (ojoin bool orb ⊜ A B) C
    -> length A = length B
    -> PIR2 (fstNoneOrR impb) A C.
Proof.
  intros. length_equify.
  general induction H; inv H0; simpl in *; eauto using PIR2; try solve [ congruence ].
  - inv Heql; econstructor; eauto.
    + inv Heql.
      destruct x0, y0; simpl in *; inv pf; econstructor; eauto.
      destruct b, b0, y0; simpl in *; eauto.
Qed.

Lemma PIR2_fstNoneOrR_inv_right A B C
  : PIR2 (fstNoneOrR impb) (ojoin bool orb ⊜ A B) C
    -> length A = length B
    -> PIR2 (fstNoneOrR impb) B C.
Proof.
  intros. length_equify.
  general induction H; inv H0; simpl in *; eauto using PIR2; try solve [ congruence ].
  - inv Heql; econstructor; eauto.
    + inv Heql.
      destruct x0, y0; simpl in *; inv pf; econstructor; eauto.
      destruct b, b0, y0; simpl in *; eauto.
Qed.

Definition unreachable_code_analysis_correct sT ZL BL s a (ST:subTerm s sT)
  : ann_R poEq (fst (forward unreachable_code_transform ZL s ST a)) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length BL)
    -> paramsMatch s (length ⊝ ZL)
    -> poLe (snd (@forward sT _ _ _ unreachable_code_transform ZL s ST a)) (Some ⊝ BL)
    -> unreachable_code ZL BL s a.
Proof.
  intros EQ Ann DefZL DefBL PM.
  general induction Ann; simpl in *; inv DefZL; inv DefBL; inv PM;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - inv EQ.
    pose proof (ann_R_get H8); simpl in *.
    econstructor.
    eapply IHAnn; eauto;
    simpl_forward_setTopAnn.
  - assert (❬snd (forward unreachable_code_transform ZL s (subTerm_EQ_If1 eq_refl ST) sa)❭ =
            ❬snd (forward unreachable_code_transform ZL t (subTerm_EQ_If2 eq_refl ST) ta)❭). {
      eapply (@forward_length_ass _ (fun _ => bool)); eauto. symmetry.
      eapply (@forward_length_ass _ (fun _ => bool)); eauto.
    }
    repeat cases in EQ; simpl in *; try solve [congruence]; inv EQ;
    repeat simpl_forward_setTopAnn;
    econstructor; intros; try solve [congruence];
      eauto using PIR2_fstNoneOrR_inv_left, PIR2_fstNoneOrR_inv_right.
  - inv_get.
    edestruct (get_in_range _ H3) as [B ?]; eauto.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr. inv_get.
    destruct x1; isabsurd.
    econstructor; eauto.
  - econstructor.
  - inv EQ.
    pose proof (ann_R_get H8); simpl in *.
    econstructor.
    eapply IHAnn; eauto;
    simpl_forward_setTopAnn.
  - inv EQ.
    econstructor; eauto.
    + eapply IHAnn; eauto.

    + intros.
      edestruct (get_forwardF (fun _ => bool) (forward unreachable_code_transform)
                              (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H3 H4).
      eapply H1; eauto. admit.
    + intros.

Qed.

Definition livenessAnalysis s :=
  let a := Analysis.safeFixpoint (LivenessAnalysis.liveness_analysis s) in
  mapAnn (@proj1_sig _ _) (proj1_sig (proj1_sig a)).



Ltac destr_sig H :=
  match type of H with
  | context [proj1_sig ?x] => destruct x; simpl in H
  end.

Tactic Notation "destr_sig" :=
  match goal with
  | [ |- context [proj1_sig (proj1_sig ?x)] ] => destruct x; simpl
  | [ |- context [proj1_sig ?x] ] => destruct x; simpl
  end.

Definition correct s
  : labelsDefined s 0
    -> paramsMatch s nil
    -> true_live_sound Imperative nil nil s (livenessAnalysis s).
Proof.
  intros.
  unfold livenessAnalysis.
  destr_sig. destr_sig. dcr.
  eapply (@liveness_analysis_correct s nil nil s); eauto.
  eapply H3.
Qed.
