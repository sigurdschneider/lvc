Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisBackward LivenessAnalysis TrueLiveness Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments backward {sT} {Dom} btransform ZL AL st {ST} a.

Definition liveness_analysis_correct (i:overapproximation) sT ZL LV s a (ST:subTerm s sT)
  : ann_R poEq (@backward _ _ (liveness_transform_dep i) ZL LV s ST a) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length LV)
    -> paramsMatch s (length ⊝ ZL)
    -> true_live_sound i ZL (proj1_sig ⊝ LV) s
                      (mapAnn proj1_sig a).
Proof.
  intros EQ Ann DefZL DefLV PM.
  general induction Ann; simpl in *; inv DefZL; inv DefLV; inv PM; destruct a.
  - inv EQ.
    pose proof (ann_R_get H7); simpl in *.
    econstructor.
    eapply IHAnn; eauto.
    + intros. simpl in *.
      rewrite getAnn_mapAnn in H0.
      rewrite <- H in H0.
      cases in H2.
      eapply live_exp_sound_incl; [eapply Exp.live_freeVars|].
      rewrite <- H2. eapply incl_right.
    + intros. rewrite <- H2.
      simpl. rewrite getAnn_mapAnn.
      eapply incl_union_left.
      rewrite H. reflexivity.
  - inv EQ.
    simpl in *.
    econstructor; intros.
    + eapply IHAnn1; eauto.
    + eapply IHAnn2; eauto.
    + repeat cases in H9; try congruence.
      eapply live_op_sound_incl; [eapply Op.live_freeVars|].
      rewrite <- H9. eauto with cset.
    + rewrite getAnn_mapAnn.
      rewrite <- H9.
      eapply ann_R_get in H12. rewrite <- H12.
      cases. reflexivity.
      cases. congruence. eauto with cset.
    + rewrite getAnn_mapAnn.
      rewrite <- H9. cases. congruence.
      eapply ann_R_get in H13. rewrite <- H13.
      cases. reflexivity. eauto with cset.
  - inv EQ. simpl in *.
    edestruct (get_in_range _ H2) as [Z ?]; eauto.
    edestruct (get_in_range _ H3) as [[Lv ?] ?]; eauto.
    econstructor; eauto.
    + simpl. cases; eauto. rewrite <- H4.
      repeat erewrite get_nth; eauto.
      eapply incl_left.
    + simpl in *.
      erewrite get_nth in H4; eauto using map_get_1.
      erewrite get_nth in H4; eauto. simpl in *.
      eapply filter_by_incl_argsLive; eauto.
      inv_get; eauto.
      rewrite <- H4; eauto with cset.
    + inv_get; eauto.
  - inv EQ. econstructor.
    simpl in *. rewrite <- H1. eapply Op.live_freeVars.
  - inv EQ.
    simpl in *.
    econstructor.
    + rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- List.map_app.
      eapply (IHAnn i (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV)
             (subTerm_EQ_Fun1 eq_refl ST)); eauto.
      etransitivity; eauto.
      refine (@backward_ext sT (fun s => { x : ⦃var⦄ | x ⊆ occurVars s}) _
                            (liveness_transform_dep i)
                            (@liveness_transform_dep_ext i sT) _ _ _ _ _ _ _ _ _ _); eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros; inv_get.
      exploit H16; eauto.
      eapply ann_R_get in H11. symmetry; eauto.
    + rewrite map_length. eauto.
    + intros. inv_get.
      rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- List.map_app.
      edestruct (@get_backwardF sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                                (liveness_transform_dep i))); eauto.
      eapply (H1 _ _ _ H3 H2 i (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV) x1); eauto.
    + intros. inv_get. cases; eauto.
      rewrite <- H13. eapply incl_union_left.
      edestruct (@get_backwardF sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                                (liveness_transform_dep i))); eauto.
      exploit H16; eauto.
      eapply incl_list_union. eapply zip_get. eapply Take.get_take; eauto using get_range.
      eapply map_get_1. eapply get_app_lt; eauto with len.
      eapply Take.get_take; eauto using get_range. eapply get_app_lt; eauto with len.
      rewrite getAnn_mapAnn.
      eapply ann_R_get in H9.
      eapply SigR.sig_R_proj1_sig in H9.
      rewrite H9. eauto.
    + rewrite getAnn_mapAnn.
      eapply ann_R_get in H17.
      rewrite <- H17.
      rewrite <- H13. cases; eauto with cset.
Qed.

Definition correct i s
  : paramsMatch s nil
    -> true_live_sound i nil nil s (livenessAnalysis i s).
Proof.
  intros.
  unfold livenessAnalysis.
  destr_sig. destr_sig. dcr.
  eapply (@liveness_analysis_correct i s nil nil s); eauto.
  eapply H2.
Qed.

(* For now, settle for occur vars;
   TODO: Show that the fixpoint is contained in freeVars (and union of Lv) *)
Lemma livenessAnalysis_getAnn i s
  : getAnn (livenessAnalysis i s) ⊆ occurVars s.
Proof.
  unfold livenessAnalysis. repeat destr_sig.
  rewrite getAnn_mapAnn. destr_sig; eauto.
Qed.
