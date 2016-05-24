Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis LivenessAnalysis TrueLiveness Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments backward {sT} {Dom} btransform ZL AL st {ST} a.

Definition liveness_analysis_correct sT ZL LV s a (ST:subTerm s sT)
  : ann_R poEq (@backward _ _ liveness_transform_dep ZL LV s ST a) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length LV)
    -> paramsMatch s (length ⊝ ZL)
    -> true_live_sound Imperative ZL (proj1_sig ⊝ LV) s
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
      eapply live_exp_sound_incl; [| eapply live_freeVars].
      rewrite <- H2. eapply incl_right.
    + rewrite <- H2.
      simpl. rewrite getAnn_mapAnn.
      eapply incl_union_left.
      rewrite H. cset_tac.
  - inv EQ.
    simpl in *.
    econstructor; intros.
    + eapply IHAnn1; eauto.
    + eapply IHAnn2; eauto.
    + repeat cases in H9; try congruence.
      eapply live_exp_sound_incl; [| eapply live_freeVars].
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
    + simpl. rewrite <- H4.
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
    simpl in *. rewrite <- H1. eapply live_freeVars.
  - inv EQ. simpl in *.
    econstructor.
    eapply IHAnn; eauto.
    + intros.
      eapply live_exp_sound_incl; [|eapply live_freeVars].
      rewrite <- H2. eapply incl_union_right.
      eapply incl_list_union; eauto using map_get_1.
    + rewrite getAnn_mapAnn. rewrite <- H2.
      eapply ann_R_get in H7. rewrite <- H7.
      eauto with cset.
  - inv EQ.
    simpl in *.
    econstructor.
    + rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- map_app.
      eapply (IHAnn (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV)
             (subTerm_EQ_Fun1 eq_refl ST)); eauto.
      etransitivity; eauto.
      refine (@backward_ext sT (fun s => { x : ⦃var⦄ | x ⊆ occurVars s}) _
                            (liveness_transform_dep)
                            (@liveness_transform_dep_ext sT) _ _ _ _ _ _ _ _ _ _); eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros; inv_get.
      exploit H16; eauto.
      eapply ann_R_get in H9. symmetry; eauto.
      * rewrite app_length, map_length. eauto.
      * rewrite app_length, map_length, <- H. eauto.
      * rewrite map_app.
        rewrite map_map. eauto.
    + rewrite map_length. eauto.
    + intros. inv_get.
      rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- map_app.
      edestruct (@get_backwardF sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0}) liveness_transform_dep)); eauto.
      eapply (H1 _ _ _ H3 H2 (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV) x1); eauto.
      * rewrite app_length, map_length. eauto.
      * rewrite app_length, map_length, <- H. eauto.
      * rewrite map_app. exploit H6; eauto.
        rewrite map_map. eauto.
    + intros. inv_get. simpl. eauto.
    + rewrite getAnn_mapAnn.
      eapply ann_R_get in H17.
      rewrite <- H17.
      rewrite <- H13. reflexivity.
Qed.