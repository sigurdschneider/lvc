Require Import Util LengthEq IL InRel RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness Coherence Delocation.
Require Import AddParam AddAdd MoreListSet DelocationAlgo DelocationAlgoIsCalled.

Set Implicit Arguments.

Opaque to_list.

Lemma additionalParameters_live_monotone ZL Lv LV' s an' LV lv
: live_sound Imperative ZL Lv s lv
  -> additionalParameters_live LV s lv an'
  -> PIR2 Subset LV' (Lv \\ ZL)
  -> additionalParameters_live LV' s lv an'.
Proof.
  intros LS APLS LE.
  general induction APLS; invt live_sound;
    eauto using additionalParameters_live.
  - inv_get. simpl in *.
    edestruct PIR2_nth_2 as [? [A B]]; eauto using zip_get.
    econstructor; eauto using map_get_1; simpl; eauto with cset.
  - lnorm.
    econstructor; eauto.
    + intros. exploit H1; eauto.
      rewrite zip_app; eauto with len. eapply PIR2_app; eauto.
      eapply PIR2_get. intros. inv_get.
      exploit H; eauto using @ifFstR.
      eauto 30 with len.
    + exploit IHAPLS; eauto.
      rewrite zip_app; eauto with len. eapply PIR2_app; eauto.
      eapply PIR2_get. intros. inv_get.
      exploit H; eauto using @ifFstR.
      eauto 30 with len.
Qed.

Lemma computeParameters_live b ZL Lv AP s lv
: live_sound Imperative ZL Lv s lv
  -> PIR2 Subset AP (Lv \\ ZL)
  -> length Lv = length ZL
  -> length ZL = length AP
  -> noUnreachableCode (isCalled b) s
  -> additionalParameters_live (oget ⊝ (snd (computeParameters (Lv \\ ZL) ZL AP s lv)))
                              s lv (fst (computeParameters (Lv \\ ZL) ZL AP s lv)).
Proof.
  intros LS SUB LEN1 LEN2 REACH.
  general induction LS; inv REACH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq;
    subst; simpl in *.
  - econstructor; eauto 20 using addParam_Subset with len.
  - econstructor; eauto with len.
    + eapply additionalParameters_live_monotone; eauto.
      * eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion;
          eauto using computeParameters_LV_DL with len.
    + eapply additionalParameters_live_monotone; eauto.
      * eapply PIR2_ifFstR_Subset_oget, ifFstR_zip_ounion;
          eauto using computeParameters_LV_DL with len.
  - inv_get. PIR2_inv. inv_get.
    econstructor; eauto using map_get_eq, keep_Some; eauto with cset.
  - econstructor.
  - exploit computeParameters_length as Len1; eauto with len.
    lnorm.
    econstructor.
    + intros. inv_get.
      pose proof (H8 _ H10).
      edestruct computeParameters_isCalledFrom_get_Some; try eapply H9;
        eauto using map_get_1, get_app with len; dcr; subst.
      intros; edestruct H2; eauto.
      simpl. rewrite of_list_3.
      exploit (@computeParameters_LV_DL (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (tab {}  ‖F‖ ++ AP));
        eauto using PIR2_Subset_tab_extend with len.
      exploit computeParametersF_LV_DL; try rewrite <- zip_app; eauto with len.
      eapply PIR2_nth in H13; eauto. dcr; inv_get. inv H17.
      split.
      rewrite H15. clear_all; cset_tac.
      edestruct H2; eauto.
      eapply NoDupA_app; eauto.
      eapply nodup_to_list_eq.
      intros.
      rewrite InA_In_eq in H18. rewrite InA_in in H18.
      rewrite InA_In_eq in H19. rewrite InA_in in H19.
      rewrite of_list_3 in H19.
      revert H15 H18 H19. clear_all. cset_tac.
    + intros. inv_get.
      exploit H1; eauto using pair_eta, PIR2_Subset_tab_extend with len.
      eapply additionalParameters_live_monotone; try eapply H9; eauto.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len.
      eapply computeParameters_LV_DL; eauto using PIR2_Subset_tab_extend with len.
    + eapply additionalParameters_live_monotone; try eapply IHLS;
        eauto using PIR2_Subset_tab_extend with len.
      rewrite map_map.
      rewrite of_list_oto_list_oget.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply PIR2_ifFstR_Subset_oget.
      eapply ifFstR_addAdds2. rewrite zip_app; eauto with len.
      eapply computeParametersF_LV_DL; eauto with len.
      eapply computeParameters_LV_DL; eauto using PIR2_Subset_tab_extend with len.
    + rewrite map_length. rewrite take_length_le; eauto.
      rewrite zip_length2.
      * eauto 20 with len.
      * rewrite fold_zip_ounion_length; eauto.
        -- eauto 20 with len.
        -- eapply computeParametersF_length; eauto.
           rewrite computeParameters_length; eauto with len.
           eauto with len.
Qed.

Lemma is_live b s lv
: live_sound Imperative nil nil s lv
  -> noUnreachableCode (isCalled b) s
  -> additionalParameters_live nil s lv (fst (computeParameters nil nil nil s lv)).
Proof.
  intros.
  assert (snd (computeParameters nil nil nil s lv) = nil). {
    exploit computeParameters_AP_LV; eauto.
    inv H1; eauto.
  }
  exploit computeParameters_live; eauto using @PIR2.
  simpl in *. rewrite H1 in H2. eauto.
Qed.
