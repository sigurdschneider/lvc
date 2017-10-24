Require Import Util LengthEq IL RenamedApart LabelsDefined OptionR.
Require Import Keep Drop Take Restrict SetOperations OUnion.
Require Import Annotation Liveness.Liveness Coherence Delocation.
Require Import AddParam AddAdd MoreListSet DelocationAlgo DelocationAlgoIsCalled.
Require Import PartialOrder.

Set Implicit Arguments.

Local Hint Extern 10 (forall _ _, get (snd ⊝ computeParametersF ?DL ?ZL ?AP ?F ?als) _ _ -> ❬?LVb❭ = ❬_❭)
=> eapply computeParametersF_length : len.

Local Hint Extern 1 =>
match goal with
  [ |- context [ ❬snd (computeParameters _ _ _ _ _)❭ ] ] =>
  rewrite computeParameters_length; eauto with len
end : len.


Lemma computeParameters_trs b ZL Lv AP s lv
: live_sound Imperative ZL Lv s lv
  -> noUnreachableCode (isCalled b) s
  -> poLe AP (Lv \\ ZL)
  -> length Lv = length ZL
  -> length ZL = length AP
  -> trs (restr (getAnn lv) ⊝ (zip ominus' (Lv \\ ZL)
                                  (snd (computeParameters (Lv \\ ZL) ZL AP s lv))))
        (List.map oto_list (snd (computeParameters (Lv \\ ZL) ZL AP s lv)))
        s lv
        (fst (computeParameters (Lv \\ ZL) ZL AP s lv)).
Proof.
  intros LIVE NOUR P LEN1 LEN2.
  revert_except LIVE.
  induction LIVE; simpl in *; intros; repeat let_case_eq;
    repeat let_pair_case_eq; inv NOUR; simpl in *.
  - eapply trsExp, trs_monotone_DL.
    + eapply IHLIVE; eauto 10 using addParam_Subset with len.
    + rewrite restrict_comp_meet.
      assert (SEQ:lv ∩ (getAnn al \ singleton x) [=] getAnn al \ singleton x) by
          (clear - H0; cset_tac).
      rewrite SEQ. eapply restrict_zip_ominus'; eauto with len.
      eapply PIR2_not_in; [ eapply computeParameters_AP_LV; eauto with len
                          | eauto with len].
  - econstructor.
    + eapply trs_monotone_DL_AP; eauto.
      eapply restrict_subset2; eauto.
      eapply zip_ominus_contra; eauto using PIR2_zip_ounion with len.
      eapply PIR2_zip_ounion; eauto with len.
    + eapply trs_monotone_DL_AP; eauto using PIR2_zip_ounion' with len.
      eapply restrict_subset2; eauto with len.
      eapply zip_ominus_contra; eauto using PIR2_zip_ounion' with len.
  - inv_get.
    econstructor.
    + eapply restrict_get_Some.
      eapply zip_get_eq. eapply zip_get; eauto.
      eapply keep_Some; eauto. simpl. reflexivity.
      rewrite <- H1. eauto with cset.
    + eapply map_get_1. eapply keep_Some; eauto.
  - econstructor.
  - len_simpl.
    assert (LenHelp1:❬(getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)❭ =
                     ❬snd
                        (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)) (fst ⊝ F ++ ZL)
                                           (tab {} ‖F‖ ++ AP) t alb)❭). {
      rewrite computeParameters_length; eauto; revert LEN1 LEN2 H; clear_all;
        eauto with len.
    }
    assert (LenHelp2:
              forall (n : nat) (aa : 〔؟ ⦃var⦄〕),
                get (snd ⊝ computeParametersF F als Lv ZL AP) n aa ->
                ❬aa❭ =
                ❬snd
                   (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)) (fst ⊝ F ++ ZL)
                                      (tab {} ‖F‖ ++ AP) t alb)❭). {
      eapply computeParametersF_length; eauto.
      rewrite <- LenHelp1. eauto with len. eauto with len.
    }
    lnorm. econstructor.
    + eauto with len.
    + eauto with len.
    + rewrite map_length. rewrite take_length_le; eauto.
      rewrite zip_length2; [eauto 20 with len|].
      rewrite fold_zip_ounion_length; eauto.
    + intros. inv_get. simpl.
      rewrite <- List.map_app. rewrite <- take_eta.
      eapply trs_monotone_DL_AP.
      * eapply H1; eauto using PIR2_Subset_tab_extend with len.
      * { rewrite (take_eta (length F) (zip ominus' _ _)).
          do 2 rewrite List.map_app.
          eapply PIR2_app.
          - rewrite restrict_disj.
            + eapply restrict_subset2; eauto.
              do 2 rewrite take_zip.
              rewrite take_app_eq; [|eauto with len].
              rewrite take_app_eq; [|eauto with len].
              eapply ominus'_Some_oto_list.
              eapply PIR2_take. eapply PIR2_addAdds'.
              eauto with len.
              eapply PIR2_combineParams_get;
                [ eapply computeParametersF_length_pair; eauto with len
                | eauto with len
                | eapply zip_get; eauto
                | reflexivity ].
            + intros.
              inv_get.
              Opaque to_list.

              pose proof (H10 _ H12).
              edestruct computeParameters_isCalledFrom_get_Some; try eapply H6;
                eauto with len; dcr; subst.
              intros; edestruct H2; eauto.
              pose proof (H10 _ H15).
              edestruct computeParameters_isCalledFrom_get_Some; try eapply H7;
                eauto with len; dcr; subst.
              intros; edestruct H2; eauto.

              simpl.
              repeat rewrite of_list_app.
              repeat rewrite of_list_3.
              eapply disj_minus.
              rewrite (meet_comm _ (getAnn lvs)) at 1.
              rewrite union_meet_distr_r. rewrite union_meet_distr_r.
              eapply union_incl_split.

              eapply incl_union_incl_minus. eapply incl_union_left.
              eapply incl_meet_split. eapply incl_union_right.
              eapply incl_list_union; [ eapply map_get_1; try eapply H5 | ].
              clear_all; cset_tac.
              clear_all; cset_tac.
              eapply incl_union_incl_minus. eapply incl_union_left.
              revert H12 H6. clear_all. cset_tac'.
              exfalso; eapply n0.
              eapply incl_list_union.
              eapply map_get_1. eapply get_take; eauto.
              reflexivity. eauto.

          - rewrite restrict_comp_meet.
            pose proof (H10 _ H12).
            edestruct computeParameters_isCalledFrom_get_Some; try eapply H6;
              eauto with len; dcr; subst.
            intros; edestruct H2; eauto.
            simpl.

            repeat rewrite of_list_app. repeat rewrite of_list_3.
            set (XX:=(list_union (oget
                                ⊝ take ❬F❭
                                    (olist_union (snd ⊝ computeParametersF F als Lv ZL AP)
                                     (snd
                                        (computeParameters ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))
                                           (fst ⊝ F ++ ZL) (tab {} ‖F‖ ++ AP) t alb))))
                                 ∪ list_union (fst ∘ of_list ⊝ F))).

            assert (lvsEQ:
                      lv ∩ (getAnn lvs \ (of_list (fst Zs) ∪
                                                  (XX ∩ (getAnn lvs \ of_list (fst Zs)) ∪ x)))
                         [=]
                         (getAnn lvs \ (of_list (fst Zs) ∪
                                                (XX ∩ (getAnn lvs \ of_list (fst Zs)) ∪ x)))). {
              rewrite meet_comm. symmetry. eapply incl_meet.
              rewrite <- H3. subst XX.
              rewrite <- H14.
              clear_all; cset_tac.
            }
            rewrite lvsEQ.
            rewrite restrict_disj.
            + eapply restrict_subset2; eauto.
              do 2 rewrite drop_zip.
              repeat rewrite drop_length_ass; eauto with len.
              eapply zip_ominus_contra; eauto with len.
              eapply PIR2_drop; eauto.
              eapply PIR2_addAdds'; eauto with len.
              eapply PIR2_combineParams_get;
                [ | eauto with len | eauto using zip_get_eq | reflexivity].
              eapply computeParametersF_length_pair; eauto with len.
            + intros. inv_get.
              unfold ominus', lminus in H15.
              destruct x3; invc H15. simpl in *.
              subst XX.
              revert H5 H6. clear_all.
              intros; hnf; intros. cset_tac'.
              * eapply H8; eauto.
                eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
                eauto.
              * eapply H0; eauto.
                eapply incl_list_union.
                eapply map_get_1.
                eapply get_take; eauto using get_range. reflexivity.
                eauto.
        }
      * eapply PIR2_addAdds'; eauto with len.
        eapply PIR2_combineParams_get; [ | | | reflexivity].
        eapply computeParametersF_length_pair; eauto with len.
        eauto with len. eapply zip_get_eq; eauto.
    + rewrite <- List.map_app. rewrite <- take_eta.
      eapply trs_monotone_DL_AP.
      eapply IHLIVE; eauto using PIR2_Subset_tab_extend with len.
      * { rewrite (take_eta (length F) (zip ominus' _ _)).
          rewrite List.map_app.
          eapply PIR2_app.
          - eapply PIR2_restrict.
            do 2 rewrite take_zip.
            rewrite take_app_eq; [|eauto with len].
            rewrite take_app_eq; [|eauto with len].
            eapply ominus'_Some_oto_list.
            eapply PIR2_take. eapply PIR2_addAdds'.
            eauto with len.
            eapply PIR2_combineParams; [| reflexivity].
            eapply computeParametersF_length_pair; eauto with len.
          - eapply restrict_subset2; eauto.
            do 2 rewrite drop_zip.
            repeat (rewrite drop_length_ass; [| eauto with len]).
            eapply zip_ominus_contra.
            eapply PIR2_drop; eauto.
            eapply PIR2_addAdds'. eauto with len.
            eapply PIR2_combineParams; [| reflexivity].
            eapply computeParametersF_length_pair; eauto with len.
        }
      * eapply PIR2_addAdds'; eauto with len.
        eapply PIR2_combineParams; [|reflexivity].
        eapply computeParametersF_length_pair; eauto with len.
Qed.


Lemma is_trs b s lv
: live_sound Imperative nil nil s lv
  -> noUnreachableCode (isCalled b) s
  -> trs nil nil s lv (fst (computeParameters nil nil nil s lv)).
Proof.
  intros.
  assert (snd (computeParameters nil nil nil s lv) = nil). {
    exploit computeParameters_AP_LV; eauto.
    inv H1; eauto.
  }
  exploit computeParameters_trs; eauto; try reflexivity.
  simpl in *. rewrite H1 in H2. eauto.
Qed.
