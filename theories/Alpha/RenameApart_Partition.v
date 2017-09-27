Require Import CSet Util Map SetOperations.
Require Import Envs IL Fresh Annotation OptionR.
Require Import Liveness.Liveness Restrict RenamedApart RenameApart_Liveness.
Require Import LabelsDefined PairwiseDisjoint AppExpFree.
Require Import InfiniteSubset InfinitePartition MapSep AnnP FreshGen.

Set Implicit Arguments.

Lemma bnd_update_list p ϱ k lv Z G
      (BDN:part_bounded var (part_1 p) k lv)
      (incl: of_list Z ⊆ lv)
      (SEP:sep var p (lv \ of_list Z) ϱ)
      (incl2 : map ϱ (lv \ of_list Z) ⊆ G)
      (UNIQ:NoDupA eq Z)
  : part_bounded var (part_1 p) k
                 (lookup_set ϱ (lv \ of_list Z)
                             ∪ of_list (fst (fresh_list_stable (stable_fresh_part p) G Z))).
Proof.
  unfold part_bounded, lookup_set in *.
  rewrite filter_union; eauto.
  rewrite <- sep_filter_map_comm; eauto using sep_incl with cset.
  rewrite filter_difference; eauto.
  rewrite union_cardinal_inter.
  rewrite cardinal_filter_part; eauto.
  setoid_rewrite cardinal_1 at 3.
  - pose proof (@cardinal_map _ _ _ _
                              (filter (part_1 p) lv \ filter (part_1 p) (of_list Z)) ϱ _).
    rewrite cardinal_difference' in H.
    + assert (cardinal (filter (part_1 p) (of_list Z)) <= cardinal (filter (part_1 p) lv)). {
        rewrite incl; eauto.
      }
      omega.
    + rewrite incl; eauto.
  - eapply empty_is_empty_2.
    eapply disj_intersection.
    hnf; intros. eapply (@fresh_list_stable_spec var _).
    cset_tac.
    rewrite <- incl2. cset_tac.
Qed.

Lemma sep_update_list p ϱ (Z:list var) (lv:set var) G
      (ND:NoDupA eq Z) (SEP:sep var p (lv \ of_list Z) ϱ) (incl:of_list Z [<=] lv)
  : sep var p lv
        (ϱ [Z <-- fst (fresh_list_stable (stable_fresh_part p) G Z)]).
Proof.
  hnf; split; intros; decide (x ∈ of_list Z).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H4. cset_tac'.
    exploit (@fresh_list_stable_get var _); try eapply H3; eauto; dcr.
    subst. get_functional. eapply least_fresh_part_1; eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H4. cset_tac'.
    exploit (@fresh_list_stable_get var _); try eapply H3; eauto; dcr.
    dcr. subst. get_functional. eapply least_fresh_part_2; eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
Qed.

(*
Lemma renameApart_sep o ZL LV DL p ϱ k lv fi s (isFnc:isFunctional o)
  (AN:ann_P (part_bounded (part_1 p) k) lv)
  (LS: live_sound o ZL LV s lv)
  (SEP: sep p (getAnn lv) ϱ)
  (SRD:srd DL s lv)
  (iEQ:PIR2 (ifFstR Equal) DL (LV \\ ZL))
  (Incl:map ϱ (getAnn lv) ⊆ domain FG_even_fast fi)
  : ann_P (part_bounded (part_1 p) k)
          (snd (renameApart_live FG_even_fast fi ϱ s lv)).
Proof.
  general induction LS; invt ann_P; invt srd; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - econstructor; eauto using part_bounded_sep.
    eapply IHLS; eauto using restrict_ifFstR, sep_update_part with len.
    rewrite lookup_set_update_in_union; eauto.
    rewrite <- Incl at 3. rewrite <- H0.
    unfold lookup_set. clear; cset_tac.
  - econstructor; eauto using part_bounded_sep with cset.
  - econstructor; eauto using part_bounded_sep.
  - econstructor; eauto using part_bounded_sep.
  - econstructor; eauto using part_bounded_sep.
    + intros; inv_get.
      edestruct (get_fst_renameApartF_live _ _ _ _ _ _ H4); eauto; dcr; subst.
      erewrite !getAnn_snd_renameApart_live in *; eauto.
      eapply ann_P_setTopAnn; eauto.
      * eapply H1; eauto.
        -- exploit H2; eauto; dcr.
           eapply sep_update_list; eauto.
           cases in H16. eauto.
        -- rewrite !zip_app; eauto with len.
           eauto using PIR2_app, PIR2_ifFstR_refl, restrict_ifFstR.
        -- exploit H2; eauto; dcr.
           cases in H16.
           rewrite lookup_set_update_with_list_in_union_length; eauto with len.
           rewrite H16. unfold lookup_set. rewrite Incl.
           clear; cset_tac.
      * exploit H8; eauto.
        exploit H2; eauto; dcr.
        cases in H17.
        rewrite lookup_set_update_with_list_in_union_length; eauto with len.
        eapply ann_P_get in H5.
        rewrite union_comm.
        rewrite union_subset_equal; eauto with cset.
        eapply bnd_update_list; eauto.
        rewrite H17. rewrite Incl.
        clear; cset_tac.
    + eapply IHLS; eauto using restrict_ifFstR.
      * rewrite zip_app;[| eauto with len].
        eauto using PIR2_app, PIR2_ifFstR_refl.
      * rewrite H3, Incl. eauto with cset.
Qed.

Lemma renamedApart_incl VD s ra
      (RA:renamedApart s ra)
      (Incl:fst (getAnn ra) ∪ snd (getAnn ra) ⊆ VD)
  : ann_P (fun x => fst x ∪ snd x ⊆ VD) ra.
Proof.
  general induction RA; simpl in *; econstructor; simpl; set_simpl; pe_rewrite; eauto with cset.
  - intros; inv_get. eapply H1; eauto.
    rewrite <- Incl.
    rewrite <- incl_list_union; eauto using zip_get; [|reflexivity].
    unfold defVars.
    edestruct H2; eauto; dcr.
    rewrite H7. clear; cset_tac.
Qed.*)