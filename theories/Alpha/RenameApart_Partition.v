Require Import CSet Util Map SetOperations.
Require Import Env IL Alpha Fresh Annotation OptionR.
Require Import Liveness Coherence Restrict RenamedApart RenameApart_Liveness.
Require Import LabelsDefined PairwiseDisjoint AppExpFree.
Require Import InfinitePartition MapSep AnnP.

Set Implicit Arguments.

Inductive locally_sep (p:inf_partition) (rho:env var)
  : stmt -> ann (set var) -> Prop :=
| RNOpr x b lv e (al:ann (set var))
  :  locally_sep p rho  b al
     -> sep p lv rho
     -> locally_sep p rho (stmtLet x e b) (ann1 lv al)
| RNIf x b1 b2 lv (alv1 alv2:ann (set var))
  :  sep p lv rho
     -> locally_sep p rho b1 alv1
     -> locally_sep p rho b2 alv2
     -> locally_sep p rho (stmtIf x b1 b2) (ann2 lv alv1 alv2)
| RNGoto l Y lv
  : sep p lv rho
    -> locally_sep p rho (stmtApp l Y) (ann0 lv)
| RNReturn x lv
  : sep p lv rho
    -> locally_sep p rho (stmtReturn x) (ann0 lv)
| RNLet F b lv alvs alvb
  : length F = length alvs
    -> (forall n Zs alv, get F n Zs -> get alvs n alv -> locally_sep p rho (snd Zs) alv)
    -> locally_sep p rho b alvb
    -> sep p lv rho
    -> locally_sep p rho (stmtFun F b) (annF lv alvs alvb).

Definition part_bounded (p:inf_subset) (k:nat) : ⦃nat⦄ -> Prop
  := fun a => cardinal (filter p a) <= k.

Instance part_bounded_impl p k
  : Proper (flip Subset ==> impl) (part_bounded p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; intros.
  rewrite H. eauto.
Qed.

Instance part_bounded_iff p k
  : Proper (Equal ==> iff) (part_bounded p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; split;
  rewrite H; eauto.
Qed.

Lemma part_dich (p:inf_partition) x
  : (part_1 p x /\ (part_2 p x -> False)) \/ (part_2 p x /\ (part_1 p x -> False)).
Proof.
  destruct (part_cover p x);
    pose proof (part_disj p x); cset_tac.
Qed.

Lemma sep_filter_map_comm p (ϱ:var -> var) lv
  : sep p lv ϱ
    -> map ϱ (filter (part_1 p) lv) [=] filter (part_1 p) (map ϱ lv).
Proof.
  intros [GT LE]. cset_tac'.
  - eexists x; cset_tac'.
    pose proof (part_dich p x).
    pose proof (part_disj p (ϱ x)).
    cset_tac.
Qed.

Lemma part_bounded_sep p ϱ k lv
  (BND:part_bounded (part_1 p) k lv)
  (SEP:sep p lv ϱ)
  : part_bounded (part_1 p) k (lookup_set ϱ lv).
Proof.
  unfold part_bounded in *.
  unfold lookup_set. rewrite <- sep_filter_map_comm; eauto.
  rewrite cardinal_map; eauto.
Qed.

Lemma filter_union X `{OrderedType X} (p:X->bool) s t `{Proper _ (_eq ==> eq) p}
  : filter p (s ∪ t) [=] filter p s ∪ filter p t.
Proof.
  cset_tac.
Qed.

Lemma least_fresh_part_1_back (p:inf_partition) G x
  : part_1 p (least_fresh_part p G x) -> part_1 p x.
Proof.
  intros.
  decide (part_1 p x); eauto.
  destruct (part_cover p x); eauto.
  eapply least_fresh_part_2 in i.
  edestruct (part_disj p); eauto.
Qed.

Lemma least_fresh_part_2_back (p:inf_partition) G x
  : part_2 p (least_fresh_part p G x) -> part_2 p x.
Proof.
  intros.
  decide (part_2 p x); eauto.
  destruct (part_cover p x); eauto.
  eapply least_fresh_part_1 in i.
  edestruct (part_disj p); eauto.
Qed.

Lemma cardinal_filter_part p G Z
      (UNIQ:NoDupA eq Z)
  : cardinal (filter (part_1 p)
                     (of_list (fresh_list_stable (stable_fresh_part p) G Z)))
    = cardinal (filter (part_1 p) (of_list Z)).
Proof.
  general induction Z; simpl.
  - reflexivity.
  - decide (part_1 p a).
    + rewrite filter_add_in; eauto using least_fresh_part_1.
      rewrite filter_add_in; eauto.
      rewrite !add_cardinal_2; eauto.
      * intro. inv UNIQ. cset_tac'.
        rewrite <- InA_in in H0. eauto.
      * exploit (fresh_list_stable_spec (stable_fresh_part p));
        eauto using least_fresh_part_fresh.
        cset_tac'.
        eapply H; cset_tac.
    + rewrite filter_add_notin; eauto.
      rewrite filter_add_notin; eauto.
      eauto using least_fresh_part_1_back.
Qed.

Lemma bnd_update_list p ϱ k a Z G
      (BDN:part_bounded (part_1 p) k (getAnn a))
      (incl: of_list Z ⊆ getAnn a)
      (SEP:sep p (getAnn a \ of_list Z) ϱ)
      (incl2 : map ϱ (getAnn a \ of_list Z) ⊆ G)
      (UNIQ:NoDupA eq Z)
  : part_bounded (part_1 p) k
    (lookup_set ϱ (getAnn a \ of_list Z)
     ∪ of_list
         (fresh_list_stable (stable_fresh_part p) G Z)).
Proof.
  unfold part_bounded, lookup_set in *.
  rewrite filter_union; eauto.
  rewrite <- sep_filter_map_comm; eauto using sep_incl with cset.
  rewrite filter_difference; eauto.
  rewrite union_cardinal_inter.
  rewrite cardinal_filter_part; eauto.
  setoid_rewrite cardinal_1 at 3.
  - pose proof (@cardinal_map _ _ _ _
                              (filter (part_1 p) (getAnn a) \ filter (part_1 p) (of_list Z)) ϱ _).
    rewrite cardinal_difference' in H.
    + assert (cardinal (filter (part_1 p) (of_list Z)) <= cardinal (filter (part_1 p) (getAnn a))). {
        rewrite incl; eauto.
      }
      omega.
    + rewrite incl; eauto.
  - eapply empty_is_empty_2.
    eapply disj_intersection.
    hnf; intros. eapply fresh_list_stable_spec.
    cset_tac.
    rewrite <- incl2. cset_tac.
Qed.


Lemma sep_update_part p ϱ lv x G
      (SEP:sep p (lv \ singleton x) ϱ)
  : sep p lv (ϱ [x <- least_fresh_part p G x]).
Proof.
  unfold sep in SEP; dcr.
  hnf; split; intros; lud; cset_tac';
    eauto using least_fresh_part_1,least_fresh_part_2.
Qed.


Lemma ann_P_setTopAnn A (P:A->Prop) an a
  : ann_P P an
    -> P a
    -> ann_P P (setTopAnn an a).
Proof.
  intros AN PA; inv AN; simpl; econstructor; eauto.
Qed.

Lemma sep_update_list p ϱ (Z:params) (lv:set nat) F als n G
      (ND:NoDupA eq Z) (SEP:sep p (lv \ of_list Z) ϱ) (incl:of_list Z [<=] lv)
  : sep p lv
        (ϱ [Z <--
              fresh_list_stable (stable_fresh_part p)
              (snd
                 (renameApartF_live (stable_fresh_part p) renameApart_live G ϱ
                                    {} (take n F) (take n als)) ∪ G) Z]).
Proof.
  hnf; split; intros; decide (x ∈ of_list Z).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H4. cset_tac'.
    exploit fresh_list_stable_get; try eapply H3; eauto; dcr.
    subst. get_functional. eapply least_fresh_part_1; eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H4. cset_tac'.
    exploit fresh_list_stable_get; try eapply H3; eauto; dcr.
    dcr. subst. get_functional. eapply least_fresh_part_2; eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
Qed.

Lemma renameApart_sep o ZL LV DL p ϱ k lv G s (isFnc:isFunctional o)
  (AN:ann_P (part_bounded (part_1 p) k) lv)
  (LS: live_sound o ZL LV s lv)
  (SEP: sep p (getAnn lv) ϱ)
  (SRD:srd DL s lv)
  (iEQ:PIR2 (ifFstR Equal) DL (LV \\ ZL))
  (Incl:map ϱ (getAnn lv) ⊆ G)
  : ann_P (part_bounded (part_1 p) k)
          (snd (renameApart_live (stable_fresh_part p) ϱ G s lv)).
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
