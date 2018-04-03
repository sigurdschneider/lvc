Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take Subset1 ListMax.
Require Import Val Var StableFresh Envs IL Annotation Liveness.Liveness MoreList SetOperations AnnP.
Require Import Coherence Coherence.Allocation RenamedApart AllocationAlgo.
Require Import RenamedApart_Liveness LabelsDefined Restrict InfinitePartition MapSep.
Require Import RenameApart_Partition Filter.

Set Implicit Arguments.

Inductive locally_sep (p:inf_partition var) (rho:env var)
  : ann (set var) -> Prop :=
| RNOpr lv (al:ann (set var))
  :  locally_sep p rho al
     -> sep var p lv rho
     -> locally_sep p rho (ann1 lv al)
| RNIf lv (alv1 alv2:ann (set var))
  :  sep var p lv rho
     -> locally_sep p rho alv1
     -> locally_sep p rho alv2
     -> locally_sep p rho (ann2 lv alv1 alv2)
| RNGoto lv
  : sep var p lv rho
    -> locally_sep p rho (ann0 lv)
| RNReturn lv
  : sep var p lv rho
    -> locally_sep p rho (ann0 lv)
| RNLet lv alvs alvb
  : (forall n alv, get alvs n alv -> locally_sep p rho alv)
    -> locally_sep p rho alvb
    -> sep var p lv rho
    -> locally_sep p rho (annF lv alvs alvb).

Lemma locally_separate p ϱ lv
  : locally_sep p ϱ lv -> sep var p (getAnn lv) ϱ.
Proof.
  inversion 1; eauto.
Qed.

Lemma locally_sep_ext D p ϱ ϱ' lv ra s
      (LS:locally_sep p ϱ lv)
      (Incl1:ann_R (fun x y => x ⊆ fst y) lv ra)
      (RA:renamedApart s ra)
      (Incl2:fst (getAnn ra) ∪ snd (getAnn ra) ⊆ D)
      (Agr:agree_on eq D ϱ ϱ')
  : locally_sep p ϱ' lv.
Proof.
  general induction LS;
    pose proof (ann_R_get Incl1) as incl; simpl in incl;
      invt renamedApart;
      invt @ann_R; simpl in *; pe_rewrite; set_simpl.
  - econstructor.
    + eapply IHLS; eauto.
      pe_rewrite. rewrite <- Incl2; clear; cset_tac.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- H8. eauto with cset.
  - econstructor; eauto.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- H11. eauto with cset.
    + eapply IHLS1; eauto; pe_rewrite.
      rewrite <- Incl2. clear; cset_tac.
    + eapply IHLS2; eauto; pe_rewrite.
      rewrite <- Incl2. clear; cset_tac.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor; eauto.
    + intros. inv_get.
      eapply H0; eauto.
      rewrite <- Incl2.
      edestruct H4; eauto; dcr.
      rewrite H11.
      rewrite <- incl_list_union; eauto using zip_get; [|reflexivity].
      unfold defVars. clear; cset_tac.
    + eapply IHLS; eauto.
      pe_rewrite. rewrite <- Incl2.
      clear; cset_tac.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- incl; eauto.
Qed.

Lemma sep_part_bounded p k lv ϱ
      (AN:ann_P (part_bounded var (part_1 p) k) lv)
      (LS:locally_sep p ϱ lv)
  : ann_P (part_bounded var (part_1 p) k) (mapAnn (lookup_set ϱ) lv).
Proof.
  general induction AN; invt locally_sep;
    simpl in *; econstructor; eauto using part_bounded_sep.
  - intros; inv_get; eauto.
Qed.

Instance sep_agree_morph_impl p lv
  : Proper (agree_on eq lv ==> impl) (sep var p lv).
Proof.
  unfold Proper, respectful, impl.
  eauto using sep_agree.
Qed.

Instance sep_agree_morph_iff p lv
  : Proper (agree_on eq lv ==> iff) (sep var p lv).
Proof.
  unfold Proper, respectful; split.
  eauto using sep_agree.
  symmetry in H. eauto using sep_agree.
Qed.

Lemma sep_update_part p o ϱ lv x G
      (SEP:sep var p (lv \ singleton x) ϱ)
  : sep var p lv (ϱ [x <- least_fresh_part p o G x]).
Proof.
  unfold sep in SEP; dcr.
  hnf; split; intros; lud.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
Qed.

Lemma regAssign_sep p o (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (allocOK:regAssign p o s alv ϱ = Success ϱ')
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (Sep:sep var p (getAnn alv) (findt ϱ default_var))
      (sd:renamedApart s ra)
      (incl:ann_R (fun x y => x ⊆ fst y) alv ra)
: locally_sep p (findt ϱ' default_var) alv.
Proof.
  intros.
  general induction LS; simpl in *;
    pose proof (ann_R_get incl) as incl'; simpl in incl';
      invt @ann_R;
      try monadS_inv allocOK; invt renamedApart;
        pe_rewrite; simpl in *; set_simpl.

  - econstructor; eauto. eapply IHLS; eauto.
    + eapply injective_on_update_cmap_fresh; eauto using injective_on_incl.
    + rewrite <- map_update_update_agree.
      eapply sep_update_part; eauto.
    + exploit regAssign_renamedApart_agree; eauto; pe_rewrite.
      eapply sep_agree.
      * eapply agree_on_incl; eauto with cset.
      * rewrite <- map_update_update_agree.
        eapply sep_update_part; eauto.
  - exploit regAssign_renamedApart_agree; try eapply EQ; eauto; pe_rewrite.
    exploit IHLS1; try eapply EQ; eauto using injective_on_incl, sep_incl.
    exploit IHLS2; try eapply EQ0; pe_rewrite; eauto using sep_incl, sep_agree, agree_on_incl.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto using agree_on_incl.
    + exploit regAssign_renamedApart_agree; eauto. pe_rewrite.
      econstructor; eauto.
      * assert (agree_on eq lv (findt ϱ default_var) (findt ϱ' default_var)). {
          etransitivity; eauto using agree_on_incl.
        }
        rewrite <- H9; eauto.
      * exploit regAssign_renamedApart_agree' as AGR;
          try eapply EQ0; simpl; eauto using live_sound. pe_rewrite.
        instantiate (1:=D ∪ Ds) in AGR.
        eapply locally_sep_ext; eauto.
        pe_rewrite.
        eapply renamedApart_disj in H15; pe_rewrite.
        revert H12 H15. clear_all. cset_tac.
  - econstructor; eauto.
  - econstructor; eauto.
  - exploit regAssign_renamedApart_agreeF' as Agr1;
      eauto using regAssign_renamedApart_agree'. reflexivity.
    instantiate (1:=D) in Agr1.
    exploit regAssign_renamedApart_agree as Agr2;
      try eapply EQ0; simpl; eauto using live_sound.
    assert (AGR:agree_on _eq lv (findt ϱ default_var) (findt x default_var)). {
      eapply agree_on_incl; eauto.
      rewrite disj_minus_eq; eauto using disj_D_defVars.
    }
    exploit (IHLS p); try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
    + assert (DDISJ:forall n  DD' Zs, get F n Zs -> get bns n DD' ->
                                 disj D (defVars Zs DD')). {
        eapply defVars_disj_D; eauto with cset.
      }
      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          inv_get. rename x1 into Zs.
          edestruct (regAssignF_get p o (fst (getAnn x0) ∪ snd (getAnn x0)
                                           ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H22; eauto with len.
          exploit H1; eauto. pe_rewrite.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H12; clear_all; cset_tac.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply disj_lv_take; eauto.
            simpl in *.
            setoid_rewrite <- H12 at 1.
            eapply injective_on_fresh_list; eauto with len.
            + eapply injective_on_incl; eauto.
              eapply H2; eauto.
            + eapply disj_2_incl.
              eapply fresh_list_stable_spec.
              reflexivity.
            + eapply fresh_list_stable_nodup; eauto using least_fresh_part_fresh.
          - exploit H2; eauto; dcr.
            eapply sep_agree. eapply agree_on_incl; eauto.
            + rewrite <- incl_right.
              rewrite disj_minus_eq; eauto.
              eapply disj_lv_take; eauto.
            + eapply sep_update_list; eauto.
          - eapply locally_sep_ext; eauto.
            reflexivity.
            pe_rewrite.
            eapply regAssign_renamedApart_agreeF' in H19;
              eauto using get_drop, drop_length_stable; try reflexivity.
            + eapply regAssign_renamedApart_agree' in EQ0; simpl; eauto using live_sound.
              etransitivity; eapply agree_on_incl; try eassumption.
              * rewrite disj_minus_eq. reflexivity.
                eapply disj_fst_snd_ra; eauto.
              * pe_rewrite.
                rewrite disj_minus_eq. reflexivity.
                eapply disj_fst_snd_Dt; eauto.
            + intros.
              eapply regAssign_renamedApart_agree'; eauto using get_drop, drop_get.
        }
      * pe_rewrite.
        eapply sep_agree; eauto.
        etransitivity; eapply agree_on_incl; eauto.
Qed.
