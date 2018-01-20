Require Import CMap MapNotations CSet Le Arith.Compare_dec.

Require Import Plus Util Status Take Subset1 Filter.
Require Import Val Var StableFresh Envs IL Annotation Liveness.Liveness MoreList SetOperations.
Require Import Coherence Coherence.Allocation RenamedApart AllocationAlgo InfinitePartition.

Set Implicit Arguments.

Require Import MapNotations.
(** ** the algorithm produces a locally injective renaming *)

Lemma regAssign_correct p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (sd:renamedApart s ra)
      (incl:getAnn alv ⊆ fst (getAnn ra))
: locally_inj (findt ϱ' default_var) s alv.
Proof.
  intros.
  general induction LS; simpl in *;
    try monadS_inv allocOK; invt renamedApart;
      pe_rewrite; simpl in *; set_simpl.
  - exploit regAssign_renamedApart_agree; eauto.
    exploit IHLS; eauto.
    + eapply injective_on_update_cmap_fresh; eauto using injective_on_incl.
    + pe_rewrite. eauto with cset.
    + econstructor; eauto.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      rewrite map_update_update_agree; eauto.
      pe_rewrite.
      revert H5 incl; clear_all; cset_tac.
  - exploit regAssign_renamedApart_agree; try eapply EQ; eauto.
    pe_rewrite.
    exploit IHLS1; try eapply EQ; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto using agree_on_incl.
    + pe_rewrite. eauto with cset.
    + econstructor; eauto.
      * exploit regAssign_renamedApart_agree; eauto. pe_rewrite.
        assert (agree_on eq D (findt ϱ default_var) (findt ϱ' default_var)). {
          etransitivity; eauto.
        }
        eapply injective_on_agree; eauto using agree_on_incl.
      * eapply locally_inj_live_agree; eauto; pe_rewrite;[| eauto with cset].
        exploit regAssign_renamedApart_agree' as AGR;
          try eapply EQ0; simpl; eauto using live_sound.
        pe_rewrite. instantiate (1:=D ∪ Ds) in AGR.
        eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
  - econstructor; eauto.
  - exploit regAssign_renamedApart_agreeF';
    eauto using regAssign_renamedApart_agree'. reflexivity.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    instantiate (1:=D) in H4.
    assert (AGR:agree_on _eq lv (findt ϱ default_var) (findt x default_var)). {
      eapply agree_on_incl; eauto.
      rewrite disj_minus_eq; eauto using disj_D_defVars.
    }
    exploit (IHLS p); try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
    + pe_rewrite. etransitivity; eauto.
    + assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                                 disj D (defVars Zs DD')). {
        eapply defVars_disj_D; eauto with cset.
      }
      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          edestruct (regAssignF_get p (fst (getAnn x0) ∪ snd (getAnn x0)
                                           ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H20; eauto.
          exploit (H1 _ _ _ H13 H14 p); try eapply H19; eauto.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H16; clear_all; cset_tac'.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply disj_lv_take; eauto.
            simpl in *.
            setoid_rewrite <- H16 at 1.
            eapply injective_on_fresh_list; eauto with len.
            + eapply injective_on_incl; eauto.
              eapply H2; eauto.
            + eapply disj_2_incl.
              eapply fresh_list_stable_spec.
              reflexivity.
            + eapply fresh_list_stable_nodup; eauto using least_fresh_part_fresh.
          - eapply lv_incl_fst_ra; eauto.

          - eapply locally_inj_live_agree; try eapply H20; eauto.
            eapply regAssign_renamedApart_agreeF' in H17;
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
            + eapply lv_incl_fst_ra; eauto.
          - eauto with len.
        }
      * eapply injective_on_agree; try eapply inj; eauto.
        etransitivity; eapply agree_on_incl; eauto. pe_rewrite. eauto.
Qed.


Require Import Restrict RenamedApart_Liveness LabelsDefined.

Lemma regAssign_correct_I b p s ang ϱ ϱ' (alv:ann (set var)) ZL Lv
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> noUnreachableCode (isCalled b) s
  -> injective_on (getAnn alv) (findt ϱ default_var)
  -> regAssign p s alv ϱ = Success ϱ'
  -> locally_inj (findt ϱ' default_var) s alv.
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply regAssign_correct; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac.
Qed.