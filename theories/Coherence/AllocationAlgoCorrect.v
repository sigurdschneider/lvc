Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take.
Require Import Val Var Env IL Annotation Liveness Fresh MoreList SetOperations.
Require Import Coherence Allocation RenamedApart AllocationAlgo.

Set Implicit Arguments.


(** ** the algorithm produces a locally injective renaming *)

Lemma regAssign_correct (ϱ:Map [var,var]) ZL Lv s alv ϱ' al
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (allocOK:regAssign s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
: locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  general induction LS; simpl in *; try monadS_inv allocOK; invt renamedApart;
  pe_rewrite; eauto 10 using locally_inj, injective_on_incl.
  - exploit IHLS; try eapply allocOK; pe_rewrite; eauto with cset.
    + eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_incl.
      eapply injective_on_fresh;
        eauto using injective_on_incl, least_fresh_spec with cset.
      eauto with cset.
    + pe_rewrite. eauto with cset.
    + exploit regAssign_renamedApart_agree;
      try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *; simpl in *.
      econstructor; eauto using injective_on_incl.
      * eapply injective_on_agree; try eapply inj.
        eapply agree_on_incl.
        eapply agree_on_update_inv.
        rewrite map_update_update_agree; eauto.
        pe_rewrite.
        revert H5 incl; clear_all; cset_tac; intuition.
  - exploit regAssign_renamedApart_agree;
    try eapply EQ; simpl; eauto using live_sound.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    pe_rewrite.
    simpl in *.
    exploit IHLS1; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
    eapply injective_on_incl; eauto.
    eapply injective_on_agree; eauto using agree_on_incl.
    rewrite H12; simpl. rewrite <- incl; eauto.
    econstructor; eauto.
    assert (agree_on eq D (findt ϱ 0) (findt ϱ' 0)). etransitivity; eauto.
    eapply injective_on_agree; eauto. eauto using agree_on_incl.
    eapply locally_inj_live_agree. eauto. eauto. eauto.
    rewrite H11; simpl; eauto.
    exploit regAssign_renamedApart_agree'; try eapply EQ0; simpl; eauto using live_sound.
    pe_rewrite.
    eapply agree_on_incl. eapply H13. instantiate (1:=D ∪ Ds).
    pose proof (renamedApart_disj H9).
    pe_rewrite.
    revert H6 H14; clear_all; cset_tac; intuition; eauto.
    rewrite H11; simpl. rewrite <- incl; eauto.

  - exploit regAssign_renamedApart_agreeF;
    eauto using regAssign_renamedApart_agree'. reflexivity.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    exploit IHLS; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto. instantiate (1:=D).
      rewrite disj_minus_eq; eauto. simpl in *.
      symmetry. rewrite <- list_union_disjunct.
      intros. inv_zip H12. edestruct H8; eauto; dcr.
      unfold defVars. symmetry. eapply disj_app; split; eauto.
      symmetry; eauto.
      exploit H7; eauto. eapply renamedApart_disj in H17.
      eapply disj_1_incl; eauto. rewrite H16. eauto with cset.
    + pe_rewrite. etransitivity; eauto.
    +
      assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                              disj D (defVars Zs DD')).
      {
        eapply renamedApart_disj in sd. eauto using defVars_disj_D.
      }

      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          edestruct (regAssignF_get (fst (getAnn x0) ∪ snd (getAnn x0) ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H21; eauto.
          exploit H1; try eapply H19; eauto.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H17; clear_all; cset_tac; intuition.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply renamedApart_disj in sd.
            simpl in *.
            rewrite <- H17. symmetry. rewrite disj_app. split; symmetry.
            eapply disj_1_incl. eapply disj_2_incl. eapply sd.
            rewrite <- H13. eapply incl_union_left.
            hnf; intros ? A. eapply list_union_get in A. destruct A. dcr.
            inv_get.
            eapply incl_list_union; eauto using zip_get.
            reflexivity. cset_tac.
            edestruct H2; eauto; dcr. rewrite <- incl. eauto.
            eapply disj_1_incl.
            eapply defVars_take_disj; eauto. unfold defVars.
            eauto with cset.
            setoid_rewrite <- H17 at 1.
            eapply injective_on_fresh_list; eauto.
            eapply injective_on_incl; eauto.
            eapply H2; eauto.
            eapply disj_intersection.
            eapply disj_2_incl. eapply fresh_list_spec. eapply least_fresh_spec.
            reflexivity.
            edestruct H8; eauto.
            eapply fresh_list_nodup, least_fresh_spec.
          - edestruct H8; eauto; dcr. rewrite H17.
            exploit H2; eauto; dcr. rewrite incl in H26; simpl in *.
            rewrite <- H26. clear_all; cset_tac; intuition.
          - eapply locally_inj_live_agree; try eapply H17; eauto.
            eapply regAssign_renamedApart_agreeF in H18;
              eauto using get_drop, drop_length_stable; try reflexivity.
            + eapply regAssign_renamedApart_agree' in EQ0; simpl; eauto using live_sound.
              etransitivity; eapply agree_on_incl; try eassumption.
              * rewrite disj_minus_eq. reflexivity.
                {
                  edestruct H8; eauto; dcr. rewrite H20.
                  rewrite union_comm. rewrite <- union_assoc.
                  symmetry; rewrite disj_app; split; symmetry.
                  - eapply disj_1_incl. eapply defVars_drop_disj; eauto.
                    unfold defVars. eauto with cset.
                  - eapply renamedApart_disj in sd; simpl in sd.
                    eapply disj_2_incl; eauto.
                    rewrite <- H13. eapply incl_union_left.
                    rewrite <- drop_zip; eauto.
                    eapply list_union_drop_incl; eauto.
                }
              * pe_rewrite.
                rewrite disj_minus_eq. reflexivity.
                {
                  edestruct H8; eauto; dcr. rewrite H20.
                  rewrite union_comm. rewrite <- union_assoc.
                  symmetry; rewrite disj_app; split; symmetry.
                  rewrite union_comm; eauto.
                  eapply renamedApart_disj in H10. pe_rewrite. eapply H10.
                }
            + intros.
              eapply regAssign_renamedApart_agree'; eauto using get_drop, drop_get.
            + intros. edestruct H8; eauto; dcr. rewrite H20.
              exploit H2; eauto; dcr. rewrite incl in H27. simpl in *.
              revert H27; clear_all; cset_tac; intuition.
              decide (a ∈ of_list (fst Zs)); intuition.
        }
      * eapply injective_on_agree; try eapply inj; eauto.
        etransitivity; eapply agree_on_incl; eauto.
        rewrite disj_minus_eq; eauto. simpl in *.
        symmetry. rewrite <- list_union_disjunct.
        intros. inv_zip H14. edestruct H8; eauto; dcr.
        unfold defVars. symmetry. eapply disj_app; split; eauto.
        symmetry; eauto.
        exploit H7; eauto. eapply renamedApart_disj in H18.
        eapply disj_1_incl; eauto. rewrite H17. eauto with cset.
        pe_rewrite. eauto.
Qed.


Require Import Restrict RenamedApart_Liveness LabelsDefined.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_correct]
    above, which we did prove by induction. *)

Lemma regAssign_correct' s ang ϱ ϱ' (alv:ann (set var)) ZL Lv
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> noUnreachableCode isCalled s
  -> injective_on (getAnn alv) (findt ϱ 0)
  -> regAssign s alv ϱ = Success ϱ'
  -> locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply regAssign_correct; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac.
Qed.
