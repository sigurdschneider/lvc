Require Import CSet Util Map.
Require Import Env IL Alpha Fresh Annotation RenamedApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint RenameApart.

Set Implicit Arguments.

Lemma rename_apart_alpha' G ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ G
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (renameApart' ϱ G s)) s.
Proof.
  revert G ϱ ϱ'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; subst;
  simpl in * |- *; eauto using alpha.

  - econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; try eassumption. eauto with cset.
    eapply IH; eauto.
    + rewrite <- H at 3. rewrite lookup_set_update_in_union; eauto.
      cset_tac; intuition. right.
      eapply lookup_set_union_incl; eauto. lset_tac.
    + eapply inverse_on_update_inverse. intuition.
      eapply inverse_on_incl; try eassumption. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                         lookup_set ϱ ((freeVars s \ {{x}}) ∪ Exp.freeVars e)).
      rewrite lookup_set_union; cset_tac; intuition.
      rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor; eauto.
    + eapply alpha_op_sym. eapply alpha_op_rename_injective.
      eapply inverse_on_incl; try eassumption. eapply incl_right.
    + eapply IH; eauto.
      * eapply Subset_trans; try eassumption. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_right.
      * eapply inverse_on_incl; try eassumption.
        rewrite union_assoc, union_comm. eapply incl_right.
    + eapply IH; eauto.
      * rewrite <- H at 1. repeat rewrite lookup_set_union; cset_tac; intuition.
      * eapply inverse_on_incl; try eassumption.
        cset_tac; intuition.
  - econstructor. rewrite map_length; eauto.
    intros. edestruct map_get_4; eauto; dcr; get_functional; subst.
    eapply alpha_op_sym. eapply alpha_op_rename_injective.
    eapply inverse_on_incl; try eassumption. eapply incl_list_union; try reflexivity.
    eapply map_get_1; eauto.

  - econstructor; eauto. eapply alpha_op_sym.
    eapply alpha_op_rename_injective.
    eapply inverse_on_incl; try eassumption. reflexivity.
  - econstructor.
    + rewrite rev_length, renameApartF_length; eauto.
    + intros. eapply get_rev in H1.
      rewrite renameApartF_length in H1.
      edestruct get_fst_renameApartF as [? [? [? ]]]; dcr; eauto.
      exploit (get_range H2).
      orewrite (length F - S (length F - S n) = n) in H4. get_functional; subst.
      eauto.
    + intros.
      eapply get_rev in H1.
      rewrite renameApartF_length in H1.
      edestruct get_fst_renameApartF as [? [? [? ]]]; dcr; eauto.
      exploit (get_range H2).
      orewrite (length F - S (length F - S n) = n) in H4. get_functional; subst.
      rewrite H6.
      erewrite renameApart'_agree. eapply IH; eauto.
      * rewrite lookup_set_update_with_list_in_union_length; eauto.
        eapply union_subset_3; eauto.
        rewrite <- H5.
        rewrite <- H.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      * eapply inverse_on_update_fresh; eauto.
        eapply inverse_on_incl; try eassumption. eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        symmetry. eapply disj_1_incl; eauto.
        rewrite <- H. eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      * symmetry. eapply agree_on_incl; eauto with cset.
    + eapply IH; eauto.
      * rewrite <- H at 1.
        rewrite lookup_set_union; eauto with cset.
      * eapply inverse_on_incl; try eassumption. eauto.
Qed.

Lemma rename_apart_alpha s
  : alpha id id (rename_apart s) s.
Proof.
  eapply rename_apart_alpha'.
  + eapply lookup_set_on_id; reflexivity.
  + eapply inverse_on_id.
Qed.
