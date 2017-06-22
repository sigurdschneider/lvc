Require Import CSet Util Map.
Require Import Env IL Alpha Annotation RenamedApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint RenameApart FreshGen.

Set Implicit Arguments.

Lemma rename_apart_alpha' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ domain FG fi
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (renameApart' FG fi ϱ s)) s.
Proof.
  revert fi ϱ ϱ'.
  induction s using stmt_ind'; simpl; intros; repeat let_pair_case_eq; subst;
  simpl in * |- *; eauto using alpha.

  - econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; try eassumption. eauto with cset.
    eapply IHs; eauto.
    + rewrite <- fresh_domain_spec; eauto.
      rewrite <- H. rewrite lookup_set_update_in_union; eauto.
      rewrite <- lookup_set_union_incl; eauto; try reflexivity.
      cset_tac.
    + eapply inverse_on_update_inverse. intuition.
      eapply inverse_on_incl; try eassumption. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                         lookup_set ϱ ((freeVars s \ {{x}}) ∪ Exp.freeVars e)).
      rewrite lookup_set_union; cset_tac; intuition.
      rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor; eauto.
    + eapply alpha_op_sym. eapply alpha_op_rename_injective.
      eapply inverse_on_incl; try eassumption. eapply incl_right.
    + eapply IHs1; eauto.
      * eapply Subset_trans; try eassumption. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_right.
      * eapply inverse_on_incl; try eassumption.
        rewrite union_assoc, union_comm. eapply incl_right.
    + eapply IHs2; eauto.
      * rewrite <- renameApart'_domain; eauto.
        rewrite <- H. repeat rewrite lookup_set_union; cset_tac; intuition.
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
    + intros. inv_get. len_simpl. inv_get. rewrite fresh_list_len; eauto.
    + intros. inv_get; len_simpl. inv_get.
      * eapply H; eauto.
        -- rewrite lookup_set_update_with_list_in_union_length; eauto.
           rewrite <- fresh_list_domain_spec; eauto.
           rewrite union_comm. eapply incl_union_lr; eauto.
           rewrite <- domain_incl_renameApartFRight; eauto.
           rewrite <- H0.
           eapply lookup_set_incl; eauto.
           eapply incl_union_left.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
           rewrite fresh_list_len; eauto.
        -- eapply inverse_on_update_fresh; eauto.
           eapply inverse_on_incl; try eassumption. eauto.
           eapply incl_union_left.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
           eapply fresh_list_nodup; eauto.
           rewrite fresh_list_len; eauto.
           symmetry. eapply disj_1_incl; eauto.
           eapply fresh_list_disj; eauto.
           rewrite <- domain_incl_renameApartFRight; eauto.
           rewrite <- H0. eapply lookup_set_incl; eauto.
           eapply incl_union_left.
           eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
    + eapply IHs; eauto.
      * rewrite <- domain_incl_renameApartF; eauto.
        rewrite <- H0 at 1.
        rewrite lookup_set_union; eauto with cset.
      * eapply inverse_on_incl; try eassumption. eauto.
Qed.

Lemma rename_apart_alpha {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi s
  : alpha id id (rename_apart FG (domain_add FG fi (freeVars s)) s) s.
Proof.
  eapply rename_apart_alpha'; eauto.
  + eapply lookup_set_on_id. rewrite <- domain_add_spec; eauto with cset.
  + eapply inverse_on_id.
Qed.
