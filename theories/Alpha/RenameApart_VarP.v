Require Import Util CSet Var.
Require Import StableFresh.
Require Import IL VarP RenameApart FreshGen.


Lemma renameApart_var_P Fi (FG:FreshGen var Fi) (FGS:FreshGenSpec FG) fi (P:var -> Prop) (ϱ:env var) s
      (Pfresh:forall fi x, P (fst (fresh FG fi x)))
      (Pfresh_list:forall fi Z, forall (x:var), x ∈ of_list (fst (fresh_list FG fi Z)) -> P x)
      (ren:forall x, x ∈ freeVars s -> P (ϱ x))
  : var_P P (snd (renameApart FG fi ϱ s)).
Proof.
  revert ϱ ren fi.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - econstructor; eauto.
    + eapply IHs; eauto.
      * intros; lud; eauto.
        eapply ren. cset_tac.
    + rewrite freeVars_renameExp. unfold lookup_set.
      hnf; intros. cset_tac.
  - econstructor; eauto.
    + rewrite rename_op_freeVars; eauto. unfold lookup_set.
      hnf; intros. cset_tac.
    + eapply IHs1; eauto. cset_tac.
    + eapply IHs2; eauto. cset_tac.
  - econstructor.
    rewrite freeVars_rename_op_list. unfold lookup_set.
    hnf; intros. cset_tac.
  - econstructor.
    rewrite rename_op_freeVars; eauto. unfold lookup_set.
    hnf; intros. cset_tac.
  - econstructor; eauto.
    + intros. inv_get; len_simpl; inv_get.
      eapply H; eauto.
      intros. decide (x ∈ of_list (fst x0)).
      * edestruct update_with_list_lookup_in_list as [? [? [? [? [? [? ?]]]]]]; try eapply i.
        Focus 2.
        rewrite H4.
        eapply get_in_of_list in H3.
        eapply Pfresh_list; eauto.
        rewrite fresh_list_len; eauto.
      * rewrite lookup_set_update_not_in_Z; eauto.
        eapply ren.
        eapply incl_left.
        eapply incl_list_union; [| reflexivity|]; eauto.
        cset_tac.
    + intros.
      intros. inv_get.
      hnf; intros.
      eapply Pfresh_list; eauto.
    + eapply IHs; eauto.
      cset_tac.
Qed.
