Require Import Util CSet Var.
Require Import StableFresh.
Require Import IL VarP RenameApart.


Inductive FreshGenVarProp (P:var -> Prop) (FG:FreshGen) : Prop :=
  {
    fresh_var_inv : forall x, P (fst (fresh FG x));
    fresh_var_list_inv : forall Z x, x ∈ of_list (fst (fresh_list FG Z)) -> P x;
    fresh_inv : forall x, FreshGenVarProp P (snd (fresh FG x));
    fresh_list_inv : forall Z, FreshGenVarProp P (snd (fresh_list FG Z));
  }.

Local Hint Resolve fresh_inv fresh_list_inv.

Lemma renameApart_var_P (fresh:FreshGen) (P:var -> Prop) (ϱ:env var) s
      (FGVP:FreshGenVarProp P fresh) (FGI:FreshGenVarProp P fresh)
      (ren:forall x, x ∈ freeVars s -> P (ϱ x))
  : var_P P (snd (renameApart' fresh ϱ s)).
Proof.
  revert ϱ ren fresh fresh FGVP FGI.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - econstructor; eauto.
    + eapply IHs; eauto.
      * intros; lud; eauto using fresh_var_inv. eapply fresh_var_inv. eauto.
        eapply ren. cset_tac.
    + eapply fresh_var_inv; eauto.
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
    + intros. inv_get.
      edestruct get_fst_renameApartF as [? [? ?]]; eauto; dcr; subst.
      destruct Zs as [Z s']; simpl in *; subst.
      eapply IH; eauto.
      intros. decide (x ∈ of_list (fst x0)).
      * edestruct update_with_list_lookup_in_list; try eapply i; dcr.
        Focus 2.
        rewrite H11.
        exploit fresh_list_stable_get; try eapply H10; eauto; dcr.
        subst. get_functional. eapply freshP; eauto.
        eauto with len.
      * rewrite lookup_set_update_not_in_Z; eauto.
        eapply ren.
        eapply incl_left.
        eapply incl_list_union; [| reflexivity|]; eauto.
        cset_tac.
    + intros.
      intros. inv_get.
      edestruct get_fst_renameApartF as [? [? ?]]; eauto; dcr; subst.
      destruct Zs as [Z s']; simpl in *; subst.
      hnf; intros.
      eapply fresh_list_stable_In in H0; dcr; subst.
      eapply freshP.
    + eapply IH; eauto.
      cset_tac.
Qed.
