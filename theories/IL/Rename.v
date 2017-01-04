Require Import List.
Require Export Util Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events.
Require Import SetOperations IL AppExpFree.

Set Implicit Arguments.

Fixpoint rename (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtLet x e s => stmtLet (ϱ x) (rename_exp ϱ e) (rename ϱ s)
    | stmtIf e s t => stmtIf (rename_op ϱ e) (rename ϱ s) (rename ϱ t)
    | stmtApp l Y => stmtApp l (List.map (rename_op ϱ) Y)
    | stmtReturn e => stmtReturn (rename_op ϱ e)
    | stmtFun s t =>
      stmtFun (List.map (fun Zs => (lookup_list ϱ (fst Zs), (rename ϱ (snd Zs)))) s) (rename ϱ t)
  end.

(** Renaming respects function equivalence *)

Global Instance rename_morphism
  : Proper (@feq _ _ _eq ==> eq ==> eq) rename.
Proof.
  unfold Proper, respectful; intros; subst.
  sind y0; destruct y0; simpl; f_equal; eauto; try (now rewrite H; eauto);
    eauto using rename_op_ext, rename_exp_ext, map_ext_get_eq2; eauto.
  - eapply map_ext_get_eq2; intros. f_equal; eauto. rewrite H; eauto.
Qed.

Lemma rename_agree ϱ ϱ' s
: agree_on eq (occurVars s) ϱ ϱ'
  -> rename ϱ s = rename ϱ' s.
Proof with eauto 50 using rename_op_agree, rename_exp_agree, map_ext_get_eq2 with cset.
  intros.
  sind s; destruct s; simpl in *; f_equal...
  - eapply map_ext_get_eq2; intros. f_equal; eauto.
    + erewrite lookup_list_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- (get_list_union_map _ H0); eauto with cset.
    + eapply IH; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- (get_list_union_map _ H0); eauto with cset.
Qed.

Lemma rename_app_expfree ϱ s
  : app_expfree s
    -> app_expfree (rename ϱ s).
Proof.
  induction 1; simpl; econstructor; eauto; intros; inv_get; simpl in *; eauto.
  exploit H as IV; eauto. inv IV; simpl. eauto using isVar.
Qed.
