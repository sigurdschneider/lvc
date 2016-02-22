Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events.
Require Import SetOperations IL.

Set Implicit Arguments.

Fixpoint rename (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtLet x e s => stmtLet (ϱ x) (rename_exp ϱ e) (rename ϱ s)
    | stmtIf e s t => stmtIf (rename_exp ϱ e) (rename ϱ s) (rename ϱ t)
    | stmtApp l Y => stmtApp l (List.map (rename_exp ϱ) Y)
    | stmtReturn e => stmtReturn (rename_exp ϱ e)
    | stmtExtern x f e s => stmtExtern (ϱ x) f (List.map (rename_exp ϱ) e) (rename ϱ s)
    | stmtFun s t =>
      stmtFun (List.map (fun Zs => (lookup_list ϱ (fst Zs), (rename ϱ (snd Zs)))) s) (rename ϱ t)
  end.

(** Renaming respects function equivalence *)

Global Instance rename_morphism
  : Proper (@feq _ _ _eq ==> eq ==> eq) rename.
Proof.
  unfold Proper, respectful; intros; subst.
  sind y0; destruct y0; simpl; f_equal; eauto; try (now rewrite H; eauto);
  eauto using rename_exp_ext, map_ext_get_eq2; eauto.
  eapply map_ext_get_eq2; intros. f_equal; eauto. rewrite H; eauto.
Qed.

Lemma rename_agree ϱ ϱ' s
: agree_on eq (occurVars s) ϱ ϱ'
  -> rename ϱ s = rename ϱ' s.
Proof with eauto 50 using rename_exp_agree, map_ext_get_eq2 with cset.
  intros.
  sind s; destruct s; simpl in *; f_equal...
  eapply map_ext_get_eq2; intros. f_equal; eauto.
  - erewrite lookup_list_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- get_list_union_map; eauto with cset. eauto with cset.
  - eapply IH; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- get_list_union_map; eauto with cset. eauto with cset.
Qed.
