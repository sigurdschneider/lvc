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
    | stmtFun Z s t => stmtFun (lookup_list ϱ Z) (rename ϱ s) (rename ϱ t)
  end.

(** Renaming respects function equivalence *)

Global Instance rename_morphism
  : Proper (@feq _ _ _eq ==> eq ==> eq) rename.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; f_equal; eauto; try (now rewrite H; eauto);
  eauto using rename_exp_ext, map_ext_get_eq; eauto.
Qed.

Lemma rename_agree ϱ ϱ' s
: agree_on eq (occurVars s) ϱ ϱ'
  -> rename ϱ s = rename ϱ' s.
Proof with eauto 50 using rename_exp_agree, map_ext_get_eq with cset.
  intros. general induction s; simpl in *; f_equal...
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
