Require Import Var IL.

Inductive var_P (P:var -> Prop)
  : stmt -> Prop :=
| VarPOpr x b e
  :  var_P P b
     -> P x
     -> For_all P (Exp.freeVars e)
     -> var_P P (stmtLet x e b)
| VarPIf e b1 b2
  :  For_all P (Ops.freeVars e)
     -> var_P P b1
     -> var_P P b2
     -> var_P P (stmtIf e b1 b2)
| VarPGoto l Y
  : For_all P (list_union (Ops.freeVars ⊝ Y))
    -> var_P P (stmtApp l Y)
| VarPReturn e
  : For_all P (Ops.freeVars e)
    -> var_P P (stmtReturn e)
| VarPLet F b
  : (forall n Zs, get F n Zs -> var_P P (snd Zs))
    -> (forall n Zs, get F n Zs -> For_all P (of_list (fst Zs)))
    -> var_P P b
    -> var_P P (stmtFun F b).

Lemma var_P_occurVars (P:var -> Prop) s
  : var_P P s
    -> For_all P (occurVars s).
Proof.
  induction 1; unfold For_all in *; intros; simpl in *; cset_tac'.
  eapply list_union_get in H4. destruct H4; dcr; inv_get; cset_tac.
Qed.
