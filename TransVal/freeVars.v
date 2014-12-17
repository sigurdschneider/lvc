Require Import List smt Exp Util CSet MapAgreement bitvec tvalTactics Val.
Require Import OptionMap MoreExp.

Fixpoint freeVars (s:smt) :=
match s with
| smtReturn e => Exp.freeVars e
| funcApp f x => list_union (List.map (Exp.freeVars) x)
| smtAnd a b => freeVars a ∪ freeVars b
| smtOr a b => freeVars a ∪ freeVars b
| smtNeg a => freeVars a
| ite c t f => freeVars t ∪ freeVars f ∪ Exp.freeVars c
| smtImp a b => freeVars a ∪ freeVars b
| smtFalse => {}
| smtTrue =>  {}
|constr e1 e2 => Exp.freeVars e1 ∪ Exp.freeVars e2
end.

Definition freeVarsList el :=
list_union (List.map freeVars el).

Lemma models_agree F E E' s:
  agree_on eq (freeVars s) E E'
  -> (models F E s <-> models F E' s).

Proof.
intros agree; general  induction s; simpl in *; try reflexivity.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs F E E'); try reflexivity; setSubst2 agree.
- assert (agree_on eq (Exp.freeVars e) E E') by setSubst2 agree.
  assert (exp_eval E e = exp_eval E' e)
  by( eapply exp_eval_agree; symmetry; eauto).
  case_eq (exp_eval E e); intros; unfold evalSexp.
  +  rewrite <- H0. rewrite H1. case_eq(val2bool v); intros.
     * rewrite (IHs1 F E E'); try reflexivity; setSubst2 agree.
     * rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
  + rewrite <- H0; rewrite H1; simpl.
    rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
-  assert (exp_eval E e = exp_eval E' e)
    by ( eapply exp_eval_agree; symmetry; eauto; setSubst2 agree).
  assert (exp_eval E e0 = exp_eval E' e0)
    by (eapply exp_eval_agree; symmetry; eauto; setSubst2 agree).
  unfold evalSexp; rewrite <- H; rewrite <- H0.
  unfold val2bool.
  case_eq (exp_eval E e); case_eq (exp_eval E e0); intros;
  rewrite bvEq_equiv_eq; reflexivity.
- unfold evalSpred. destruct p.  unfold evalList.
  assert (omap (exp_eval E) a = omap (exp_eval E')  a).
  + eapply omap_exp_eval_agree; symmetry; eauto.
  + rewrite <- H. destruct (omap (exp_eval E) a); reflexivity.
- unfold evalSexp.
  assert (exp_eval E e = exp_eval E' e)
    by (eapply  exp_eval_agree; symmetry; eauto; setSubst2 agree).
  rewrite <- H. case_eq (exp_eval E e); intros; reflexivity.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
