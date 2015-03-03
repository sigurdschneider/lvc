Require Import List smt Exp Util CSet MapAgreement bitvec tvalTactics Val.
Require Import OptionMap MoreExp SetOperations.

Fixpoint freeVars (s:smt) :=
match s with
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
  assert (exp_eval (to_partial E) e = exp_eval (to_partial E') e). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial; eauto.
  }
 unfold smt_eval in *.
  case_eq (exp_eval (to_partial E) e); intros.
  +  rewrite <- H0. rewrite H1. case_eq(val2bool v); intros.
     * rewrite (IHs1 F E E'); try reflexivity; setSubst2 agree.
     * rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
  + rewrite <- H0; rewrite H1. case_eq (val2bool undef_substitute); intros.
    * rewrite (IHs1 F E E'); try reflexivity. setSubst2 agree.
    * rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
- assert (exp_eval (to_partial E) e = exp_eval (to_partial E') e). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial. eapply agree_on_incl; eauto. cset_tac; intuition.
  }
  assert (exp_eval (to_partial E) e0 = exp_eval (to_partial E') e0). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial. eapply agree_on_incl; eauto. cset_tac; intuition.
  }
  unfold smt_eval in *.
  rewrite <- H; rewrite <- H0.
  unfold val2bool.
  case_eq (exp_eval (to_partial E) e); case_eq (exp_eval (to_partial E) e0); intros;
  try rewrite bvEq_equiv_eq; reflexivity.
- destruct p.
  assert (List.map (smt_eval E) a =List.map (smt_eval E') a).
  + general induction a.
    * eauto.
    * simpl.
      assert (smt_eval E a = smt_eval E' a).
      { unfold smt_eval.
      pose proof (exp_eval_agree (E:=to_partial E) (E':=to_partial E') a (v:=exp_eval (to_partial E) a)).
      rewrite H; eauto.
      eapply agree_on_partial.
      simpl in agree.
      eapply (agree_on_incl (bv:=Exp.freeVars a)(lv:=list_union (Exp.freeVars a:: List.map Exp.freeVars a0))); eauto.
      cset_tac; unfold list_union; simpl;
      eapply list_union_start_swap.
      cset_tac; eauto. }
      { rewrite H. f_equal. eapply IHa; eauto.
        eapply (agree_on_incl (bv:=list_union (List.map Exp.freeVars a0))
               (lv:=list_union (List.map Exp.freeVars (a::a0)))); eauto.
        unfold list_union. cset_tac; simpl.
        eapply list_union_start_swap.
        unfold list_union.
        eapply union_right; eauto. }
  + rewrite H.  split; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
