Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import CSet Val Var Env EnvTy Equiv.Sim IL Fresh Annotation MoreExp Coherence.

Require Import SetOperations Filter.

Set Implicit Arguments.
Unset Printing Records.

Inductive eqn :=
  | EqnEq (e e':exp)
  | EqnApx (e e':exp)
  | EqnBot.

Definition satisfies (E:onv val) (gamma:eqn) : Prop :=
match gamma with
| EqnEq e e' => option_R eq (exp_eval E e) (exp_eval E e')
| EqnApx e e' => fstNoneOrR eq (exp_eval E e) (exp_eval E e')
| EqnBot => False
end.

Inductive eqnLt : eqn -> eqn -> Prop :=
| EqnLtBotEq e e'
  : eqnLt EqnBot (EqnEq e e')
| EqnLtBotApx e e'
  : eqnLt EqnBot (EqnApx e e')
| EqnLtEqApx e1 e1' e2 e2'
  : eqnLt (EqnEq e1 e2) (EqnApx e1' e2')
| EqnLtEqEq1 e1 e1' e2 e2'
  : expLt e1 e1'
    -> eqnLt (EqnEq e1 e2) (EqnEq e1' e2')
| EqnLtEqEq2 e1 e2 e2'
  : expLt e2 e2'
    -> eqnLt (EqnEq e1 e2) (EqnEq e1 e2')
| EqnLtApxApx1 e1 e1' e2 e2'
  : expLt e1 e1'
    -> eqnLt (EqnApx e1 e2) (EqnApx e1' e2')
| EqnLtApxApx2 e1 e2 e2'
  : expLt e2 e2'
    -> eqnLt (EqnApx e1 e2) (EqnApx e1 e2').

Instance eqnLt_irr : Irreflexive eqnLt.
hnf; intros; unfold complement.
- induction x; inversion 1; subst; eauto;
  try now eapply expLt_irr; eauto.
Qed.

Instance eqnLt_trans : Transitive eqnLt.
hnf; intros.
inv H; inv H0; eauto using eqnLt, expLt_trans.
Qed.

Instance StrictOrder_eqnLt : OrderedType.StrictOrder eqnLt eq.
econstructor; intros; eauto using eqnLt_trans.
- intro. rewrite H0 in H. eapply eqnLt_irr; eauto.
Qed.

Local Notation "'Compare' x 'next' y" :=
  (match x with
    | Eq => y
    | z => z
  end) (at level 100).

Fixpoint eqn_cmp (e e':eqn) :=
  match e, e' with
    | EqnBot, EqnBot => Eq
    | EqnBot, _ => Lt
    | EqnEq _ _, EqnBot => Gt
    | EqnEq _ _, EqnApx _ _ => Lt
    | EqnEq e1 e2, EqnEq e1' e2' =>
      Compare _cmp e1 e1' next
      Compare _cmp e2 e2' next Eq
    | EqnApx e1 e2, EqnApx e1' e2' =>
      Compare _cmp e1 e1' next
      Compare _cmp e2 e2' next Eq
    | EqnApx _ _, _ => Gt
  end.

Instance OrderedType_eqn : OrderedType eqn :=
 { _eq := eq;
  _lt := eqnLt;
  _cmp := eqn_cmp}.
intros.
destruct x,y; simpl eqn_cmp; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e e0); unfold _cmp in *; simpl in *.
inv H; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e' e'0); unfold _cmp in *; simpl in *.
inv H1; try now (econstructor; eauto 20 using eqnLt).
pose proof (_compare_spec e e0); unfold _cmp in *; simpl in *.
inv H; try now (econstructor; eauto using eqnLt).
pose proof (_compare_spec e' e'0); unfold _cmp in *; simpl in *.
inv H1; try now (econstructor; eauto 20 using eqnLt).
Defined.

Definition eqns := set eqn.

Definition satisfiesAll (E:onv val) (Gamma:eqns) :=
  forall gamma, gamma ∈ Gamma -> satisfies E gamma.

Definition freeVars (gamma:eqn) :=
  match gamma with
    | EqnEq e e' => Exp.freeVars e ∪ Exp.freeVars e'
    | EqnApx e e' => Exp.freeVars e ∪ Exp.freeVars e'
    | EqnBot => ∅
  end.

Definition eqns_freeVars (Gamma:eqns) := fold union (map freeVars Gamma) ∅.

Definition entails Gamma Γ' := forall E, satisfiesAll E Gamma -> satisfiesAll E Γ'.

Definition not_entails Gamma gamma := exists E, satisfiesAll E Gamma /\ ~ satisfies E gamma.


Definition onvLe X (E E':onv X)
:= forall x v, E x = Some v -> E' x = Some v.

(*Definition models Gamma gamma := forall E, satisfiesAll E Gamma -> satisfies E gamma.*)

Lemma exp_eval_onvLe e E E' v
: onvLe E E'
  -> exp_eval E e = Some v
  -> exp_eval E' e = Some v.
Proof.
  intros. general induction e; simpl in * |- *; eauto.
  simpl in H0. rewrite H0. eapply H in H0. eauto.
  - monad_inv H0. rewrite EQ.
    erewrite IHe; eauto.
  - monad_inv H0. rewrite EQ, EQ1.
    erewrite IHe1, IHe2; eauto.
Qed.

Definition list_EqnApx Y Y' :=
  of_list (zip (fun e e' => EqnApx e e') Y Y').

Definition subst_eqn (ϱ : env exp) (gamma: eqn) :=
  match gamma with
    | EqnEq e e' => EqnEq (subst_exp ϱ e) (subst_exp ϱ e')
    | EqnApx e e' => EqnApx (subst_exp ϱ e) (subst_exp ϱ e')
    | EqnBot => EqnBot
  end.

Definition subst_eqns (ϱ : env exp) (G:eqns) : eqns :=
  map (subst_eqn ϱ) G.

Definition sid := fun x => Var x.

Definition unsatisfiable (Gamma:eqns) :=
  forall E, ~ satisfiesAll E Gamma.
