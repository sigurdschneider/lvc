Require Import List EqNat Bool.
Require Import IL MoreExp SetOperations Val DecSolve.

Set Implicit Arguments.

(** Arguments are lists of expressions **)
Definition arglst := list exp.

(** Lists of values **)
Definition vallst := list val. (*bitvec.*)

(**
evalSexp evaluates an SMT expression given an environment that must be total on
every variable that may occur in a formula.
**)

(* "Lower" an environment back to returning option types **)
Definition to_partial (E:env val) x : option val := Some (E x).

(* Make an environment total *)
Definition to_total (E:onv val) x : val :=
  match E x with
    |Some v => v
    |None => default_val
  end.

Lemma agree_on_partial lv E E'
: agree_on eq lv E E'
  -> agree_on eq lv (to_partial E) (to_partial E').
Proof.
  intros; unfold to_partial; hnf; intros; simpl.
  rewrite H; eauto.
Qed.

Lemma agree_on_total lv E E'
: agree_on eq lv E E'
  -> agree_on eq lv (to_total E) (to_total E').
Proof.
  intros; unfold to_total; hnf; intros; simpl.
  rewrite H; eauto.
Qed.

Lemma to_partial_to_total (E:onv val) x v
  : E x = Some v -> to_partial (to_total E) x = Some v.
Proof.
  intros.
  unfold to_partial, to_total. cases; eauto.
  inv H.
Qed.

(** Define what uninterpreted function symbols are **)
Definition pred := lab (*arglst -> bool*).

(** First define what an smt statement is **)
Inductive smt :Type :=
(** Conjunction **)
| smtAnd: smt -> smt -> smt
(** Disjunction **)
| smtOr: smt -> smt -> smt
(** Negation **)
| smtNeg: smt -> smt
(** Conditional **)
| ite: exp -> smt -> smt -> smt
(** Implication **)
| smtImp: smt -> smt -> smt
(** Constraint *)
| constr: exp -> exp -> smt
(** Predicate evaluation **)
| funcApp: pred -> arglst -> smt
(** Constant false **)
| smtFalse: smt
(** Constant true **)
| smtTrue:smt.

Instance smt_eq_dec (s t:smt) : Computable (s = t).
Proof.
  general induction s; destruct t; try dec_solve;
  try (decide (s1 = t1); decide (s2 = t2); subst; eauto; try dec_solve);
  try (decide (s = t); subst; eauto; try dec_solve).
  - decide (e = e0); subst; dec_solve.
  - decide (e = e1); decide (e0 = e2); subst; dec_solve.
  - decide (p = p0); decide (a = a0); subst; dec_solve.
Qed.


(** Now define the parameters for the translation function **)
Inductive pol:Type :=
| source :pol
| target :pol.

Fixpoint listGen (el:arglst) :=
match el with
|nil => nil
|_:: el' => default_val :: listGen el'
end.

Parameter undef_substitute : val.

Definition smt_eval (E:env val) (e:exp) :=
  match exp_eval (to_partial E) e with
    | Some v => v
    | None => undef_substitute
  end.

(** models relation for smt. No need for options here too, because if models can be evaluated by an environment,
every variable must have been defined. **)
Fixpoint models (F:pred ->vallst->bool) (E:env val) (s:smt) : Prop:=
match s with
  |smtAnd a b
   => (models F E a) /\ (models F E b)
  |smtOr a b
   => (models F E a) \/  (models F E b)
  |smtNeg a
   =>  (models F E a) -> False
| ite c t f
  =>  if val2bool (smt_eval E c)
            then models F E t
            else models F E f
|smtImp a b
 => (models F E a) ->(models F E b)
|constr s1 s2 => (smt_eval E s1) = (smt_eval E s2)
|funcApp f a => F f (List.map (smt_eval E) a)
|smtFalse => False
|smtTrue => True
end.

Lemma smtand_comm:
forall a b F E,
models F E (smtAnd a b)
-> models F E (smtAnd b a).

Proof.
intros.
hnf in H. simpl. destruct H as [A B]. eauto.
Qed.

Lemma smtand_neg_comm:
forall a b F E,
~ models F E (smtAnd a b)
-> ~ models F E (smtAnd b a).

Proof.
intros.
hnf. intros. eapply smtand_comm in H0. eapply H. assumption.
Qed.

Lemma extend_not_models:
forall s Q,
(forall F E, ~ models F E s)
-> (forall F E, models F E Q -> ~ models F E s).

Proof.
intros.
specialize (H F E). assumption.
Qed.

(*
Instance bind_equiv (A B : Type) `{Equivalence A} `{Equivalence B}
         (f:A -> option B) `{Proper _ (Equivalence.equiv ==> Equivalence.equiv) f}
  : Proper (Equivalence.equiv ==> Equivalence.equiv) (@bind A B f).
Proof.
  unfold Proper, respectful; intros; subst.
  inv H2; simpl; eauto.
Qed.

Lemma eq_equiv X (x y:X) `{Equivalence X}
  : x = y -> x === y.
Proof.
  intros; subst; eauto.
Qed.
Hint Immediate eq_equiv.
 *)



Lemma exp_eval_partial_total E e v
 : exp_eval E e = Some v ->
   exp_eval (to_partial (to_total E)) e = Some v.
Proof.
  intros.
  general induction e; simpl in * |- *; eauto.
  - erewrite to_partial_to_total; eauto.
  - monad_inv H; simpl; eauto.
    erewrite IHe, EQ; eauto.
  - intros.
    monad_inv H; simpl.
    erewrite IHe1, IHe2; eauto; simpl.
    rewrite EQ, EQ1; eauto.
Qed.

(** Next 2 Lemmata belong to Lemma 4 in subsection 3.4 in the thesis
They prove that evaluation without a total environment is equal
to evaluation under a total environment **)
Lemma exp_eval_partial_total_list E el vl
:  omap (exp_eval E) el = Some vl
-> omap (exp_eval (to_partial (to_total  E))) el = Some vl.

Proof.
  intros. general induction el; eauto using exp_eval_partial_total.
  - simpl in H. monad_inv H. simpl.
    erewrite exp_eval_partial_total; eauto; simpl.
    erewrite IHel; eauto; simpl.
    rewrite EQ, EQ1; eauto.
Qed.

Lemma list_eval_agree E el v:
  omap(exp_eval E) el = Some v
  -> List.map (smt_eval (to_total E) ) el = v.

Proof.
  intros. general induction el.
  - eauto.
  - simpl in *.
    monad_inv H.
    eapply exp_eval_partial_total in EQ.
    unfold smt_eval at 1.
    rewrite EQ.
    f_equal.
    erewrite (IHel E x0); eauto.
Qed.

Lemma list_length_agree E el v:
  omap (exp_eval E) el = v
  ->(exists vl, List.map (smt_eval (to_total E)) el = vl
               /\ List.length el = List.length vl).

Proof.
  intros.
  general induction el.
  - simpl.
    exists nil; split; eauto.
  - simpl in *.
    specialize (IHel E (omap (exp_eval E) el)).
    destruct IHel; eauto.
    destruct H.
    exists ( (smt_eval (to_total E) a):: x).
    simpl. rewrite H. split; eauto.
Qed.

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

Lemma models_agree F E E' s:
  agree_on eq (freeVars s) E E'
  -> (models F E s <-> models F E' s).

Proof.
intros agree; general  induction s; simpl in *; try reflexivity.
- rewrite (IHs1 F E E'), (IHs2 F E E'); eauto with cset. reflexivity.
- rewrite (IHs1 F E E'), (IHs2 F E E'); eauto with cset. reflexivity.
- rewrite (IHs F E E'); eauto with cset. reflexivity.
- assert (agree_on eq (Exp.freeVars e) E E') by eauto with cset.
  assert (exp_eval (to_partial E) e = exp_eval (to_partial E') e). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial; eauto.
  }
 unfold smt_eval in *.
  case_eq (exp_eval (to_partial E) e); intros.
  +  rewrite <- H0. rewrite H1. case_eq(val2bool v); intros.
     * rewrite (IHs1 F E E'); eauto with cset.
     * rewrite (IHs2 F E E'); eauto with cset.
  + rewrite <- H0; rewrite H1. case_eq (val2bool undef_substitute); intros.
    * rewrite (IHs1 F E E'); eauto with cset.
    * rewrite (IHs2 F E E'); eauto with cset.
- rewrite (IHs1 F E E'), (IHs2 F E E'); eauto with cset. reflexivity.
- assert (exp_eval (to_partial E) e = exp_eval (to_partial E') e). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial. eapply agree_on_incl; eauto.  }
  assert (exp_eval (to_partial E) e0 = exp_eval (to_partial E') e0). {
    eapply exp_eval_agree; symmetry; eauto.
    eapply agree_on_partial. eapply agree_on_incl; eauto.  }
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
      cset_tac; simpl.
      eapply list_union_start_swap.
      cset_tac; eauto. }
      { rewrite H. f_equal. eapply IHa; eauto.
        eapply (agree_on_incl (bv:=list_union (List.map Exp.freeVars a0))
               (lv:=list_union (List.map Exp.freeVars (a::a0)))); eauto.
        cset_tac; simpl.
        eapply list_union_start_swap.
        eapply union_right; eauto. }
  + rewrite H.  split; eauto.
Qed.

Lemma exp_freeVars_list_agree (E: onv val) e el:
    (forall x, x ∈ list_union (Exp.freeVars e:: List.map Exp.freeVars el) -> exists v, E x = Some v)
    ->(forall x, x ∈ Exp.freeVars e -> (exists v, E x = Some v)) /\
      (forall x, x ∈ list_union (List.map Exp.freeVars el) -> exists v, E x = Some v).

Proof.
  intros. split;
  intros; specialize (H x); destruct H; eauto;
    simpl;
    eapply list_union_start_swap;
    cset_tac; eauto.
Qed.

Lemma exp_freeVars_bin_agree (E:onv val) a b:
  (forall x, x ∈ (union (Exp.freeVars a) (Exp.freeVars b)) -> exists v, E x = Some v)
    ->(forall x, x ∈ Exp.freeVars a -> (exists v, E x = Some v)) /\
      (forall x, x ∈ Exp.freeVars b -> exists v, E x = Some v).

Proof.
  intros.
  split; intros; specialize (H x); destruct H; cset_tac; eauto.
Qed.