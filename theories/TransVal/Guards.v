Require Import List EqNat Bool SetOperations.
Require Import IL Exp Val SMT.

(** Helper function to merge SMT options **)
Definition combine (o1:smt) (o2: smt) :smt :=
   if [o1 = smtTrue] then o2 else
    if [o2 = smtTrue] then o1 else smtAnd o1 o2.

Lemma models_combine F E a b
: models F E (combine a b) <-> models F E (smtAnd a b).

Proof.
  unfold combine. repeat (cases; subst); simpl; intuition.
Qed.

Lemma models_combine_vars a b:
  freeVars (combine a b) [=] freeVars (smtAnd a b).

Proof.
  unfold combine. repeat(cases; subst); simpl; cset_tac.
Qed.

(** Function to generate the guard expression for one expression **)
Fixpoint undef e :=
  match e with
  | BinOp op a b
    => combine (combine (undef a) (undef b))
              (if [op = BinOpDiv]
               then smtNeg (constr b (Con val_zero))
               else smtTrue)
  | UnOp n a => undef a
  | Con v => smtTrue
  | Var v => smtTrue
  end.

Fixpoint undefLift (el: list op) :=
  match el with
  | nil => smtTrue
  | e::el' => combine (undef e) (undefLift el')
  end.

Definition guardGen s p cont :=
  if [s = smtTrue] then cont else
    match p with
    | source => smtAnd s cont
    | target => smtImp s cont
    end.

Lemma freeVars_guardGen s p t
  : freeVars (guardGen s p t) ⊆ freeVars s ∪ freeVars t.
Proof.
  unfold guardGen; repeat cases; eauto with cset.
Qed.

Lemma models_guardGen_source F E s cont
: models F E (guardGen s source cont) <-> models F E (smtAnd s cont).

Proof.
 unfold guardGen; cases; subst; simpl; intuition.
Qed.

Lemma models_guardGen_target F E s cont
: models F E (guardGen s target cont) <-> models F E (smtImp s cont).
Proof.
 unfold guardGen; cases; subst; simpl; intuition.
Qed.

Lemma freeVars_undef e
  : freeVars (undef e) ⊆ Ops.freeVars e.
Proof.
  intros. general induction e; simpl in * |- *; eauto with cset.
  - unfold combine in *. repeat cases ; eauto with cset.
Qed.

Lemma freeVars_undefLift el
  : freeVars (undefLift el) ⊆ list_union (List.map Ops.freeVars el).
Proof.
  general induction el; simpl in * |- *; eauto.
  - rewrite list_union_start_swap.
    unfold combine; repeat cases; simpl;
      try rewrite IHel; try rewrite freeVars_undef; eauto with cset.
Qed.