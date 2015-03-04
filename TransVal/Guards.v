Require Import List EqNat Bool SetOperations.
Require Import IL Exp Val bitvec smt freeVars tvalTactics.

Opaque zext.

(** Helper function to merge SMT options **)
Definition combine (o1:smt) (o2: smt) :smt :=
   if [o1 = smtTrue] then o2 else
    if [o2 = smtTrue] then o1 else smtAnd o1 o2.

Lemma models_combine F E a b
: models F E (combine a b) <-> models F E (smtAnd a b).

Proof.
  unfold combine. repeat (destruct if; subst); simpl; intuition.
Qed.

(** Function to generate the guard expression for one expression **)
Fixpoint undef e :=
match e with
|BinOp n a b
 => combine (combine (undef a) (undef b))
           (if [n = 5]
            then smtNeg (constr b (Con (zext k (O::nil))))
            else smtTrue)
|UnOp n a => undef a
|Con v => smtTrue
|Var v => smtTrue
end.

Fixpoint undefLift (el: list exp) :=
match el with
|nil => smtTrue
| e::el' => combine (undef e) (undefLift el')
end.

Definition guardGen s p cont :=
  if [s = smtTrue] then cont else
  match p with
    | source => smtAnd s cont
    | target => smtImp s cont
  end.

Lemma models_guardGen_source F E s cont
: models F E (guardGen s source cont) <-> models F E (smtAnd s cont).

Proof.
 unfold guardGen; destruct if; subst; simpl; intuition.
Qed.

Lemma models_guardGen_target F E s cont
: models F E (guardGen s target cont) <-> models F E (smtImp s cont).
Proof.
 unfold guardGen; destruct if; subst; simpl; intuition.
Qed.

Lemma freeVars_undef :
forall a e,
a ∈ freeVars (undef e)
-> a ∈ Exp.freeVars e.

Proof.
  intros. general induction e; simpl in * |- *; cset_tac; intuition.
  - repeat (destruct if in H; unfold combine in *; simpl in *; cset_tac); eauto; intuition.
Qed.

Lemma freeVars_undefLift:
forall a el,
  a ∈ freeVars (undefLift el)
-> a ∈ list_union (List.map Exp.freeVars el).

Proof.
  intros a el inclFV.
  general induction el; simpl in * |- *; eauto.
  - unfold list_union. simpl in *.
    eapply list_union_start_swap.
    unfold combine in *.
    repeat (destruct if in inclFV); simpl in *; cset_tac; intuition (eauto using freeVars_undef).
Qed.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)