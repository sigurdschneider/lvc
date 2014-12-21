Require Import List EqNat Bool SetOperations.
Require Import IL Exp Val bitvec smt freeVars tvalTactics.

(** Helper function to merge SMT options **)
Definition combine (o1:option smt) (o2:option smt) :option smt :=
match o1, o2 with
| Some v1, Some v2 => Some (smtAnd v1 v2)
| Some v1, _ => o1
| _, _  => o2
end.

(** Function to generate the guard expression for one expression **)
Fixpoint undef e :=
match e with
|BinOp n a b
 => match n with
        | 0 =>  combine (undef a) (undef b)
        | 1 =>  combine (undef a) (undef b)
        | 2 =>  combine (undef a) (undef b)
        | 3 =>  combine (undef a) (undef b)
        | 4 =>  combine (undef a) (undef b)
        | _ => match combine (undef a) (undef b) with
                 | Some c => Some (smtAnd (smtNeg (constr b (Con (zext k (O::nil))))) c )
                 | None =>  Some (smtNeg (constr b (Con (zext k (O::nil)))))
               end
    end
|UnOp n a
 => undef a
|Con v
 => None
|Var v
 => None
end.

Fixpoint undefLift (el: list exp) :=
match el with
|nil => None
| e::el' => combine (undef e) (undefLift el')
end.

Definition guardGen s p cont :=
match s, p with
| Some v, source => smtAnd v cont
| Some v, target => smtImp v cont
| None, _ => cont
end.

Lemma combine_keep_undef:
forall e1 e2,
combine (undef e1) (undef e2) = None
-> undef e1 = None /\ undef e2 = None.

Proof.
intros.
case_eq (undef e1); case_eq (undef e2); intros;
rewrite H0 in H; rewrite H1 in H; try isabsurd; eauto.
Qed.

Lemma combine_keep_undef_list:
forall e el,
combine (undef e) (undefLift el) =  None
-> undef e = None /\ undefLift el = None.

Proof.
  intros.
  case_eq (undef e); case_eq (undefLift el); intros;
  rewrite H0 in H; rewrite H1 in H; try isabsurd; eauto.
Qed.

Lemma freeVars_undef :
forall a e s,
undef e = Some s
-> a ∈ freeVars s
-> a ∈ Exp.freeVars e.

Proof.
  intros. general induction e.
  - simpl in *. exploit IHe; eauto.
  - simpl in *.
    destruct b; try destruct b; try destruct b; try destruct b; try destruct b;
    try destruct b; simpl in *.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { left; exploit IHe1; eauto. }
        { right; exploit IHe2; eauto. }
      * cset_tac. left; exploit IHe1; eauto.
      * cset_tac. right; exploit IHe2; eauto.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { left; exploit IHe1; eauto. }
        { right; exploit IHe2; eauto. }
      * cset_tac. left; exploit IHe1; eauto.
      * cset_tac. right; exploit IHe2; eauto.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { left; exploit IHe1; eauto. }
        { right; exploit IHe2; eauto. }
      * cset_tac. left; exploit IHe1; eauto.
      * cset_tac. right; exploit IHe2; eauto.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { left; exploit IHe1; eauto. }
        { right; exploit IHe2; eauto. }
      * cset_tac. left; exploit IHe1; eauto.
      * cset_tac. right; exploit IHe2; eauto.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { left; exploit IHe1; eauto. }
        { right; exploit IHe2; eauto. }
      * cset_tac. left; exploit IHe1; eauto.
      * cset_tac. right; exploit IHe2; eauto.
    +case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        destruct H0; try isabsurd.
        { right; eauto. }
        { destruct H0.
          -  left; exploit IHe1; eauto.
          - right; exploit IHe2; eauto. }
      *  simpl in H0. cset_tac. destruct H0. destruct H0; try isabsurd.
         right; eauto.
         { left; exploit IHe1; eauto. }
      * simpl in H0. cset_tac. destruct H0. destruct H0; try isabsurd.
        { right; eauto. }
        { right; exploit IHe2; eauto. }
      * simpl in H0. cset_tac. destruct H0; try isabsurd.
        right; eauto.
    + case_eq (undef e1); case_eq (undef e2); intros;
      rewrite H1 in H; rewrite H2 in H; simpl in H;
      inversion H; rewrite <- H4 in *.
      * simpl in H0; cset_tac. destruct H0.
        { destruct H0; isabsurd. right; eauto. }
        {  destruct H0.
           - left; exploit IHe1; eauto.
           - right; exploit IHe2; eauto.  }
      * simpl in H0. clear H4. cset_tac. destruct H0.
        { destruct H0; eauto; isabsurd. }
        { left; exploit IHe1; eauto. }
      * simpl in H0. clear H4. cset_tac. destruct H0.
        { destruct H0; eauto; isabsurd. }
        { right; exploit IHe2; eauto. }
      * simpl in *.  cset_tac; destruct H0; eauto; isabsurd.
Qed.

Lemma freeVars_undefLift:
forall a el ul,
undefLift el = Some ul
-> a ∈  freeVars ul
-> a ∈ list_union (List.map Exp.freeVars el).

Proof.
  intros a el ul udef inclFV.
  general induction el.
  - unfold list_union. simpl in *.
    eapply list_union_start_swap.
    case_eq (undef a); case_eq (undefLift el); intros;
    rewrite H, H0 in udef; inversion udef;
    rwsimplB H2 inclFV; cset_tac; eauto.
    +destruct inclFV; eauto.
       left; right; eapply (freeVars_undef) in H1; eauto.
    + left; right; eapply (freeVars_undef) in inclFV; eauto.
Qed.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)