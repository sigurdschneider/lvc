Require Import List Arith.
Require Import IL Annotation AutoIndTac Exp Fresh Util.
Require Import SetOperations Sim Var.
Require Import SMT NoFun.
Require Import Guards ILFtoSMT.

(** Lemma 7 in the thesis.
Proves that whenever an expression evaluates under
a partial environment, then it's guard must be satisfiable **)

Unset Printing Records.

Lemma guard_true_if_eval:
forall F E e v,
 op_eval E e = Some v
->  models F (to_total E) (undef e).

Proof.
intros. general induction e; simpl in *; eauto.
- monad_inv H.
  eapply IHe; eauto.
- monad_inv H; cases.
   + repeat( erewrite models_combine; simpl).
     split; try split; intros; eauto.
     unfold smt_eval in H; simpl in H.
     erewrite !op_eval_partial_total in H; simpl; eauto.
     eapply (binop_eval_div_zero x) in H; eauto.
   + erewrite models_combine; simpl; erewrite models_combine; simpl.
     split; try split; eauto.
Qed.

(** Lemma7 in the thesis, lifted to lists **)
Lemma guardList_true_if_eval:
  forall F E el vl,
    omap (op_eval E) el = Some vl
    -> models F (to_total E) (undefLift el).

Proof.
  intros. general induction el; simpl in *; eauto.
  monad_inv H.
  erewrite models_combine; simpl; split; eauto using guard_true_if_eval.
Qed.

(** Lemma 8 **)
Lemma guard_models_impl_eval:
forall F E e,
(forall x, x ∈ Op.freeVars e -> exists v,  E x = Some v)
-> models F (to_total E) (undef e)
-> exists v, op_eval E e = Some v.

Proof.
  intros. general induction e; simpl in *; eauto.
  - destruct (IHe F E); subst; eauto; rewrite H1; simpl.
    eapply unop_eval_total.
  - simpl in *.
    repeat (rewrite models_combine in H0; simpl in H0); intuition; cset_tac.
    edestruct (IHe1 F); eauto.
    edestruct (IHe2 F); eauto.
    rewrite H1, H4; simpl.
    cases in H2; simpl in H2.
    + decide (x0 = val_zero).
      * exfalso. eapply H2. unfold smt_eval; simpl.
        erewrite op_eval_partial_total; eauto.
      * eapply binop_eval_div_nonzero; eauto.
   + eapply binop_eval_not_div; eauto.
Qed.

(*  Lemma 8 lifted to lists**)
Lemma guardlist_impl_eval:
  forall F E el,
    (forall x, x ∈ list_union (List.map Op.freeVars el) -> exists v,  E x = Some v)
    -> models F (to_total E) (undefLift el)
    -> exists v, omap (op_eval E) el = Some v.
Proof.
  intros.
  general induction el; simpl in *; eauto.
  eapply models_combine in H0; simpl in H0; dcr.
  edestruct IHel; eauto.
  - eapply op_freeVars_list_agree; eauto.
  - rewrite H0. edestruct guard_models_impl_eval; eauto.
    + eapply op_freeVars_list_agree; eauto.
    + rewrite H3; eexists; simpl; eauto.
Qed.

(** Lemma 9 in thesis **)
Lemma guardTrue_if_Terminates_ret:
  forall L L' E s E' e,
    noFun s
    -> Terminates (L, E, s)(L', E', stmtReturn e)
    -> forall F, models F (to_total E') (undef e).

Proof.
  intros L L' E s E' e noFun_s Terminates_s_ret F.
  general induction Terminates_s_ret; eauto using guard_true_if_eval.
  specialize (IHTerminates_s_ret L0 L'0 E' s' E'0 e).
  inversion H; subst; invt noFun; eauto using IHTerminates_s_ret; eauto.
Qed.

(** Lemma 10 **)
Lemma guardTrue_if_Terminates_goto:
forall L L' E s E' f el,
noFun s
-> Terminates (L, E, s) (L', E' , stmtApp f el)
-> forall F, models F (to_total E') (undefLift el).

Proof.
  intros. general induction H0; eauto using guardList_true_if_eval.
  specialize (IHTerminates L0 L'0  E' s' E'0 f el).
  inversion H; subst; invt noFun; eauto using IHTerminates; eauto.
Qed.

(** Lemma 11 in the Thesis **)
Lemma undef_models:
forall F E e,
(forall x, x ∈ Op.freeVars e -> exists v, E x = Some v)
-> op_eval E e = None
-> ~ models F (to_total E) (undef e).

Proof.
  intros;  hnf;  intros.
  general induction e; simpl in *; try isabsurd.
  - specialize (H v); destruct H; cset_tac; eauto; isabsurd.
  - monad_inv H0.
    + eapply IHe; eauto.
    + destruct u; isabsurd.
  - repeat (rewrite models_combine in H1; simpl in H1).
    destruct H1 as [[H1 H2] H3].
    edestruct guard_models_impl_eval; eauto.
    + eapply op_freeVars_bin_agree; eauto.
    + edestruct (guard_models_impl_eval F E e1); eauto.
      * eapply (op_freeVars_bin_agree E e1 e2); eauto.
      * rewrite H4, H5 in *; simpl in *.
        cases in H3; simpl in H3.
        eapply H3.
        unfold smt_eval; erewrite op_eval_partial_total; simpl; eauto.
        eapply binop_eval_div_zero in H0; subst; eauto.
        edestruct binop_eval_not_div in H0; eauto.
        rewrite H6 in H0; congruence.
Qed.

Lemma undefList_models:
  forall F E el,
    (forall x, x ∈ list_union (List.map Op.freeVars el) -> exists v, E x = Some v)
    -> omap (op_eval E) el = None
    -> ~ models F (to_total E) (undefLift el).

Proof.
  intros.
  general induction el; simpl in *.
  - hnf; intros.
    repeat(rewrite models_combine in H1; simpl in H1).
    destruct H1.
    pose proof (undef_models F E a).
    monad_inv H0; try isabsurd.
    + eapply H3; eauto.
      eapply op_freeVars_list_agree; eauto.
    + eapply IHel; eauto.
      eapply op_freeVars_list_agree; eauto.
Qed.

Lemma undef_vars_subset:
  forall e,
    freeVars (undef e) ⊆ Op.freeVars e.
Proof.
  intros e.
  cset_tac.
  induction e; simpl in *; try isabsurd; eauto.
  - rewrite models_combine_vars in H; simpl in H.
    rewrite models_combine_vars in H; simpl in H.
    cset_tac.
    cases in H0; simpl in *; cset_tac.
Qed.
