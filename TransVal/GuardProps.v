Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import smt nofun noGoto bitvec freeVars.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil.

Opaque zext.

(* TODO Move *)
Lemma exp_freeVars_list_agree (E: onv val) e el:
    (forall x, x ∈ list_union (Exp.freeVars e:: List.map Exp.freeVars el) -> exists v, E x = Some v)
    ->(forall x, x ∈ Exp.freeVars e -> (exists v, E x = Some v)) /\
      (forall x, x ∈ list_union (List.map Exp.freeVars el) -> exists v, E x = Some v).

Proof.
  intros. split;
  intros; specialize (H x); destruct H; eauto;
    unfold list_union; simpl;
    eapply list_union_start_swap;
    cset_tac; eauto.
Qed.


Lemma exp_freeVars_bin_agree (E:onv val) a b:
  (forall x, x ∈ (Exp.freeVars a ++ Exp.freeVars b) -> exists v, E x = Some v)
    ->(forall x, x ∈ Exp.freeVars a -> (exists v, E x = Some v)) /\
      (forall x, x ∈ Exp.freeVars b -> exists v, E x = Some v).

Proof.
  intros.
  split; intros; specialize (H x); destruct H; cset_tac; eauto.
Qed.

(** Lemma 5 in the thesis.
Proves that whenever an expression evaluates under
a partial environment, then it's guard must be satisfiable **)
 Lemma guard_true_if_eval:
forall F E e v,
 exp_eval E e = Some v
->  models F (to_total E) (undef e).

Proof.
intros. general induction e; simpl in *; eauto.
- monad_inv H.
  eapply IHe; eauto.
- monad_inv H.
  destruct if.
   + erewrite models_combine; simpl; erewrite models_combine; simpl.
     split; try split; eauto.
     intros.
     unfold val2bool in H.
     eapply bvEq_equiv_eq in H.
     unfold smt_eval in H.
     erewrite exp_eval_partial_total in H; eauto.
     simpl in H.
     rewrite H in EQ2; subst; simpl in EQ2; isabsurd.
   + erewrite models_combine; simpl; erewrite models_combine; simpl.
     split; try split; eauto.
Qed.

(** Lemma 5 in the thesis, lifted to lists **)
Lemma guardList_true_if_eval:
forall F E el vl,
omap (exp_eval E) el = Some vl
-> models F (to_total E) (undefLift el).

Proof.
intros. general induction el; simpl in *; eauto.
monad_inv H.
erewrite models_combine; simpl; split; eauto using guard_true_if_eval.
Qed.

(** Lemma 6 **)
Lemma guard_models_impl_eval:
forall F E e,
(forall x, x ∈ Exp.freeVars e -> exists v,  E x = Some v)
-> models F (to_total E) (undef e)
-> exists v, exp_eval E e = Some v.

Proof.
  intros. general induction e; simpl in *; eauto.
  - destruct (H v); cset_tac; eauto.
  - destruct (IHe F E); subst; destruct u; eauto; simpl; rewrite H1.
    + case_eq (val2bool x); intros.
      * exists val_true; simpl; unfold option_lift1; rewrite H2; simpl; eauto.
      * exists val_false; simpl; unfold option_lift1; rewrite H2; simpl; eauto.
    + exists (neg x). simpl; unfold option_lift1; eauto.
  - simpl in *.
    repeat (rewrite models_combine in H0; simpl in H0); intuition; cset_tac.
    edestruct (IHe1 F); eauto.
    edestruct (IHe2 F); eauto.
    rewrite H1, H4.
    destruct if in H2; simpl in *; unfold val2bool in H2.
   + erewrite bvEq_equiv_eq in H2.
     rewrite e. unfold binop_eval.
     unfold smt_eval in *; erewrite exp_eval_partial_total in H2; eauto.
     unfold bvDiv. destruct if; isabsurd.
     destruct (bvLessZero x); destruct (bvLessZero x0); eexists; eauto.
   + unfold binop_eval; unfold option_lift2; simpl; case_eq b; intros; [ eexists; eauto |].
     case_eq n0; intros; [ eexists; eauto | ].
     case_eq n1; intros; [ eexists; eauto | ].
     case_eq n2; intros; [ eexists; eauto | ].
     case_eq n3; intros; [ eexists; eauto | ].
     case_eq n4; intros; [ isabsurd | eexists; eauto].
Qed.

(*  Lemma 6**)
Lemma guardlist_impl_eval:
  forall F E el,
    (forall x, x ∈ list_union (List.map Exp.freeVars el) -> exists v,  E x = Some v)
    -> models F (to_total E) (undefLift el)
    -> exists v, omap (exp_eval E) el = Some v.

Proof.
  intros.
  general induction el; simpl in *; eauto.
  eapply models_combine in H0; simpl in H0.
  destruct H0.
  edestruct IHel; eauto.
  - eapply exp_freeVars_list_agree; eauto.
  - rewrite H2. edestruct guard_models_impl_eval; eauto.
    + eapply exp_freeVars_list_agree; eauto.
    + rewrite H3; eexists; simpl; eauto.
Qed.

(** Lemma 7 in thesis **)
Lemma guardTrue_if_Terminates_ret:
forall L L' E s E' e,
noFun s
-> Terminates (L, E, s)(L', E', stmtReturn e)
-> forall F, models F (to_total E') (undef e).

Proof.
  intros. general induction H0; eauto using guard_true_if_eval.
  specialize (IHTerminates L0 L'0 E' s' E'0 e).
  inversion H; subst; invt noFun; eauto using IHTerminates; eauto.
  isabsurd.
Qed.

Lemma guardTrue_if_Terminates_goto:
forall L L' E s E' f el,
noFun s
-> Terminates (L, E, s) (L', E' , stmtGoto f el)
-> forall F, models F (to_total E') (undefLift el).

Proof.
  intros. general induction H0; eauto using guardList_true_if_eval.
  specialize (IHTerminates L0 L'0  E' s' E'0 f el).
  inversion H; subst; invt noFun; eauto using IHTerminates; eauto.
  isabsurd.
Qed.

(** Lemma 9 in the Thesis **)
Lemma undef_models:
forall F E e,
(forall x, x ∈ Exp.freeVars e -> exists v, E x = Some v)
-> exp_eval E e = None
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
    + eapply exp_freeVars_bin_agree; eauto.
    + edestruct (guard_models_impl_eval F E e1); eauto.
      * eapply (exp_freeVars_bin_agree E e1 e2); eauto.
      *  unfold smt_eval.  rewrite H4, H5 in *; simpl in *.
         destruct if in H3; simpl in H3.
         { eapply H3. unfold val2bool; eapply bvEq_equiv_eq.
           subst; simpl in *.
           unfold smt_eval; erewrite exp_eval_partial_total; eauto.
           unfold bvDiv in H0; destruct if in H0; subst; eauto; isabsurd. }
         { destructBin b; subst; isabsurd. }
Qed.

Lemma undefList_models:
  forall F E el,
    (forall x, x ∈ list_union (List.map Exp.freeVars el) -> exists v, E x = Some v)
    -> omap (exp_eval E) el = None
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
      eapply exp_freeVars_list_agree; eauto.
    + eapply IHel; eauto.
      eapply exp_freeVars_list_agree; eauto.
Qed.
(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)