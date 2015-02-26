Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import bitvec sexp smt nofun noGoto freeVars.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil GuardProps ComputeProps.

(** Definitons **)
Definition combineEnv D (E1:onv val) E2 :=
fun x => if [x ∈ D] then E1 x else E2 x.

(** Lemmata **)

Lemma combineenv_agree D E E':
  agree_on eq D (combineEnv D E E') E.

Proof.
  hnf; intros. unfold combineEnv. destruct if; eauto; isabsurd.
Qed.

Lemma exp_combineenv_eql:
forall e D Es Et v,
Exp.freeVars e ⊆ D
-> (exp_eval (combineEnv D Es Et) e= v <-> exp_eval Es e = v).

Proof.
  intros. split; intros.
  - eapply (exp_eval_agree (E:=(combineEnv D Es Et))); eauto.
    eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= D));
      cset_tac; eauto.
    eapply combineenv_agree.
  - eapply (exp_eval_agree (E:=Es)); eauto.
    eapply (agree_on_incl (bv:=Exp.freeVars e) (lv:=D)); eauto.
    symmetry. eapply combineenv_agree.
Qed.

  Lemma explist_combineenv_eql:
forall el D Es Et rl,
list_union (List.map Exp.freeVars el) ⊆ D
-> ( omap (exp_eval (combineEnv D Es Et)) el = rl <-> omap (exp_eval Es) el = rl).

Proof.
  intros; split; intros.
  - general induction el; eauto.
    + simpl. simpl in H. hnf in H.
      pose proof (exp_combineenv_eql a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
      destruct H0; hnf; intros; try setSubstUnion H.
      * rewrite H0; eauto. erewrite IHel ; eauto.
        hnf; intros. setSubstUnion H.
  - general induction el; eauto.
    + simpl; simpl in H; hnf in H.
      pose proof (exp_combineenv_eql a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
      destruct H0; hnf; intros; try setSubstUnion H.
      * rewrite H0; eauto. erewrite IHel; eauto.
        hnf; intros; setSubstUnion H.
Qed.

Lemma combineenv_eql:
forall F s D Es Et,
 freeVars s ⊆  D
->(  models F (to_total Es) s  <-> models F (to_total (combineEnv D Es Et)) s).

Proof.
  intros. eapply models_agree. eapply (agree_on_incl (lv:=D)); eauto; symmetry.
  eapply agree_on_total.
  eapply combineenv_agree.
Qed.

Lemma exp_combineenv_eqr:
forall e D Es Et v,
agree_on eq (Exp.freeVars e ∩ D) Es Et
-> (exp_eval (combineEnv D Es Et) e= v <-> exp_eval Et e = v).

Proof.
 intros; split; intros.
 - eapply (exp_eval_agree (E:=(combineEnv D Es Et))); eauto.
   hnf. cset_tac. unfold combineEnv. destruct if; eauto.
   eapply H. cset_tac; intuition.
 - eapply (exp_eval_agree (E:= Et)); eauto.
   hnf; cset_tac. unfold combineEnv; destruct if; eauto.
   symmetry. eapply H; cset_tac; intuition.
Qed.

Lemma exp_combineenv_eqr':
forall e D Es Et v,
agree_on eq (Exp.freeVars e ∩ D) Es Et
-> (exp_eval (to_partial (to_total (combineEnv D Es Et))) e
   = v <-> exp_eval (to_partial (to_total Et)) e = v).

Proof.
 intros; split; intros.
 - eapply (exp_eval_agree (E:=(to_partial (to_total (combineEnv D Es Et))))); eauto.
   hnf. cset_tac. unfold combineEnv, to_partial, to_total. destruct if; eauto.
   rewrite H. reflexivity. cset_tac; intuition.
 - eapply (exp_eval_agree (E:= to_partial (to_total Et))); eauto.
   hnf; cset_tac. unfold combineEnv, to_partial, to_total; destruct if; eauto.
   rewrite H. reflexivity.
   cset_tac; intuition.
Qed.

Lemma explist_combineenv_eqr:
forall el D Es Et vl,
agree_on eq (list_union (List.map Exp.freeVars el) ∩ D) Es Et
-> (omap (exp_eval (combineEnv D Es Et)) el = vl <-> omap (exp_eval Et) el = vl).

Proof.
  intros; split; intros.
  - general induction el.
    + reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr a D Es Et (exp_eval (combineEnv D Es Et) a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H. split; eauto.
        unfold list_union; simpl. eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H0; eauto. f_equal.
        rewrite (IHel D Es Et (omap (exp_eval (combineEnv D Es Et)) el)); eauto.
        hnf. intros. cset_tac. eapply H. split; eauto.
        unfold list_union. simpl. eapply list_union_start_swap. cset_tac; eauto.
  - general induction el.
    + reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr a D Es Et (exp_eval Et a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H. split; eauto.
        unfold list_union; simpl. eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H1; eauto. f_equal.
        symmetry. rewrite (IHel D Es Et (omap (exp_eval  Et) el)); eauto.
        hnf. intros. cset_tac. eapply H. split; eauto.
        unfold list_union. simpl. eapply list_union_start_swap. cset_tac; eauto.
Qed.

Lemma explist_combineenv_eqr':
forall el D Es Et vl,
  agree_on eq (list_union (List.map Exp.freeVars el) ∩ D) Es Et
  -> (omap (exp_eval (to_partial (to_total (combineEnv D Es Et)))) el = vl
                     <-> omap (exp_eval (to_partial (to_total Et))) el = vl).

Proof.
  intros; split; intros.
  - general induction el.
    +  reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr' a D Es Et (exp_eval (to_partial (to_total (combineEnv D Es Et))) a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H; split; eauto.
        unfold list_union; simpl; eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H0; eauto. f_equal.
        symmetry. simpl.
        rewrite (IHel D Es Et (omap (exp_eval (to_partial (to_total (combineEnv D Es Et)))) el)); eauto.
        hnf; intros; cset_tac. eapply H; split; eauto.
        unfold list_union; simpl; eapply list_union_start_swap. cset_tac; eauto.
  - general induction el.
    + reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr' a D Es Et (exp_eval (to_partial (to_total Et)) a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H; split; eauto.
        unfold list_union; simpl; eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H1; eauto. f_equal.
        symmetry. simpl.
        rewrite (IHel D Es Et (omap (exp_eval (to_partial (to_total Et))) el)); eauto.
        hnf; intros; cset_tac. eapply H; split; eauto.
        unfold list_union; simpl; eapply list_union_start_swap. cset_tac; eauto.
Qed.

Lemma combineenv_eqr:
  forall  F s D Es Et,
    agree_on eq (freeVars s ∩ D) Es Et
    -> (models F (to_total Et) s <-> models F (to_total (combineEnv D Es Et)) s).

Proof.
  intros.  general induction s; try reflexivity; simpl.
  - rewrite (IHs1 F D Es Et). rewrite (IHs2 F D Es Et).
    + reflexivity.
    + setSubst2 H.
    + setSubst2 H.
  - rewrite (IHs1 F D Es Et).  rewrite (IHs2 F D Es Et).
    + reflexivity.
    + setSubst2 H.
    + setSubst2 H.
  - rewrite (IHs F D Es Et).
    + reflexivity.
    + setSubst2 H.
  - case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e); intros.
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
        split; eauto.
      * destruct H1; eauto.
        specialize (H1 H0).
        rewrite H1.
        case_eq (val2bool v); intros.
        { rewrite (IHs1 F D Es Et).
          - reflexivity.
          - setSubst2 H. }
        { rewrite (IHs2 F D Es Et).
          - reflexivity.
          - setSubst2 H. }
     + pose proof (exp_combineenv_eqr' e D Es Et None).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto.
       * destruct H1; eauto.  specialize (H1 H0). rewrite H1.
         intuition.
  - rewrite (IHs1 F D Es Et).  rewrite (IHs2 F D Es Et).
    + reflexivity.
    + setSubst2 H.
    + setSubst2 H.
  - case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e); intros;
    case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e0); intros.
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto.
       * destruct H2; eauto. specialize (H2 H0).
         pose proof (exp_combineenv_eqr' e0 D Es Et (Some v0)).
         assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
       { hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto. }
       { destruct H5; eauto. specialize (H5 H1).
         rewrite H2, H5; intuition.
       }
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0).
        pose proof (exp_combineenv_eqr' e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { destruct H5; eauto. specialize (H5 H1).
          rewrite H5; intuition.
          destruct (exp_eval (to_partial (to_total Et)) e); intuition.
        }
    + pose proof (exp_combineenv_eqr' e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0). rewrite H2.
        intuition.
    + pose proof (exp_combineenv_eqr' e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0). rewrite H2.
        intuition.
  -  simpl. unfold labInc. destruct p.
   pose proof (explist_combineenv_eqr' a D Es Et (omap (exp_eval (to_partial (to_total(combineEnv D Es Et)))) a)).
   destruct H0; eauto.
   rewrite H0; eauto. reflexivity.
  - case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e); intros.
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H1; eauto.  specialize (H1 H0). rewrite H1.
        split; intros; eauto.
    + pose proof (exp_combineenv_eqr' e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H1; eauto. specialize (H1 H0). rewrite H1.
        split; intros; eauto.
Qed.

Lemma agree_on_ssa_combine:
  forall D D' Ds' Dt' L E s t Es Et es et,
    getAnn D = (Ds' ∩ Dt', Ds')
    -> getAnn D' = (Ds' ∩ Dt', Dt')
    -> ssa s D
    -> ssa t D'
    -> noFun s
    -> noFun t
(*    -> (forall x, x ∈ (Ds' ∩ Dt') -> exists v, E x = Some v)*)
    ->Terminates (L, E, s) (L, Es, stmtReturn es)
    -> Terminates (L, E, t) (L, Et, stmtReturn et)
    -> (agree_on eq (Exp.freeVars et) Et (combineEnv Ds' Es Et)
        /\ agree_on eq (Exp.freeVars es) Es (combineEnv Ds' Es Et)).

Proof.
  intros D D' Ds' Dt' L E s t Es Et es et.
  intros getD getD' ssaS ssaT nfS nfT (*liveness*) sterm tterm.
  split.
  - pose proof (ssa_move_return D' L E t Et et nfT ssaT tterm).
    destruct H as [D'' [ ssaRet [fstSubset sndSubset]]].
    inv ssaRet.  rewrite getD' in *; simpl in *.
    rewrite <- H1 in sndSubset.
    hnf; intros.
    unfold combineEnv.
    destruct if; eauto.
   + assert (x ∈ Ds' ∩ Dt').
     * hnf in fstSubset. hnf in H0.  specialize (H0 x H).
       cset_tac; eauto.
     *(* specialize (liveness x  H2); destruct liveness.*)
       pose proof (term_ssa_eval_agree L L s D (stmtReturn es) E Es ssaS nfS sterm).
       pose proof (term_ssa_eval_agree L L t D' (stmtReturn et) E Et ssaT nfT tterm).
       rewrite getD  in H3. rewrite getD'  in H4. simpl in *.
       rewrite <- H3; eauto. rewrite <- H4; eauto.
  - pose proof (ssa_move_return D L E s Es es nfS ssaS sterm).
    destruct H as [D'' [ssaRet [fstSubset sndSubset]]].
    inv ssaRet. rewrite getD in *; simpl in *.
    rewrite <- H1 in sndSubset.
    hnf; intros.
    unfold combineEnv.
    destruct if; eauto.
    exfalso; apply n. hnf in H0. specialize (H0 x H).
    eapply sndSubset; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
