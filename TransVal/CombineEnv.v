Require Import List Arith.
Require Import IL Annotation AutoIndTac Exp MoreExp RenamedApart Fresh Util.
Require Import SetOperations Sim Var.
Require Import bitvec smt nofun freeVars.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil GuardProps ComputeProps.

(** Definitons **)
Definition combineEnv D (E1:onv val) E2 :=
fun x => if [x ∈ D] then E1 x else E2 x.

(** Lemmata **)

Lemma combineenv_agree D E E':
  agree_on eq D (combineEnv D E E') E.

Proof.
  hnf; intros. unfold combineEnv. cases; eauto; isabsurd.
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
   hnf. cset_tac. unfold combineEnv. cases; eauto.
   eapply H. cset_tac; intuition.
 - eapply (exp_eval_agree (E:= Et)); eauto.
   hnf; cset_tac. unfold combineEnv; cases; eauto.
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
   hnf. cset_tac. unfold combineEnv, to_partial, to_total. cases; eauto.
   rewrite H. reflexivity. cset_tac; intuition.
 - eapply (exp_eval_agree (E:= to_partial (to_total Et))); eauto.
   hnf; cset_tac. unfold combineEnv, to_partial, to_total; cases; eauto.
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
        eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H0; eauto. f_equal.
        rewrite (IHel D Es Et (omap (exp_eval (combineEnv D Es Et)) el)); eauto.
        hnf. intros. cset_tac. eapply H. split; eauto.
        eapply list_union_start_swap. cset_tac; eauto.
  - general induction el.
    + reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr a D Es Et (exp_eval Et a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H. split; eauto.
        eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H1; eauto. f_equal.
        symmetry. rewrite (IHel D Es Et (omap (exp_eval  Et) el)); eauto.
        hnf. intros. cset_tac. eapply H. split; eauto.
        eapply list_union_start_swap. cset_tac; eauto.
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
        eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H0; eauto. f_equal.
        symmetry. simpl.
        rewrite (IHel D Es Et (omap (exp_eval (to_partial (to_total (combineEnv D Es Et)))) el)); eauto.
        hnf; intros; cset_tac. eapply H; split; eauto.
        eapply list_union_start_swap. cset_tac; eauto.
  - general induction el.
    + reflexivity.
    + simpl in *; hnf in H.
      pose proof (exp_combineenv_eqr' a D Es Et (exp_eval (to_partial (to_total Et)) a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H; split; eauto.
        eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H1; eauto. f_equal.
        symmetry. simpl.
        rewrite (IHel D Es Et (omap (exp_eval (to_partial (to_total Et))) el)); eauto.
        hnf; intros; cset_tac. eapply H; split; eauto.
        eapply list_union_start_swap. cset_tac; eauto.
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
      * hnf; intros. hnf in H. simpl in H. cset_tac.
      * destruct H1; eauto.
        specialize (H1 H0).
        unfold smt_eval; rewrite H1.
        case_eq (val2bool v); intros.
        { rewrite (IHs1 F D Es Et).
          - rewrite H0, H4. reflexivity.
          - setSubst2 H. }
        { rewrite (IHs2 F D Es Et).
          - rewrite H0, H4. reflexivity.
          - setSubst2 H. }
     + pose proof (exp_combineenv_eqr' e D Es Et None).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac.
       * destruct H1; eauto.  specialize (H1 H0).
         unfold smt_eval; rewrite H0, H1.
         case_eq (val2bool undef_substitute); intros.
         { rewrite (IHs1 F D Es Et).
           - reflexivity.
           - setSubst2 H. }
         { rewrite (IHs2 F D Es Et).
           - reflexivity.
           - setSubst2 H. }
  - rewrite (IHs1 F D Es Et).  rewrite (IHs2 F D Es Et).
    + reflexivity.
    + setSubst2 H.
    + setSubst2 H.
  - case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e); intros;
    case_eq (exp_eval (to_partial (to_total (combineEnv D Es Et))) e0); intros.
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac.
       * destruct H2; eauto. specialize (H2 H0).
         pose proof (exp_combineenv_eqr' e0 D Es Et (Some v0)).
         assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
       { hnf; intros. hnf in H. simpl in H. cset_tac. }
       { destruct H5; eauto. specialize (H5 H1).
         unfold smt_eval.
         rewrite H2, H5, H4, H7; eauto; intuition.
       }
    + pose proof (exp_combineenv_eqr' e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0).
        pose proof (exp_combineenv_eqr' e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { destruct H5; eauto. specialize (H5 H1).
          unfold smt_eval.
          rewrite H0, H1, H2, H5; intuition.
        }
    + pose proof (exp_combineenv_eqr' e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0).
        pose proof (exp_combineenv_eqr' e0 D Es Et (Some v)).
        destruct H5.
        { setSubst2 H. }
        { specialize (H5 H1).
        unfold smt_eval.
        rewrite H0, H1, H2, H5.
        intuition. }
    + pose proof (exp_combineenv_eqr' e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0).
        pose proof (exp_combineenv_eqr' e0 D Es Et None).
        destruct H5.
        { setSubst2 H. }
        { unfold smt_eval. rewrite H0, H1, H2, H5; eauto.
        intuition. }
  -  simpl. unfold labInc. destruct p.
     (* TODO: Make Lemma *)
     assert ((List.map (smt_eval (to_total Et)) a)
     = (List.map (smt_eval (to_total (combineEnv D Es Et))) a)).
     + general induction a.
       * eauto.
       * simpl.
         pose proof (exp_combineenv_eqr' a D Es Et (exp_eval (to_partial (to_total Et)) a)).
         pose proof (exp_combineenv_eqr' a D Es Et
                                         (exp_eval (to_partial (to_total (combineEnv D Es Et))) a)).
         destruct H0.
         { setSubst2 H. eapply list_union_start_swap; cset_tac; eauto. }
         { destruct H1.
           - setSubst2 H. eapply list_union_start_swap; cset_tac; eauto.
           - clear H3. clear H0.
             unfold smt_eval at 1. rewrite H1; eauto.
             unfold smt_eval at 2.
             destruct (exp_eval (to_partial (to_total (combineEnv D Es Et))) a);
               f_equal.
             + erewrite (IHa n _ D Es Et); eauto.
               eapply (agree_on_incl (lv:=freeVars (funcApp (LabI n) (a::a0)) ∩ D) ); eauto.
               cset_tac; eauto.
               simpl. eapply list_union_start_swap.
               cset_tac; eauto.
             + erewrite (IHa n _ D Es Et); eauto.
               eapply (agree_on_incl (lv:= (freeVars (funcApp (LabI n) (a::a0)) ∩ D))) ; eauto.
               cset_tac; eauto; simpl.
               eapply list_union_start_swap.
               cset_tac; eauto.
         }
     + rewrite H0; intuition.
    Grab Existential Variables.
    econstructor.
    econstructor.
Qed.

Lemma renamed_apart_contained x e L E s Es D:
  x \In Exp.freeVars e
  -> Terminates (L, E, s) (L, Es, stmtReturn e)
  -> noFun s
  -> renamedApart s D
  -> x \In (fst(getAnn D)) \/ x \In (snd (getAnn D)).

Proof.
  intros fv_e term_s nf_s ssa_s.
  general induction term_s.
  - inv ssa_s.
    cset_tac.
  - inv H; inv ssa_s; inv nf_s; simpl.
    + specialize (IHterm_s x e L' (E0 [x0 <- ⎣ v ⎦]) s' Es an fv_e).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite H8.
        rewrite H9 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite H8.
        rewrite H9 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (IHterm_s x e L' E' s' Es ans).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite <- H6.
        rewrite H10 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite <- H6.
        rewrite H10 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (IHterm_s x e L' E' s' Es ant).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite <- H6.
        rewrite H11 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite <- H6.
        rewrite H11 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (H0 l Y); isabsurd.
Qed.

Lemma renamed_apart_contained_list x X L E s Es f D:
  x \In list_union (Exp.freeVars ⊝ X)
  -> Terminates (L,E,s) (L, Es, stmtApp f X)
  -> noFun s
  -> renamedApart s D
  -> x \In (fst (getAnn D)) \/ x \In (snd (getAnn D)).

Proof.
  intros fv_e term_s nf_s ssa_s.
  general induction term_s.
  - inv ssa_s.
    cset_tac.
  - inv H; inv ssa_s; inv nf_s; simpl.
    + specialize (IHterm_s x X L' (E0 [x0 <- ⎣ v ⎦]) s' Es f an fv_e).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite H8.
        rewrite H9 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite H8.
        rewrite H9 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (IHterm_s x X L' E' s' Es f ans).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite <- H6.
        rewrite H10 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite <- H6.
        rewrite H10 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (IHterm_s x X L' E' s' Es f ant).
      destruct IHterm_s as [in_fv | in_dv]; auto.
      * rewrite <- H6.
        rewrite H11 in in_fv; simpl in in_fv.
        cset_tac.
      * rewrite <- H6.
        rewrite H11 in in_dv; simpl in in_dv.
        cset_tac.
    + specialize (H0 l Y); isabsurd.
Qed.

Lemma agree_on_ssa_combine:
  forall D D' L E s t Es Et es et,
    renamedApart s D
    -> renamedApart t D'
    -> fst (getAnn D) [=] fst (getAnn D')
    -> disj (snd (getAnn D)) (snd (getAnn D'))
    -> noFun s
    -> noFun t
    -> Terminates (L, E, s) (L, Es, stmtReturn es)
    -> Terminates (L, E, t) (L, Et, stmtReturn et)
    -> (agree_on eq (Exp.freeVars et) Et (combineEnv (fst(getAnn D) ∪ snd(getAnn D)) Es Et)
        /\ agree_on eq (Exp.freeVars es) Es (combineEnv (fst(getAnn D) ∪ snd(getAnn D)) Es Et)).

Proof.
  intros D D' L E s t Es Et es et.
  intros ssa_s ssa_t agree_fv disj_dv nf_s nf_t sterm tterm.
  split.
  - pose proof (ssa_move_return D' L E t Et et nf_t ssa_t tterm).
    destruct H as [D'' [ ssaRet [fstSubset sndSubset]]].
    inv ssaRet.
    hnf.
    intros x fv_Et.
    simpl in *.
    unfold combineEnv.
    cases; try reflexivity.
    + cset_tac.
      * pose proof (term_ssa_eval_agree L L s D (stmtReturn es) E Es ssa_s nf_s sterm).
        pose proof (term_ssa_eval_agree L L t D' (stmtReturn et) E Et ssa_t nf_t tterm).
        hnf in H2, H3.
        rewrite <- (H2 x H).
        rewrite (agree_fv x) in H.
        rewrite <- (H3 x H).
        reflexivity.
      * exfalso.
        pose proof (renamed_apart_contained x et L E t Et D') as fv_dv.
        destruct fv_dv as [in_fv | in_dv]; auto.
        pose proof (renamedApart_disj ssa_s) as disj_fv_dv.
        unfold disj in disj_fv_dv.
        apply (disj_fv_dv x); auto.
        rewrite (agree_fv x); auto.
  - pose proof (ssa_move_return D L E s Es es nf_s ssa_s sterm).
    destruct H as [D'' [ssaRet [fstSubset sndSubset]]].
    inv ssaRet.
    simpl in *.
    hnf; intros.
    unfold combineEnv.
    cases; auto.
    exfalso.
    apply NOTCOND. hnf in H0. specialize (H0 x H).
    cset_tac.
    pose proof (renamed_apart_contained x es L E s Es D) as fv_dv.
    destruct fv_dv; auto.
Qed.