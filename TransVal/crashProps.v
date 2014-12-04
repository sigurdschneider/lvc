Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.
Require Import tvalTactics TUtil Guards.

Definition failed (σ:F.state)  := result (σ ) = None.

Lemma crash_ssa_eval_agree L L' s D s' (E:onv val) (E':onv val)
: ssa s D
  ->noFun s
  -> Crash (L, E, s) (L', E', s')
  -> agree_on eq (fst (getAnn (D))) E E'.

Proof.
  intros.
  general induction H1; invt ssa; try invt F.step; try invt noFun; simpl;
  try reflexivity; isabsurd.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H7 in X; simpl in *; cset_tac; intuition.
    hnf; hnf in X; intros.
    unfold update in X; specialize (X x0).
    assert (x0 ∈ D0 ++ {x; {}}) by (cset_tac; left; assumption).
    specialize (X H10); decide (x === x0); eauto.
    + rewrite <- e0 in H8; exfalso; eapply H4; assumption.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H9 in X; eauto.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H10 in X; eauto.
Qed.

Lemma undef_models:
forall F E e g,
(forall x, x ∈ Exp.freeVars e -> exists v, E x = Some v)
-> undef e =Some g
-> exp_eval E e = None
-> ~ models F E g.

Proof.
intros;  hnf;  intros.
general induction e; simpl in *; try isabsurd.
- monad_inv H1.
  + specialize (IHe F E g H H0 H3 H2); eauto.
  + destruct u; isabsurd.
- destructBin b; monad_inv H1; try isabsurd.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H1 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
    * eapply (IHe1 F E s0); eauto.
      intros. cset_tac. specialize (H x). destruct H; eauto.
    * eapply (IHe1 F E s); eauto.
      intros; cset_tac; specialize (H x); destruct H; eauto.
    * pose proof (noguard_impl_eval  E e1).
      destruct H5; isabsurd; eauto.
      intros; cset_tac; destruct (H x); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H3 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
    * pose proof (noguard_impl_eval E e2).
      destruct H5; isabsurd; eauto.
      intros; cset_tac. destruct (H x0); eauto.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
  +  case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H1 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
     * eapply (IHe1 F E s0); eauto.
       intros; cset_tac. destruct (H x); eauto.
     * eapply (IHe1 F E s); eauto.
       intros; cset_tac; destruct (H x); eauto.
     * pose proof (noguard_impl_eval E e1).
       destruct H5; eauto; isabsurd.
       intros; cset_tac; destruct (H x); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H3 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
    * pose proof (noguard_impl_eval E e2).
      destruct H5; eauto; isabsurd.
      intros; cset_tac. destruct (H x0); eauto.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H1 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
     * eapply (IHe1 F E s0); eauto.
       intros; cset_tac. destruct (H x); eauto.
     * eapply (IHe1 F E s); eauto.
       intros; cset_tac; destruct (H x); eauto.
     * pose proof (noguard_impl_eval  E e1).
       destruct H5; eauto; isabsurd.
       intros; cset_tac; destruct (H x); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H3 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
    * pose proof (noguard_impl_eval E e2).
      destruct H5; eauto; isabsurd.
      intros; cset_tac. destruct (H x0); eauto.
    * eapply (IHe2 F E s); eauto.
      intros; cset_tac. destruct (H x0); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H1 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
     * eapply (IHe1 F E s0); eauto.
       intros; cset_tac. destruct (H x); eauto.
     * eapply (IHe1 F E s); eauto.
       intros; cset_tac; destruct (H x); eauto.
     * pose proof (noguard_impl_eval E e1).
       destruct H5; eauto; isabsurd.
       intros; cset_tac; destruct (H x); eauto.
  +  case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H3 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
     * pose proof (noguard_impl_eval E e2).
       destruct H5; eauto; isabsurd.
       intros; cset_tac. destruct (H x0); eauto.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H1 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
    * eapply (IHe1 F E s0); eauto.
      intros; cset_tac. destruct (H x); eauto.
    * eapply (IHe1 F E s); eauto.
      intros; cset_tac; destruct (H x); eauto.
    * pose proof (noguard_impl_eval E e1).
      destruct H5; eauto; isabsurd.
      intros; cset_tac; destruct (H x); eauto.
  +  case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H4 in H0; rewrite H3 in H0; simpl in H0; inversion H0;
    rewrite <- H6 in H2; simpl in H2; try destruct H2.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
     * pose proof (noguard_impl_eval E e2).
       destruct H5; eauto; isabsurd.
       intros; cset_tac. destruct (H x0); eauto.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H1, H4 in H0; simpl in H0; inversion H0; clear H0;
    rewrite <- H6 in H2; clear H6;
    simpl in H2.
    * destruct H2; destruct H2.  eapply (IHe1 F E s0); eauto.
      intros; cset_tac. destruct (H x); eauto.
    * destruct H2.  eapply (IHe1 F E s); eauto.
      intros; cset_tac. destruct (H x); eauto.
    * destruct H2. pose proof (noguard_impl_eval E e1); eauto.
      destruct H5; eauto; isabsurd.
      intros; cset_tac. destruct (H x); eauto.
    * pose proof (noguard_impl_eval E e1).
      destruct H0; eauto; isabsurd.
      intros; cset_tac. destruct (H x); eauto.
  +  case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H3, H4 in H0; simpl in H0; inversion H0; clear H0;
    rewrite <- H6 in H2; clear H6;
    simpl in H2; destruct H2; try destruct H2.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
     * pose proof (noguard_impl_eval E e2).
       destruct H5; eauto; isabsurd.
       intros; cset_tac. destruct (H x0); eauto.
     * eapply (IHe2 F E s); eauto.
       intros; cset_tac. destruct (H x0); eauto.
     * pose proof (noguard_impl_eval E e2).
       destruct H0; eauto; isabsurd.
       intros; cset_tac. destruct (H x0); eauto.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H1, H3 in H0; simpl in H; inversion H0; clear H0;
    rewrite <- H5 in H2; destruct H2; try destruct H2; clear H5.
    * simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H0.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H1 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H0.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H1 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H0.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H1 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      case_eq(bvZero x0); intros.
      Focus 2. rewrite H0 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))).  eapply zero_implies_eq; eauto.
Qed.

Lemma undefList_models:
  forall F E el gl,
    (forall x, x ∈ list_union (List.map Exp.freeVars el) -> exists v, E x = Some v)
    -> undefLift el = Some gl
    -> omap (exp_eval E) el = None
    -> ~ models F E gl.

Proof.
  intros.
  general induction el; simpl in *.
  - case_eq (undef a); case_eq (undefLift el); intros;
    rewrite H2, H3 in H0; simpl in H0; inversion H0; simpl; hnf; intros.
    + destruct H4.
      monad_inv (H1); isabsurd.
      * pose proof (undef_models F E a s0).
        eapply H1; eauto. setSubstUnion H.
      * exploit (IHel F E s); eauto.
        setSubstUnion H.
    +  rewrite <- H5 in H4.
      monad_inv H1; isabsurd.
      * pose proof (undef_models F E a s).
        eapply H1; eauto.
        setSubstUnion H.
      * pose proof (noguardlist_impl_eval E el).
        destruct H6; eauto; isabsurd.
        setSubstUnion H.
    + monad_inv H1; isabsurd.
      * pose proof (noguard_impl_eval E a).
        destruct H1; eauto; isabsurd.
        setSubstUnion H.
      * exploit (IHel F E s); eauto; isabsurd.
        setSubstUnion H.
Qed.

Lemma crash_impl_err:
  forall (E:onv val) s Es s' L L',
    noFun s
    -> Crash (L, E, s) (L', Es, s')
    -> ( star2 F.step (L,E,s) nil (L', Es, s'))
       /\ normal2 F.step (L', Es, s') /\ failed (L', Es, s').

Proof.
  intros E s Es s' L L' nf Crash.
  general induction Crash.
  - split; econstructor.
    +  hnf. intros. destruct H0. destruct H0. inversion H0.
       rewrite H in def; isabsurd.
    + unfold failed; eauto.
   - split; eauto;  econstructor.
- destruct sigma'. destruct p. inversion nf; subst; try isabsurd.
  + exploit (IHCrash o s1 Es s' l L') ; try reflexivity; eauto; subst.
    * inversion H; eauto.
    * destruct X; split; eauto.
      change (star2 F.step (L0, E0, stmtExp x e s1) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto. destruct a; eauto; isabsurd.
  + inversion H; exploit (IHCrash o s Es s' l L'); subst; eauto.
    * destruct X; split; eauto.
      change (star2 F.step (l, o, stmtIf e s t) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto.
    * destruct X; split; eauto.
      change (star2 F.step (l, o, stmtIf e s1 s) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto.
Qed.

Lemma nostep_let:
forall L E x e s,
normal2 F.step (L, E, stmtExp x e s)
-> exp_eval E e = None.

Proof.
intros. case_eq (exp_eval E e); intros; eauto.
exfalso; apply H. unfold reducible2.
exists EvtTau. exists (L, E[x<-Some v],s). econstructor; eauto.
Qed.

Lemma nostep_if:
forall L E e t f,
normal2 F.step (L, E, stmtIf e t f)
-> exp_eval E e = None.

Proof.
intros. case_eq (exp_eval E e); intros; eauto.
exfalso; eapply H; unfold reducible2.
exists (EvtTau).
case_eq (val2bool v); intros.
- exists (L, E, t); econstructor; eauto.
- exists (L, E, f); econstructor; eauto.
Qed.

Lemma crash_impl_models:
  forall L L' D s E Es s',
    ssa s D
    -> (forall x, x ∈ fst(getAnn D) -> exists v, E x = Some v)
    -> noFun s
    -> Crash (L, E, s) (L', Es, s')
    -> models (fun _ => fun _ => true) Es (translateStmt s target).

Proof.
  intros. general induction H2; simpl.
  - case_eq (undefLift Y); intros; simpl; intros; eauto.
    + pose proof (undefList_models (fun _ => fun _ => true) E0 Y s).
      eapply H6; eauto.
      intros. eapply H1. inversion H0.
      simpl. eauto.
    + pose proof (noguardlist_impl_eval E0 Y).
      destruct H5; eauto; isabsurd.
      intros; eapply H1. inversion H0; simpl; eauto.
  - inversion H4; subst.
    + case_eq (undef e); simpl; intros.
      * pose proof (nostep_let L0 E0 x e s H0).
        pose proof (undef_models (fun _ => fun _ => true) E0 e s0).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; invt ssa. specialize (H3 x0). eapply H3.
          simpl; cset_tac; eauto. }
        { rewrite H6.  simpl.  intros. specialize (H8 H9 H6 H7 H10); isabsurd. }
      * pose proof (noguard_impl_eval E0 e).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros. inversion H2. specialize (H3 x0). subst. simpl in H3.
          hnf in H13.  specialize (H13 x0 H8).  destruct (H3 H13).
          exists x1; eauto. }
        { specialize (H7 H8 H6). destruct H7.
        assert (exists y σ, F.step (L0, E0, stmtExp x e s) y σ )
            by (exists EvtTau; exists (L0, E0[x<-Some x0], s); econstructor; eauto ).
          hnf in H0.  unfold reducible2 in H0. specialize (H0 H9); isabsurd. }
    + case_eq (undef e); simpl; intros.
      * pose proof (nostep_if L0 E0 e s t H0).
        pose proof (undef_models (fun _ => fun _ => true) E0 e s0).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; invt ssa. eapply (H3 x). simpl; cset_tac; eauto. }
        { rewrite H7; simpl; intros. specialize (H9 H10 H7 H8 H11); isabsurd. }
      * pose proof (noguard_impl_eval E0 e).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; invt ssa. specialize (H3 x); subst; simpl in *. cset_tac.
          hnf in H13. destruct (H3 (H13 x H9)).
          exists x0. rewrite H10; eauto. }
        { specialize (H8 H9 H7).
        assert (exists y σ, F.step (L0, E0 , stmtIf e s t) y σ).
        { exists EvtTau. destruct H8. case_eq (val2bool x); intros.
          - exists (L0, E0, s). econstructor; eauto.
          - exists (L0, E0, t). econstructor; eauto. }
        { specialize (H0 H10); isabsurd. } }
    + isabsurd.
    +  case_eq (undef e); simpl; intros.
       * pose proof (undef_models (fun _ => fun _ => true) E0 e s).
         assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; inversion H2; cset_tac.  simpl in H3. specialize (H3 x).
        destruct H1; eauto. }
       { rewrite H5; simpl. specialize (H6 H7 H5 H1); isabsurd. }
       * pose proof (noguard_impl_eval E0 e).
         assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
         { intros. inversion H2. simpl in H3. specialize (H3 x).
           hnf in H9. cset_tac. destruct H3; eauto. }
         { simpl in H3. specialize (H6 H7). specialize (H6 H5).
           destruct H6. rewrite H5; simpl; intros. simpl in H1.
           rewrite H6 in H1; isabsurd. }
  - destruct sigma' as  [[L E'] sc].
    case_eq s0; intros; subst; simpl in*; invt ssa; invt noFun; invt F.step; subst.
    + exploit (IHCrash L L' an sc (E0 [x<-Some v]) Es s'); eauto; intros.
      * rewrite H12 in H5.  simpl in H5.  cset_tac.  destruct H5.
        { inversion H; subst.  simpl in H3; specialize (H3 x0 H5).
          destruct H3. exists x1. unfold update.
          decide (x === x0); eauto; isabsurd. }
        { rewrite H5. unfold update.
          decide (x === x); isabsurd.
          exists v; eauto. }
      * case_eq (undef e); intros.
        { simpl; split; eauto. unfold evalSexp.
          assert ( exp_eval Es e = Some v /\ exp_eval Es (Var x) = Some v).
          - split.
            + eapply (exp_eval_agree (E:=E0)); eauto.
            hnf. intros.  hnf in H9. specialize (H9 x0 H10).
            pose proof (crash_ssa_eval_agree L L' (stmtExp x e sc) (ann1 (D0, D') an) s' E0 Es).
            eapply H13; eauto; econstructor; eauto.
            +  eapply (exp_eval_agree (E:= E0[x<-Some v])).
              * hnf. intros; simpl in H10.
                eapply (crash_ssa_eval_agree L L' sc an s' (E0[x<-Some v]) Es); eauto.
                rewrite H12; simpl. cset_tac. right. rewrite H10; eauto.
              * simpl. unfold update. decide (x === x); eauto; isabsurd.
          - destruct H10.  rewrite H10, H13.  eapply bvEq_equiv_eq; eauto. }
        { simpl; split; eauto. unfold evalSexp. inversion H.
          assert ( exp_eval Es e = Some v).
          - eapply (exp_eval_agree (E:= E0)); eauto.
            hnf. intros.  hnf in H9. specialize (H9 x1 H7).
            pose proof (crash_ssa_eval_agree L L' (stmtExp x e sc) (ann1 (D0, D') an) s' E0 Es).
            eapply H18; eauto; econstructor;  eauto.
          - assert (exp_eval Es (Var x) =Some v).
            + eapply (exp_eval_agree (E:= E0[x<-Some v])).
              * hnf. intros. simpl in H18. cset_tac.
                eapply (crash_ssa_eval_agree L L' sc an s' (E0[x<-Some v]) Es); eauto.
                rewrite H12; simpl. cset_tac. right. rewrite H18; eauto.
              * simpl. unfold update. decide (x === x).
                { reflexivity. }
                { isabsurd. }
            + rewrite H18, H7. eapply bvEq_equiv_eq.
              reflexivity. }
    +  exploit (IHCrash L L' ans sc E' Es s'); eauto.
       * intros. rewrite H14 in H5. simpl in *; eauto.
       * case_eq (undef e); intros; simpl; unfold evalSexp.
         { assert (exp_eval Es e = Some v).
           - eapply (exp_eval_agree (E:= E')); eauto.
             hnf; intros.  hnf in H8.  specialize (H8 x H6).
             pose proof (crash_ssa_eval_agree L L' (stmtIf e sc t) (ann2 (D0, D') ans ant) s'  E' Es).
             eapply H13; eauto; econstructor; eauto.
           - rewrite H6.  rewrite condTrue.  intros; subst; eauto. }
         { assert (exp_eval Es e = Some v).
           - eapply (exp_eval_agree (E:= E')); eauto.
             hnf; intros.  hnf in H8.  specialize (H8 x H6).
             pose proof (crash_ssa_eval_agree L L' (stmtIf e sc t) (ann2 (D0, D') ans ant) s'  E' Es).
             eapply H13; eauto; econstructor; eauto.
           - rewrite H6.  rewrite condTrue.  intros; subst; eauto. }
    + exploit (IHCrash L L' ant sc E' Es s'); eauto.
      * intros. rewrite H15 in H5; simpl in *; eauto.
      *  case_eq (undef e); intros; simpl; unfold evalSexp.
         {  assert (exp_eval Es e = Some v).
            - eapply (exp_eval_agree (E:= E')); eauto.
              hnf; intros.  hnf in H8.  specialize (H8 x H6).
              pose proof (crash_ssa_eval_agree L L' (stmtIf e s sc) (ann2 (D0, D') ans ant) s'  E' Es).
              eapply H13; eauto; econstructor; eauto.
            - rewrite H6.  rewrite condFalse. intros; subst; eauto. }
         { assert (exp_eval Es e = Some v).
           - eapply (exp_eval_agree (E:= E')); eauto.
             hnf; intros.  hnf in H8.  specialize (H8 x H6).
              pose proof (crash_ssa_eval_agree L L' (stmtIf e s sc) (ann2 (D0, D') ans ant) s'  E' Es).
              eapply H13; eauto; econstructor; eauto.
           - rewrite H6.  rewrite condFalse.  intros; subst; eauto. }
    + isabsurd.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)