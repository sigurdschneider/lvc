Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.
Require Import tvalTactics TUtil Guards.

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

Definition combineEnv D (E1:onv val) E2 :=
fun x => if [x ∈ D] then E1 x else E2 x.

Lemma ssa_eval_agree s D s' (E:onv val) (E':onv val)
 : ssa s D
   -> noFun s
   -> Terminates (nil,E, s) (nil, E', s')
   -> agree_on eq (fst (getAnn D)) E E'.

Proof.
  intros.
  general induction H1; invt ssa; try invt F.step;try invt noFun; simpl.
  - reflexivity.
  - reflexivity.
-  inversion H2.
   exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
   rewrite H18 in X; simpl in *. cset_tac; intuition.  hnf. hnf in X. intros.
    unfold update in X. specialize (X x0).
    assert (x0 ∈ D0 ++ {x; {}}) by (cset_tac; left; assumption).
    specialize (X H10). decide (x === x0).
    + rewrite  e0 in H14; exfalso; apply H14; assumption.
    + assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H25 in X; simpl in *. assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H26 in X; simpl in *; assumption.
- inversion H0.
Qed.

Lemma terminates_impl_models :
forall s D E s' E',
ssa  s D
-> noFun s
-> Terminates (nil,E, s) (nil, E', s')
->  models (fun (f:pred) (x:vallst) => true)  E'  (translateStmt s source).

Proof.
intros.
general induction H1; simpl.
- assert (X: models (fun (_:pred) (_:vallst) => true) E0 (smtReturn e)).
  + simpl. econstructor.
  + case_eq (undef e); eauto; intros.
    * simpl; split; eauto.
      eapply (guard_true_if_eval); eauto.
- case_eq (undefLift x); intros; simpl; eauto.
  + split; eauto.
       eapply (guardList_true_if_eval _ E0); eauto.
- inv H; invt ssa; invt noFun; simpl in * |- *; subst.
  + case_eq(undef e); intros; simpl; split; eauto.
    * eapply (guard_true_if_eval _ E'0 e s v ); eauto.
      eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
      { eapply (ssa_eval_agree  (stmtExp x e s') _ s'0); eauto.
        econstructor; eauto. }
      { eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
    * split; eauto; subst.
      assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0[x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))).
          + subst.  eapply (ssa_eval_agree s' _ s'0 _ E'0); eauto.
          + rewrite H11. unfold fst. cset_tac. right; rewrite H6; reflexivity.
        - unfold exp_eval. unfold update. decide (x===x).
          + reflexivity.
          + exfalso.  apply n; reflexivity. }
      assert (X2: exp_eval E'0 e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
        - eapply (ssa_eval_agree  (stmtExp x e s') _ s'0); eauto.
        econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold evalSexp. rewrite X1; rewrite X2.
         eapply  bvEq_equiv_eq. reflexivity.  }
    * assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0 [x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))).
          + eapply (ssa_eval_agree s' _ s'0); eauto.
          + rewrite H11. unfold fst. cset_tac. right; rewrite H6; reflexivity.
        - unfold exp_eval. unfold update. decide (x===x).
          + reflexivity.
          + exfalso.  apply n; reflexivity. }
      assert (X2: exp_eval E'0 e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
        - eapply (ssa_eval_agree  (stmtExp x e s') _ s'0); eauto.
        econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold evalSexp. rewrite X1; rewrite X2.
         eapply  bvEq_equiv_eq. reflexivity.  }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'0 ( ite e (translateStmt s' source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
        by (hnf; intros; hnf in H7; specialize (H7 a); exact (H7 H4)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (ssa_eval_agree (stmtIf e s' b2) _ s'0); eauto; econstructor; eauto).
      erewrite (exp_eval_agree (E:=E') (E':=E'0)); eauto. simpl. rewrite condTrue.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e _ v); eauto.
          assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
            by (hnf; intros; hnf in H7; specialize (H7 a); hnf; cset_tac; simpl;  exact (H7 H5)).
          assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
            by ( eapply (ssa_eval_agree (stmtIf e s' b2) _ s'0); eauto; econstructor; eauto).
            eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
            eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'0( ite e (translateStmt b1 source) (translateStmt s' source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
        by (hnf; intros; hnf in H7; specialize (H7 a); exact (H7 H4)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (ssa_eval_agree (stmtIf e b1 s') _ s'0); eauto; econstructor; eauto).
      erewrite (exp_eval_agree (E:=E') (E':=E'0)); eauto. simpl. rewrite condFalse.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e _ v); eauto.
          + assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
              by (hnf; intros; hnf in H7; specialize (H7 a); hnf; cset_tac; simpl;  exact (H7 H5)).
            assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
              by ( eapply (ssa_eval_agree (stmtIf e b1 s') _ s'0); eauto; econstructor; eauto).
            eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
            eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + inversion H0.
Qed.

Lemma undef_models:
forall F E e g,
undef e =Some g
-> exp_eval E e = None
-> ~ models F E g.

Proof.
intros;  hnf;  intros.
general induction e; simpl in *; try isabsurd.
- monad_inv H0.
  + specialize (IHe F E g H H2 H1); eauto.
  + destruct u; isabsurd.
- destructBin b; monad_inv H0; try isabsurd.
  + case_eq (undef e1); case_eq (undef e2); intros;
    rewrite H0 in H; rewrite H3 in H; simpl in H; inversion H;
    rewrite <- H5 in H1; simpl in H1; try destruct H1.
    * exact (IHe1 F E s0 H3 H2 H1).
    * exact (IHe1 F E s H3 H2 H1).
    * pose proof (noundef  E e1 H3). admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + case_eq (undef e1); case_eq (undef e2); intros.
    * rewrite H0, H3 in H; simpl in H; inversion H. clear H.
      rewrite <- H5 in H1; clear H5.
      simpl in H1; destruct H1. destruct H1. admit.
    * admit.
    * pose proof (noundef E e1 H3). admit.
    * admit.
  + admit.
  + case_eq (undef e1); case_eq (undef e2); intros.
    * rewrite H0, H2 in H; simpl in H; inversion H; clear H.
      rewrite <- H4 in H1; clear H4.
      simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H3 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * rewrite H0, H2 in H; simpl in H; inversion H; clear H.
      rewrite <- H4 in H1; clear H4.
      simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H3 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * rewrite H0, H2 in H; simpl in H; inversion H; clear H.
      rewrite <- H4 in H1; clear H4.
      simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      apply H.  case_eq(bvZero x0); intros.
      Focus 2. rewrite H3 in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))). clear H.  eapply zero_implies_eq; eauto.
    * rewrite H0, H2 in H; simpl in H; inversion H; clear H.
      rewrite <- H4 in H1; clear H4.
      simpl in H1. destruct H1. simpl in EQ2. unfold bvDiv in EQ2.
      case_eq(bvZero x0); intros.
      Focus 2. rewrite H in EQ2. destruct (bvLessZero x); destruct (bvLessZero x0); isabsurd.
      unfold evalSexp. rewrite EQ1. simpl.
      change (val2bool (bvEq x0 (zext k (O::nil)))).  eapply zero_implies_eq; eauto.
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

(*Lemma nostep_goto:
forall L E x, *)

Lemma crash_impl_models:
  forall D s E Es s',
    ssa s D
    -> (forall x, x ∈ fst(getAnn D) -> exists v, E x = Some v)
    -> noFun s
    -> Crash ( nil, E, s) (nil, Es, s')
    -> models (fun _ => fun _ => true) Es (translateStmt s target).

Proof.
  intros. general induction H2; simpl.
  - case_eq (undef e); simpl; intros.
    + pose proof (undef_models (fun _ => fun _ => true) E0 e s H0 H H4).
      isabsurd.
    + pose proof (noguard_impl_eval E0 e).
      assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
      * intros. inversion H1. specialize (H2 x). hnf in H8. cset_tac.
        simpl in H2. specialize (H8 x H6). specialize (H2 H8).
        destruct H2. exists x0. rewrite H2; eauto.
      * specialize (H5 H6 H0). destruct H5; rewrite H5 in *.
        isabsurd.
  - case_eq (s0); intros; subst; simpl in *.
    + case_eq (undef e); simpl; intros.
      * pose proof (nostep_let nil E0 x e s H0).
        pose proof (undef_models (fun _ => fun _ => true) E0 e s0 H5 H7).
        isabsurd.
      * pose proof (noguard_impl_eval E0 e).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros. inversion H2. specialize (H3 x0). subst. hnf in H12.
          specialize (H12 x0 H7). simpl in H3. destruct (H3 H12).
          exists x1. rewrite H8; eauto. }
        specialize (H6  H7 H5). destruct H6.
        assert (exists y σ, F.step (nil, E0, stmtExp x e s) y σ )
          by (exists EvtTau; exists (nil, E0[x<-Some x0], s); econstructor; eauto).
       hnf in H.  unfold reducible2 in H. specialize (H0 H8); isabsurd.
    + case_eq (undef e); simpl; intros.
      * pose proof (nostep_if nil E0 e s t H0).
        pose proof (undef_models (fun _ => fun _ => true) E0 e s0 H5 H7 H6).
        isabsurd.
      * pose proof (noguard_impl_eval E0 e).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; invt ssa. specialize (H3 x); subst; simpl in *. cset_tac.
          hnf in H11. destruct (H3 (H11 x H7)).
          exists x0. rewrite H8; eauto. }
        { specialize (H6 H7 H5).
        assert (exists y σ, F.step (nil, E0 , stmtIf e s t) y σ).
        { exists EvtTau. destruct H6. case_eq (val2bool x); intros.
          - exists (nil, E0, s). econstructor; eauto.
          - exists (nil, E0, t). econstructor; eauto. }
        { specialize (H0 H8); isabsurd. } }
    + case_eq (undefLift Y); intros.
      * admit.
      * admit.
    + specialize (H e). isabsurd.
    + inversion H4.
    + inversion H4.
  - destruct sigma' as  [[L E'] sc].
    case_eq s; intros; subst; simpl in*; invt ssa; invt noFun; invt F.step; subst.
    + exploit (IHCrash an sc (E[x<-Some v]) Es s'); eauto; intros.
      * rewrite H11 in H4.  simpl in H4.  cset_tac.  destruct H4.
        { inversion H; subst.  simpl in H1; specialize (H1 x0 H4).
          destruct H1. exists x1. unfold update.
          decide (x === x0).
          - rewrite <- e0 in H4. isabsurd.
          - rewrite H1; eauto. }
        { rewrite H4. unfold update.
          decide (x === x); isabsurd.
          exists v; eauto. }
      * case_eq (undef e); intros.
        { simpl; split; eauto. unfold evalSexp.
          assert ( exp_eval Es e = Some v /\ exp_eval Es (Var x) = Some v).
          - split.
            + eapply (exp_eval_agree (E:= E)); eauto.
            hnf. intros.  hnf in H8. specialize (H8 x0 H9).
            admit.
            +  eapply (exp_eval_agree (E:= E[x<-Some v])).
              * hnf. intros.
                admit.
              * simpl. unfold update. decide (x === x).
                { reflexivity. }
                { isabsurd. }
          - destruct H9.  rewrite H9, H12.  eapply bvEq_equiv_eq.
              reflexivity. }
        { simpl; split; eauto. unfold evalSexp. inversion H.
          assert ( exp_eval Es e = Some v).
          - eapply (exp_eval_agree (E:= E)); eauto.
            hnf. intros.  hnf in H8. specialize (H8 x1 H6).
            admit.
          - assert (exp_eval Es (Var x) =Some v).
            + eapply (exp_eval_agree (E:= E[x<-Some v])).
              * hnf. intros. simpl in H17. cset_tac.
                admit.
              * simpl. unfold update. decide (x === x).
                { reflexivity. }
                { isabsurd. }
            + rewrite H17, H6. eapply bvEq_equiv_eq.
              reflexivity. }
    + inversion H; subst.
      * exploit (IHCrash ans sc E' Es s'); eauto.
        { admit. }
        { case_eq (undef e); intros; simpl; unfold evalSexp.
          - assert (exp_eval Es e = Some v).
            + eapply (exp_eval_agree (E:= E')); eauto.
              hnf; intros.  hnf in H7.  specialize (H7 x H5).
              admit.
            + rewrite H5.  rewrite condTrue.  intros; subst; eauto.
          - admit. }
      * exploit (IHCrash ant sc E' Es s'); eauto.
        { admit. }
        {  case_eq (undef e); intros; simpl; unfold evalSexp; admit. }
    + admit.
    + inversion H. inversion Ldef0.
Qed.


Lemma noFun_impl_term_crash :
forall E s, noFun s
->  exists E' s', Terminates (nil,E,s)(nil,E',s') \/ Crash (nil,E,s)(nil,E',s').

Proof.
intros.
general induction H.
- admit. (*case_eq (exp_eval E e); intros.
  + specialize (IHnoFun (E[x <- Some v])). destruct IHnoFun as [E' [s' [noterm | nocrash]]].
    * exists (E[x<- Some v]). exists s. left. eapply (TerminatesStep nil E econstructor; eauto. *)
- admit.
- admit.
- admit.
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

Lemma unsat_extension:
forall D E E' s s' pol P Q,
(forall F E, models F E Q -> ~ models F E (smtAnd (translateStmt s pol) P))
-> ssa s D
-> noFun s
->Terminates (nil, E, s) (nil, E', s')
-> exists Q', (forall F, models F E'  Q' ) /\
              freeVars Q' ⊆  snd(getAnn D) /\
              (forall F E, models F E (smtAnd Q Q') -> ~ models F E (smtAnd (translateStmt s' pol) P)).

Proof.
intros. general induction H2.
- simpl in *. destruct pol.
  + inversion H1. simpl in *.  exists (smtTrue). simpl. split; eauto; split; cset_tac.
    * exfalso; assumption.
    * specialize (H0 F E H3). assumption.
  + inversion H1. simpl in *; exists (smtTrue). simpl. split; eauto; split; cset_tac.
    * exfalso; assumption.
    * specialize (H0 F E H3); assumption.
-  simpl in *; destruct pol.
   + inversion H1. simpl in *. exists (smtTrue). simpl; split; eauto; split; cset_tac.
     * exfalso; assumption.
     * specialize (H0 F E H3). assumption.
   + inversion H1; simpl in *; exists (smtTrue). simpl; split; eauto; split; cset_tac.
     * exfalso; assumption.
     * specialize (H0 F E H3); assumption.
- simpl in *.  inv H.
  + simpl in *. inv H3.
    specialize (IHTerminates an (E0[x <- Some v]) E'0 s' s'0).
    inv H4. destruct pol; simpl in *.
    * specialize (IHTerminates source P (smtAnd Q (guardGen (undef e) source (constr (Var x) e)))).
      destruct IHTerminates as [Q' IHT]; intros; eauto; simpl in *.
      { specialize (H1 F E). destruct H5 as [H5 H5']. specialize (H1 H5).  hnf in H0; hnf; intros.
        eapply H1. destruct H7. split; simpl; eauto. destruct (undef e); simpl in *; eauto. destruct H5'.
        split; eauto. }
      { exists (smtAnd Q' (guardGen (undef e) source (constr (Var x) e))).
        simpl in *. intros.
        destruct IHT as [IHT1 [ IHT2 IHT3 ]].
        split; eauto; split.
        - exact (IHT1 F).
        -  assert (models F E'0 (constr (Var x) e)).
           + simpl. unfold evalSexp.
              assert (exp_eval E'0 (Var x) = Some v).
             * eapply (exp_eval_agree (E:= E0[x <- Some v])).
               { simpl. hnf. intros. inv H3. eapply (ssa_eval_agree s'); eauto. rewrite H12.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E'0 e = Some v).
              { eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros; eapply (ssa_eval_agree); eauto.
                econstructor; eauto. }
              rewrite H5; rewrite H7; simpl.  eapply bvEq_equiv_eq. reflexivity.
           + case_eq (undef e); intros; simpl.
             * split; eauto.
               eapply (guard_true_if_eval _ _ e); eauto.
               eapply (exp_eval_agree (E:=E0)); eauto. hnf; intros. eapply (ssa_eval_agree); eauto.
               econstructor; eauto.
             * simpl in *; assumption.
        - hnf. intros. hnf in H9. specialize (H9 a).  eapply ssa_incl in H11. hnf in H11. specialize (H11 a).
          simpl in H11. hnf in IHT2. specialize (IHT2 a). cset_tac. destruct H5.
          +  rewrite H12 in IHT2. exact (IHT2 H5).
          + rewrite H12 in H11. apply H11.  simpl.  cset_tac.  case_eq (undef e); intros.
            * rewrite H7 in H5. simpl in H5. cset_tac. destruct H5; eauto.
              { left; eapply H9. eapply (freeVars_undef _ _ _ H7 H5). }
              { destruct H5.
                - rewrite H5. right; reflexivity.
                - left; eapply H9. assumption. }
            * rewrite H7 in H5. simpl in H5.  cset_tac. destruct H5.
              { rewrite H5. right; reflexivity. }
              { left; eapply H9; eauto. }
        - intros. eapply IHT3. destruct H5 as [H5 [H5' H5'']]; split; eauto; split; eauto.
      }
    * specialize (IHTerminates target P (smtAnd Q (guardGen (undef e) target (constr (Var x) e)))).
      destruct IHTerminates as [Q' IHT]; intros; eauto; simpl in *.
      { specialize (H1 F E). destruct H5 as [H5 H5']. specialize (H1 H5).  hnf in H1; hnf; intros.
        eapply H1. destruct H7. split; simpl; eauto. destruct (undef e); simpl in *; eauto. }
      { exists (smtAnd Q' (guardGen (undef e) target (constr (Var x) e))).
        simpl in *. intros.
        destruct IHT as [IHT1 [ IHT2 IHT3 ]].
        split; eauto; split.
        - exact (IHT1 F).
        -  assert (models F E'0 (constr (Var x) e)).
           + simpl. unfold evalSexp.
              assert (exp_eval E'0 (Var x) = Some v).
             * eapply (exp_eval_agree (E:= E0 [x <- Some v])).
               { simpl. hnf. intros. inv H4. eapply (ssa_eval_agree s'); eauto. rewrite H12.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E'0  e = Some v).
              { eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros; eapply (ssa_eval_agree); eauto.
                econstructor; eauto. }
              rewrite H5; rewrite H7; simpl.  eapply bvEq_equiv_eq. reflexivity.
           + case_eq (undef e); intros; simpl.
             * intros; eauto.
             * simpl in H5. assumption.
        - hnf. intros. hnf in H9. specialize (H9 a).  eapply ssa_incl in H11. hnf in H11. specialize (H11 a).
          simpl in H11. hnf in IHT2. specialize (IHT2 a). cset_tac. destruct H5.
          +  rewrite H12 in IHT2. exact (IHT2 H5).
          +  case_eq (undef e); intros.
            * rewrite H7 in H5. simpl in H5. cset_tac. rewrite H12 in H11.  simpl in H11. apply H11.
              simpl. cset_tac. destruct H5; eauto.
              { left. eapply H9. eapply (freeVars_undef _ _ _ H7 H5). }
              { destruct H5.
                - rewrite H5; right; reflexivity.
                - left; eapply H9; eauto. }
            * rewrite H7 in H5. simpl in H5. cset_tac. rewrite H12 in H11; apply H11.
              simpl; cset_tac; destruct H5.
              { rewrite H5; right; reflexivity. }
              { left; eapply H9; eauto. }
        - intros. eapply IHT3. destruct H5 as [H5 [H5' H5'']]; split; eauto; split; eauto.
      }
  + simpl in *; inv H3; inv H4.
    specialize (IHTerminates ans E' E'0 s' s'0).
    destruct pol; simpl in *.
    * specialize (IHTerminates  source P (smtAnd Q (guardGen (undef e) source (ite e (smtTrue) (smtFalse))))).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { specialize (H1 F E). destruct H5. specialize (H1 H5). hnf. intros. eapply H1.
        destruct H13; split; eauto.
        case_eq (undef e); intros; simpl in *.
        - rewrite H18 in H6; simpl in H6. destruct H6. split; eauto. case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + exfalso. rewrite H20 in H19. assumption.
        - rewrite H18 in H6. simpl in H6. case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + rewrite H19 in H6. exfalso; assumption. }
      { exists (smtAnd Q' (guardGen (undef e) source (ite e smtTrue smtFalse))).
        simpl in *; intros.
        destruct IHT as [IHT1 [IHT2 IHT3]].
        split; eauto; split.
        - exact (IHT1 F).
        - assert (X': exp_eval E'0 e = Some v).
          + eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
              hnf. intros. eapply (ssa_eval_agree s' _ s'0 E' E'0); eauto.
              rewrite H14. simpl. eapply H8; eauto.
          + assert (X: models F E'0 (ite e smtTrue smtFalse))
            by ( simpl; unfold evalSexp; rewrite X'; rewrite condTrue; econstructor).
            case_eq (undef e); intros; eauto.
            simpl; split; eauto.
            eapply (guard_true_if_eval); eauto.
        - rewrite H14 in IHT2.  cset_tac. hnf in IHT2; simpl in IHT2.  destruct H5.
          +  eapply H10. left; apply IHT2; assumption.
          +  case_eq (undef e); intros; simpl in *.
             * rewrite H6 in H5. simpl in H5. cset_tac. destruct H5 as [ H5 | [[H5 | H5] | H5]]; intuition.
               { eapply (freeVars_undef a) in H5; eauto. eapply H10. hnf in H8. specialize (H8 a H5).
                 rewrite <- (H9 a) in  H8. destruct H8; eauto. }
               { hnf in H8. specialize (H8 a H5). eapply H10; erewrite <- H9 in H8. destruct H8; eauto. }
             * rewrite H6 in H5. simpl in *. cset_tac. destruct H5 as [[H5 | H5] | H5]; intuition.
               hnf in H8. specialize (H8 a H5).  eapply H10; erewrite <- H9 in H8. destruct H8; eauto.
        - intros. destruct H5 as [H5 [H5' H5'']].
          hnf. intros.  eapply (IHT3 F E); eauto.
        }
    * specialize (IHTerminates  target P (smtAnd Q (guardGen (undef e) source (ite e (smtTrue) (smtFalse))))).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { specialize (H1 F E). destruct H5. specialize (H1 H5). hnf. intros. eapply H1.
        destruct H13; split; eauto.
        case_eq (undef e); intros; simpl in *.
        - rewrite H18 in H6; simpl in H6. destruct H6. intros.
          case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + rewrite H21 in H19. exfalso; assumption.
        - rewrite H18 in H6; simpl in H6.
          case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + rewrite H19 in H6. exfalso; assumption. }
      { exists (smtAnd Q' (guardGen (undef e) source (ite e smtTrue smtFalse))).
        simpl in *; intros.
        destruct IHT as [IHT1 [IHT2 IHT3]].
        split; eauto; split.
        - exact (IHT1 F).
        - assert (X': exp_eval E'0 e = Some v).
          + eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
              hnf. intros. eapply (ssa_eval_agree s' _ s'0 E' E'0); eauto.
              rewrite H14. simpl. eapply H8; eauto.
          + assert (X: models F E'0 (ite e smtTrue smtFalse))
            by ( simpl; unfold evalSexp; rewrite X'; rewrite condTrue; econstructor).
            case_eq (undef e); intros; eauto.
            simpl; split; eauto.
            eapply (guard_true_if_eval); eauto.
        - rewrite H14 in IHT2.  cset_tac. hnf in IHT2; simpl in IHT2.  destruct H5.
          +  eapply H10. left; apply IHT2; assumption.
          +  case_eq (undef e); intros; simpl in *.
             * rewrite H6 in H5. simpl in H5. cset_tac. destruct H5 as [ H5 | [[H5 | H5] | H5]]; intuition.
               { eapply (freeVars_undef a) in H5; eauto. eapply H10. hnf in H8. specialize (H8 a H5).
                 rewrite <- (H9 a) in  H8. destruct H8; eauto. }
               { hnf in H8. specialize (H8 a H5). eapply H10; erewrite <- H9 in H8. destruct H8; eauto. }
             * rewrite H6 in H5. simpl in *. cset_tac. destruct H5 as [[H5 | H5] | H5]; intuition.
               hnf in H8. specialize (H8 a H5).  eapply H10; erewrite <- H9 in H8. destruct H8; eauto.
        - intros. destruct H5 as [H5 [H5' H5'']].
          hnf. intros.  eapply (IHT3 F E); eauto.
        }
  + simpl in *; inv H3; inv H4.
    specialize (IHTerminates ant E' E'0 s' s'0).
    destruct pol; simpl in *.
    * specialize (IHTerminates  source P (smtAnd Q (guardGen (undef e) source (ite e (smtFalse) (smtTrue))))).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { specialize (H1 F E). destruct H5. specialize (H1 H5). hnf. intros. eapply H1.
        destruct H13; split; eauto.
        case_eq (undef e); intros; simpl in *.
        - rewrite H18 in H6; simpl in H6. destruct H6. split; eauto. case_eq (val2bool (evalSexp E e)); intros.
          + exfalso. rewrite H20 in H19. assumption.
          + assumption.
        - rewrite H18 in H6. simpl in H6. case_eq (val2bool (evalSexp E e)); intros.
          + rewrite H19 in H6. exfalso; assumption.
          + assumption. }
      { exists (smtAnd Q' (guardGen (undef e) source (ite e smtFalse smtTrue))).
        simpl in *; intros.
        destruct IHT as [IHT1 [IHT2 IHT3]].
        split; eauto; split.
        - exact (IHT1 F).
        - assert (X': exp_eval E'0 e = Some v).
          + eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
              hnf. intros. eapply (ssa_eval_agree s' _ s'0 E' E'0); eauto.
              rewrite H15. simpl. eapply H8; eauto.
          + assert (X: models F E'0 (ite e smtFalse smtTrue))
            by ( simpl; unfold evalSexp; rewrite X'; rewrite condFalse; econstructor).
            case_eq (undef e); intros; eauto.
            simpl; split; eauto.
            eapply (guard_true_if_eval); eauto.
        - rewrite H15 in IHT2.  cset_tac. hnf in IHT2; simpl in IHT2.  destruct H5.
          +  eapply H10. right; apply IHT2; assumption.
          +  case_eq (undef e); intros; simpl in *.
             * rewrite H6 in H5. simpl in H5. cset_tac. destruct H5 as [ H5 | [[H5 | H5] | H5]]; intuition.
               { eapply (freeVars_undef a) in H5; eauto. eapply H10. hnf in H8. specialize (H8 a H5).
                 rewrite <- (H9 a) in  H8. destruct H8; eauto. }
               { hnf in H8. specialize (H8 a H5). eapply H10; erewrite <- H9 in H8. destruct H8; eauto. }
             * rewrite H6 in H5. simpl in *. cset_tac. destruct H5 as [[H5 | H5] | H5]; intuition.
               hnf in H8. specialize (H8 a H5).  eapply H10; erewrite <- H9 in H8. destruct H8; eauto.
        - intros. destruct H5 as [H5 [H5' H5'']].
          hnf. intros.  eapply (IHT3 F E); eauto.
        }
    * specialize (IHTerminates  target P (smtAnd Q (guardGen (undef e) source (ite e smtFalse smtTrue )))).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { specialize (H1 F E). destruct H5. specialize (H1 H5). hnf. intros. eapply H1.
        destruct H13; split; eauto.
        case_eq (undef e); intros; simpl in *.
        - rewrite H18 in H6; simpl in H6. destruct H6. intros.
          case_eq (val2bool (evalSexp E e)); intros.
          + rewrite H21 in H19. exfalso; assumption.
          + assumption.
        - rewrite H18 in H6; simpl in H6.
          case_eq (val2bool (evalSexp E e)); intros.
          + rewrite H19 in H6. exfalso; assumption.
          + assumption. }
      { exists (smtAnd Q' (guardGen (undef e) source (ite e smtFalse smtTrue))).
        simpl in *; intros.
        destruct IHT as [IHT1 [IHT2 IHT3]].
        split; eauto; split.
        - exact (IHT1 F).
        - assert (X': exp_eval E'0 e = Some v).
          + eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
              hnf. intros. eapply (ssa_eval_agree s' _ s'0 E' E'0); eauto.
              rewrite H15. simpl. eapply H8; eauto.
          + assert (X: models F E'0 (ite e smtFalse smtTrue))
            by ( simpl; unfold evalSexp; rewrite X'; rewrite condFalse; econstructor).
            case_eq (undef e); intros; eauto.
            simpl; split; eauto.
            eapply (guard_true_if_eval); eauto.
        - rewrite H15 in IHT2.  cset_tac. hnf in IHT2; simpl in IHT2.  destruct H5.
          +  eapply H10. right; apply IHT2; assumption.
          +  case_eq (undef e); intros; simpl in *.
             * rewrite H6 in H5. simpl in H5. cset_tac. destruct H5 as [ H5 | [[H5 | H5] | H5]]; intuition.
               { eapply (freeVars_undef a) in H5; eauto. eapply H10. hnf in H8. specialize (H8 a H5).
                 rewrite <- (H9 a) in  H8. destruct H8; eauto. }
               { hnf in H8. specialize (H8 a H5). eapply H10; erewrite <- H9 in H8. destruct H8; eauto. }
             * rewrite H6 in H5. simpl in *. cset_tac. destruct H5 as [[H5 | H5] | H5]; intuition.
               hnf in H8. specialize (H8 a H5).  eapply H10; erewrite <- H9 in H8. destruct H8; eauto.
        - intros. destruct H5 as [H5 [H5' H5'']].
          hnf. intros.  eapply (IHT3 F E); eauto.
        }
  + inversion H0.
  + exfalso; inv H4.
  + exfalso; inv H4.
Qed.

Lemma extend_not_models:
forall s Q,
(forall F E, ~ models F E s)
-> (forall F E, models F E Q -> ~ models F E s).

Proof.
intros.
specialize (H F E). assumption.
Qed.

Lemma terminates_impl_star2:
forall L E s L' Es s',
Terminates (L, E ,s ) (L', Es, s')
-> (exists a, star2 F.step (L, E, s) a (L', Es, s'))
   /\ ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtGoto f X)).

Proof.
intros.
general induction H; eauto.
-split.
 + exists nil. econstructor.
 + left. exists e. reflexivity.
- split.
  + exists nil; econstructor.
  + right; exists f ; exists x. reflexivity.
- exploit IHTerminates; try reflexivity.
   destruct X  as [ [a' step ]  H2 ]. split.
  + pose (evts:= filter_tau a a').  exists evts. econstructor; eauto.
  +  destruct H2 as [ [e stmtRet] | [f [ Y stmtGo]] ].
     * left; exists e. rewrite stmtRet. reflexivity.
     * right; exists f, Y; rewrite stmtGo; reflexivity.
Qed.

Lemma noFun_nil s E σ a:
  noFun s
  -> star2 F.step (nil,E,s) a σ
  -> a = nil.

Proof.
  intros; general induction H0; invt noFun; eauto; isabsurd;
  inv H; simpl; exploit IHstar2; try reflexivity; eauto.
Qed.

Lemma star2_noFun_Term:
forall E s Es s',
noFun s
-> Terminates (nil, E, s) (nil, Es, s')
-> star2 F.step  (nil, E, s) nil (nil, Es, s') /\
   ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtGoto f X)).

Proof.
  intros.
  exploit terminates_impl_star2; eauto.
  dcr; exploit noFun_nil; eauto. subst. split; eauto.
Qed.

Definition failed (σ:F.state)  := result (σ ) = None.

Lemma crash_impl_err:
  forall (E:onv val) s Es s' L L',
    Crash (L, E, s) (L', Es, s')
    -> (exists a, star2 F.step (L,E,s) a (L', Es, s'))
       /\ normal2 F.step (L', Es, s') /\ failed (L', Es, s').

Proof.
  intros E s Es s' L L' Crash.
  general induction Crash.
  - split.
    + exists nil; econstructor.
    + split; eauto. hnf. intros. inversion H0.
      isabsurd.
  -  split.
     + exists nil; econstructor.
     + split; eauto.
- destruct sigma'. destruct p. exploit (IHCrash o s0 Es s' l L') ; try reflexivity.
    destruct X as [ [al sstep] X].
    destruct X; split; try split; eauto.
    + destruct a.
      * exists (filter_tau (EvtExtern call) al). econstructor; eauto.
      * exists (filter_tau EvtTau al); econstructor; eauto.
Qed.

Lemma star2_noFun_Crash:
forall E s Es s',
noFun s
-> Crash (nil, E, s) (nil, Es, s')
-> star2 F.step (nil, E, s) nil (nil, Es, s') /\
   (normal2 F.step (nil, Es, s') /\ failed (nil, Es, s')).

Proof.
  intros.
  exploit crash_impl_err; eauto.
  dcr; exploit noFun_nil; eauto. subst. split; eauto.
Qed.

Lemma guardTrue_if_Terminates_ret:
forall E s E' e g,
noFun s
-> undef e = Some g
-> Terminates (nil, E, s)(nil, E', stmtReturn e)
-> forall F, models F E' g.

Proof.
intros. general induction H1.
- eapply (guard_true_if_eval); eauto.
- specialize (IHTerminates E' s' E'0 e g).
  inversion H2.
  + rewrite <- H5 in *. inversion H; subst.
    eapply IHTerminates; eauto.
  + rewrite <- H6 in *; inversion H; subst.
    * eapply IHTerminates; eauto.
    * eapply IHTerminates; eauto.
  + rewrite <- H4 in H0. exfalso; inversion H0.
  + rewrite <- H4 in *.  exfalso. inversion H.
Qed.

Lemma guardTrue_if_Terminates_goto:
forall E s E' f x g,
noFun s
-> undefLift x = Some g
-> Terminates (nil, E, s) (nil, E' , stmtGoto f x)
-> forall F, models F E' g.

Proof.
intros. general induction H1.
- eapply guardList_true_if_eval; eauto.
- specialize (IHTerminates E' s' E'0 f x g).
  inversion H2.
  + rewrite <- H5 in *. inversion H; subst.
    eapply IHTerminates; eauto.
  + rewrite <- H6 in *. inversion H; subst.
    * eapply IHTerminates; eauto.
    * eapply IHTerminates; eauto.
  + rewrite <- H4 in *; inversion H0.
  + rewrite <- H4 in *; inversion H.
Qed.


Lemma predeval_uneq:
forall  E et es e e' P,
exp_eval E et = Some e
-> exp_eval E es = Some e'
-> (forall F, models F E P)
-> (forall (F:lab->vallst->bool),
      models F E P ->
      ~ ((models F E (guardGen (undef et) target (smtNeg (smtReturn et))) /\
    models F E (guardGen (undef es) source (smtReturn es)))))
-> (e = e').

Proof.
intros. decide (e = e').
- assumption.
- specialize (H1 (fun _ => fun x =>toBool (bvEq e' (hd (O::nil) x)))).
  specialize (H2 (fun _ => fun x => toBool (bvEq e' (hd (O::nil) x)))).
  specialize (H2 H1).
  case_eq (undef es); case_eq (undef et); intros.
  + rewrite H3 in H2. rewrite H4 in H2. simpl in H2.
    unfold evalSexp in *.
    rewrite H in H2.  rewrite H0 in H2. exfalso.
    eapply H2.
    pose proof (bvEq_equiv_eq e' e).
     unfold evalSpred.
    split; intros; simpl; try split.
    * simpl in H7. destruct H5. eapply n. rewrite (H5 H7); eauto.
    * eapply guard_true_if_eval; eauto.
    * eapply bvEq_refl.
  + rewrite H3 in H2; rewrite H4 in H2; simpl in H2.
    unfold evalSexp in *.
    rewrite H in H2; rewrite H0 in H2; exfalso.
    eapply H2.
    pose proof (bvEq_equiv_eq e' e).
    unfold evalSpred.
    split; intros; simpl; try split.
    * simpl in H6. destruct H5. specialize (H5 H6). eapply n.
      rewrite H5; eauto.
    * eapply guard_true_if_eval; eauto.
    * eapply bvEq_refl.
  + rewrite H3 in H2; rewrite H4 in H2; simpl in H2.
    unfold evalSexp in *.
    rewrite H in H2. rewrite H0 in H2; exfalso.
    eapply H2.
    pose proof (bvEq_equiv_eq e' e).
    unfold evalSpred.
    split; intros; simpl; try split.
    * simpl  in H7. destruct H5. eapply n. rewrite (H5 H7); eauto.
    * eapply bvEq_refl.
  + rewrite H3 in H2; rewrite H4 in H2; simpl in H2.
    unfold evalSexp in *.
    rewrite H in H2. rewrite H0 in H2; exfalso.
    eapply H2.
    pose proof (bvEq_equiv_eq e' e).
    unfold evalSpred.
    split; intros; simpl; try split.
    * simpl  in H6. destruct H5. eapply n. rewrite (H5 H6); eauto.
    * eapply bvEq_refl.
Qed.

Lemma exp_combineenv_eq_left:
forall e D Es Et v,
Exp.freeVars e ⊆ D
-> exp_eval (combineEnv D Es Et) e= v
-> exp_eval Es e = v.

Proof.
  intros.  eapply (exp_eval_agree (E:=(combineEnv D Es Et))); eauto.
  hnf. cset_tac. unfold combineEnv. hnf in H. specialize (H x H1).
  decide (x ∈ D).
  - reflexivity.
  - exfalso. eapply n; assumption.
Qed.

  Lemma explist_combineenv_eq_left:
forall el D Es Et rl,
list_union (List.map Exp.freeVars el) ⊆ D
-> evalList (combineEnv D Es Et) el = rl
-> evalList Es el = rl.

Proof.
intros.  general induction el.
- simpl. reflexivity.
- simpl. simpl in H. hnf in H. unfold evalSexp.
  rewrite (exp_combineenv_eq_left a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
  + f_equal. eapply IHel; eauto.
    hnf. intros. eapply H. unfold list_union. simpl. eapply list_union_start_swap.
    cset_tac. right; assumption.
  + hnf. intros. eapply H. unfold list_union; simpl.
    eapply list_union_start_swap. cset_tac. left; right; eauto.
Qed.

Lemma combineenv_eq_left:
forall F s D Es Et,
 freeVars s ⊆  D
->(  models F Es s  <-> models F (combineEnv D Es Et) s).

Proof.
intros.  general induction s; simpl; try reflexivity.
- rewrite (IHs1 F D Es Et). rewrite (IHs2 F D Es Et).
  + reflexivity.
  + setSubst H.  right; eauto.
  + setSubst H;  left; eauto.
- rewrite (IHs1 F D Es Et). rewrite (IHs2 F D Es Et).
  + reflexivity.
  + setSubst H; right; eauto.
  + setSubst H; left; eauto.
- rewrite (IHs F D Es Et).
  + reflexivity.
  + simpl in H; eauto.
- unfold evalSexp. case_eq  (exp_eval (combineEnv D Es Et) e); intros.
  + assert (Exp.freeVars e ⊆ D).
    * setSubst H; right; assumption.
    * pose proof (exp_combineenv_eq_left e D Es Et (Some v) H1 H0).
      rewrite H2. destruct (val2bool v).
      { rewrite (IHs1 F D Es Et).
        + reflexivity.
        + setSubst H; left; left; assumption. }
      { rewrite (IHs2 F D Es Et).
        + reflexivity.
        + setSubst H; left; right; assumption. }
  + assert (Exp.freeVars e ⊆ D).
    * setSubst H; right; assumption.
    * pose proof (exp_combineenv_eq_left e D Es Et None H1 H0).
      rewrite H2. unfold default_val. simpl.
      rewrite (IHs2 F D Es Et).
      { reflexivity. }
      { setSubst H; left; right; assumption. }
- rewrite (IHs1 F D Es Et). rewrite (IHs2 F D Es Et).
  + reflexivity.
  + setSubst H. right; assumption.
  + setSubst H. left; assumption.
- unfold evalSexp; case_eq (exp_eval (combineEnv D Es Et) e); intros;
  case_eq (exp_eval (combineEnv D Es Et) e0); intros;
 assert (Exp.freeVars e ⊆ D /\ Exp.freeVars e0 ⊆ D) by (split; setSubst H; eauto).
  + destruct H2;
      pose proof (exp_combineenv_eq_left e D Es Et (Some v) H2 H0);
      pose proof (exp_combineenv_eq_left e0 D Es Et (Some v0) H3 H1);
      rewrite H4; rewrite H5;
      reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq_left e D Es Et (Some v) H2 H0);
    pose proof (exp_combineenv_eq_left e0 D Es Et None H3 H1).
    rewrite H4; rewrite H5; reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq_left e D Es Et None H2 H0);
    pose proof (exp_combineenv_eq_left e0 D Es Et (Some v) H3 H1).
    rewrite H4; rewrite H5; reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq_left e D Es Et None H2 H0);
    pose proof (exp_combineenv_eq_left e0 D Es Et None H3 H1).
    rewrite H4; rewrite H5; reflexivity.
- unfold evalSpred.
  pose proof (explist_combineenv_eq_left a D Es Et (evalList (combineEnv D Es Et) a)).
  rewrite H0; eauto. reflexivity.
- unfold evalSexp.  simpl in H.
  case_eq (exp_eval (combineEnv D Es Et) e); intros.
  + pose proof (exp_combineenv_eq_left e D Es Et (Some v) H H0).
    rewrite H1. reflexivity.
  + pose proof (exp_combineenv_eq_left e D Es Et None H H0).
    rewrite H1. reflexivity.
Qed.

Lemma exp_combineenv_eqr:
forall e D Es Et v,
agree_on eq (Exp.freeVars e ∩ D) Es Et
-> exp_eval (combineEnv D Es Et) e= v
-> exp_eval Et e = v.

Proof.
 intros. eapply (exp_eval_agree (E:=(combineEnv D Es Et))); eauto.
 hnf. cset_tac. unfold combineEnv. destruct if; eauto.
 eapply H. cset_tac; intuition.
Qed.

Lemma explist_combineenv_eqr:
forall el D Es Et vl,
agree_on eq (list_union (List.map Exp.freeVars el) ∩ D) Es Et
-> evalList (combineEnv D Es Et) el = vl
-> evalList Et el = vl.

Proof.
intros. general induction el.
- reflexivity.
- simpl in *; hnf in H. unfold evalSexp.
  rewrite (exp_combineenv_eqr a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
  + f_equal. rewrite (IHel D Es Et (evalList (combineEnv D Es Et) el)); eauto.
    hnf. intros. cset_tac. eapply H. split; eauto.
    unfold list_union. simpl. eapply list_union_start_swap. cset_tac; eauto.
  + hnf; intros; cset_tac. eapply H. split; eauto.
    unfold list_union; simpl. eapply list_union_start_swap; cset_tac; eauto.
Qed.

Lemma combineenv_eq_right:
  forall  F s D Es Et,
    agree_on eq (freeVars s ∩ D) Es Et
    -> (models F Et s <-> models F (combineEnv D Es Et) s).

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
  -  unfold evalSexp.
     case_eq (exp_eval (combineEnv D Es Et) e); intros.
     + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto.
       * specialize (H1 H2 H0). rewrite H1.
         case_eq (val2bool v); intros.
         { rewrite (IHs1 F D Es Et).
           - reflexivity.
           - setSubst2 H. }
         { rewrite (IHs2 F D Es Et).
           - reflexivity.
           - setSubst2 H. }
     + pose proof (exp_combineenv_eqr e D Es Et None).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto.
       * specialize (H1 H2 H0). rewrite H1.
         unfold default_val. simpl.
         rewrite (IHs2 F D Es Et).
         { reflexivity. }
         { setSubst2 H. }
  - rewrite (IHs1 F D Es Et).  rewrite (IHs2 F D Es Et).
    + reflexivity.
    + setSubst2 H.
    + setSubst2 H.
  - unfold evalSexp.
    case_eq (exp_eval (combineEnv D Es Et) e); intros;
    case_eq (exp_eval (combineEnv D Es Et) e0); intros.
    + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
       assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
       * hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto.
       * specialize (H2 H3 H0). rewrite H2.
         pose proof (exp_combineenv_eqr e0 D Es Et (Some v0)).
         assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
       { hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto. }
       { specialize (H4 H5 H1). rewrite H4.
         split; intros; eauto.
       }
    + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * specialize (H2 H3 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { specialize (H4 H5 H1). rewrite H4.
          split; intros; eauto. }
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * specialize (H2 H3 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et (Some v)).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { specialize (H4 H5 H1). rewrite H4.
          split; intros; eauto. }
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * specialize (H2 H3 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { specialize (H4 H5 H1). rewrite H4.
          split; intros; eauto. }
  -unfold evalSpred; simpl. unfold labInc. destruct p.
   pose proof (explist_combineenv_eqr a D Es Et (evalList(combineEnv D Es Et) a)).
   rewrite H0; eauto. reflexivity.
  - unfold evalSpred. unfold evalSexp.
    case_eq (exp_eval (combineEnv D Es Et) e); intros.
    + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * specialize (H1 H2 H0). rewrite H1.
        split; intros; eauto.
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * specialize (H1 H2 H0). rewrite H1.
        split; intros; eauto.
Qed.

Lemma terminates_impl_eval:
forall E s E' e,
Terminates (nil, E, s) (nil, E',stmtReturn  e)
-> exists v, exp_eval E' e = Some v.

Proof.
admit.
Qed.

Lemma unsat_impl_sim:
forall D D' Ds Ds' Dt Dt'  E s t,
(forall F E, ~ models F E (smtCheck s t))
-> getAnn D = (Ds, Ds')
-> getAnn D' = (Dt, Dt')
-> ssa s D
-> ssa t D'
-> Ds' ∩ Dt' = Ds ∩ Dt
-> noFun s
-> noFun t
-> @sim _ statetype_F _ statetype_F  (nil, E, s) (nil, E, t).

Proof.
intros.
unfold smtCheck in H.
pose proof  (noFun_impl_term_crash E s H5).
pose proof  (noFun_impl_term_crash E t H6).
destruct H7 as [ Es  [s' [ sterm| scrash ]]]. destruct H8 as [Et [t' [ tterm | tcrash ]]].
(* s terminiert & t terminiert *)
- pose proof (extend_not_models _ smtTrue H).
  pose proof (unsat_extension D E Es s s' source _ _ H7 ).
  specialize (H8 H2 H5 sterm).
  destruct H8 as [Q [M [ fvQ modS]]].
  assert (smodS: forall F, forall E0:onv val, models F E0 (smtAnd smtTrue Q) ->
       ~  models F E0 (smtAnd (translateStmt t target) (translateStmt s' source) )).
  + intros. eapply (smtand_neg_comm).  apply (modS F E0 H8).
  + clear modS. clear H7.
    pose proof (unsat_extension D' E Et t t' target _ (smtAnd smtTrue Q) smodS)
      as modTS.
    clear smodS. clear H.
    specialize (modTS H3 H6 tterm).
    destruct modTS as [Q' [modQ' [fvQ' modTS]]].
    exploit (star2_noFun_Term  E s Es s' H5 sterm).
    exploit (star2_noFun_Term E t Et t' H6 tterm).
    destruct X as [ sstep X]; destruct X0 as [ tstep  X0].
    destruct X as [ [es sRet] | [fs [Xs sFun]]];
    destruct X0 as [ [et tRet] | [ft [Xt tFun]]].
    * subst. eapply simTerm.
      instantiate (1:=(nil, Et, stmtReturn et)).
      instantiate (1:= (nil, Es, stmtReturn es)).
      { simpl.
        assert (exists evs, exp_eval Es es = Some evs)
          by (eapply terminates_impl_eval; eauto).
        assert (exists evt, exp_eval Et et = Some evt)
          by (eapply terminates_impl_eval; eauto).
        destruct H as [evs evalEs].
        destruct H7 as [evt evalEt].
        rewrite evalEs, evalEt in *.
        f_equal.
        pose (P := smtAnd (smtAnd smtTrue Q) Q').
        pose proof (predeval_uneq (combineEnv Ds' Es Et) et es evt evs P).
        symmetry. eapply H.
        - admit.
        - admit.
        - intros. unfold P. specialize (M F). specialize (modQ' F).
          simpl. split; try split; eauto.
          + rewrite H0 in fvQ. simpl in fvQ.
            erewrite <- combineenv_eq_left; eauto.
          + rewrite H1 in fvQ'. simpl in fvQ'.
            erewrite <- combineenv_eq_right; eauto.
            cut (agree_on eq (Ds' ∩ Dt') Es Et).
            * intros. hnf in H7. hnf. intros. cset_tac. eapply H7. split; eauto.
            * rewrite H4.
              assert (agree_on eq (Ds ∩ Dt) E Es).
              { eapply (agree_on_incl (lv:=Ds)); cset_tac; eauto.
                change (agree_on eq (fst (Ds, Ds')) E Es). rewrite <-H0.
                eapply ssa_eval_agree; eauto. }
              { rewrite <- H7. eapply (agree_on_incl (lv:=Dt)); cset_tac; eauto.
                change (agree_on eq (fst (Dt,Dt')) E Et). rewrite <- H1.
                eapply ssa_eval_agree; eauto. }
        - intros. specialize (modTS F (combineEnv Ds' Es Et) H7);
          eauto. }
      { assumption. }
      { assumption. }
      { unfold normal2.  unfold reducible2. hnf.  intros.
        destruct H as [evt [σ step]].  inversion step. }
      { unfold normal2.  unfold reducible2. hnf.  intros.
        destruct H as [evt [σ step]]. inversion step. }
    * subst. simpl in modTS. exfalso.
       pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc ft 1)))
                                   then (fun (x:vallst) =>  false)
                                   else (fun (x:vallst) => true))).
       pose (E' := combineEnv Ds' Es Et).
       specialize (modTS F E' ).
       eapply modTS.
       { split; try split; eauto.
         - specialize (M F).
           unfold E'.
           pose proof (combineenv_eq_left F Q Ds' Es Et).
           assert (forall v, v ∈ freeVars Q -> v ∈ Ds').
           + intros. hnf in fvQ. rewrite H0 in fvQ. simpl in fvQ. exact (fvQ v H7).
           + specialize (H H7).
           rewrite <- H; eauto.
         - specialize (modQ' F).
           unfold E'.  pose proof (combineenv_eq_right F Q' Ds'  Es Et).
           assert (agree_on eq (freeVars Q' ∩ Ds') Es Et).
           + hnf. intros. cset_tac. hnf in fvQ'. rewrite H1 in fvQ'.
             specialize (fvQ' x); simpl in fvQ'.
             assert (x ∈ Ds' ∩ Dt') by (cset_tac; eauto).
             eapply (ssa_eval_agree) in H2; eauto.
             eapply (ssa_eval_agree) in H3; eauto.
             hnf in H2. hnf in H3. rewrite H0 in H2. rewrite H1 in H3.
             specialize (H2 x); specialize (H3 x). simpl in H2; simpl in H3.
             rewrite H4 in H7. cset_tac.
             rewrite <- H2; eauto.
           + rewrite <- (H H7); eauto. }
       { case_eq (undef es); case_eq (undefLift Xt); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s1).
           + unfold E'. rewrite <- combineenv_eq_left.
             * eapply (guardTrue_if_Terminates_ret _ s); eauto.
             *  hnf; intros. eapply (freeVars_undef a es s1 H7) in H8.
                admit.
           + split.
             *  intros. unfold evalSpred in H10.  unfold F in H10.
                rewrite <- (beq_nat_refl (labN (labInc ft 1))) in H10.
                hnf in H10. assumption.
             * split; eauto. unfold evalSpred. unfold F.
               simpl; destruct ft; simpl; econstructor.
         - assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eq_left.
             * eapply (guardTrue_if_Terminates_ret _ s); eauto.
             * hnf; intros. eapply (freeVars_undef a es s0 H7) in H8.
               admit.
           + split; try split; eauto; intros.
             * unfold evalSpred in H9; unfold F in H9.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H9. hnf in H9.
               assumption.
             * unfold evalSpred; unfold F; simpl; destruct ft; simpl; econstructor.
         - split; try split; eauto; intros.
           + unfold evalSpred in H9; unfold F in H9.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H9. hnf in H9.
               assumption.
           + unfold evalSpred; unfold F; simpl; destruct ft; simpl; econstructor.
         - split; try split; eauto; intros.
           + unfold evalSpred in H8; unfold F in H8.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H8. hnf in H8.
               assumption.
           + unfold evalSpred; unfold F; simpl; destruct ft; simpl; econstructor.
       }
    * subst. simpl in modTS. exfalso.
      pose (F:= (fun (l:lab) => if (beq_nat (labN l) 0)
                                   then (fun (x:vallst) =>  false)
                                   else (fun (x:vallst) => true))).
       pose (E' := combineEnv Ds' Es Et).
       specialize (modTS F E').
       eapply modTS.
       { split; try split; eauto.
         - specialize (M F).
           unfold E'.   rewrite <- (combineenv_eq_left); eauto.
           rewrite H0 in fvQ. simpl in fvQ. assumption.
         - specialize (modQ' F).
           unfold E'.
           unfold E'.  pose proof (combineenv_eq_right F Q' Ds'  Es Et).
           assert (agree_on eq (freeVars Q' ∩ Ds') Es Et).
           + hnf. intros. cset_tac. hnf in fvQ'. rewrite H1 in fvQ'.
             specialize (fvQ' x); simpl in fvQ'.
             assert (x ∈ Ds' ∩ Dt') by (cset_tac; eauto).
             eapply (ssa_eval_agree) in H2; eauto.
             eapply (ssa_eval_agree) in H3; eauto.
             hnf in H2. hnf in H3. rewrite H0 in H2. rewrite H1 in H3.
             specialize (H2 x); specialize (H3 x). simpl in H2; simpl in H3.
             rewrite H4 in H7. cset_tac.
             rewrite <- H2; eauto.
           + rewrite <- (H H7); eauto. }
       { case_eq (undef et); case_eq (undefLift Xs); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eq_left.
             * eapply (guardTrue_if_Terminates_goto _ s); eauto.
             * admit.
           + split.
             *  intros. unfold evalSpred in H10.  unfold F in H10.
                exfalso; assumption.
             * split; eauto. unfold evalSpred. unfold F.
               simpl; destruct fs; simpl; econstructor.
         - assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eq_right.
             *  eapply (guardTrue_if_Terminates_ret _ t); eauto.
             * admit.
           + split; try split; eauto; intros.
             * unfold F; destruct fs; unfold labInc; simpl; eauto.
         - split; try split; eauto; intros.
           + unfold E'.  rewrite <- combineenv_eq_left.
             * eapply (guardTrue_if_Terminates_goto _ s); eauto.
             * admit.
           + unfold F; destruct fs; unfold labInc; simpl; eauto.
         - unfold evalSpred; unfold F; simpl; destruct fs;
           simpl; econstructor; eauto. }
    * subst. simpl in modTS.  decide (fs = ft).
      { admit. (* eapply simTerm.
        instantiate (1:=(nil, Es, stmtGoto fs XS)).
        - instantiate (1:= (nil, Es, stmtGoto fs Xs)). admit.
        - admit.
        - unfold normal2. unfold reducible2. hnf; intros. destruct H as [evt [σ step]]. destruct σ. destruct p.
          inversion step. inversion Ldef.
        - unfold normal2; unfold reducible2; hnf; intros. destruct H as [evt [σ step]]; destruct σ; destruct p.
          inversion step. inversion Ldef.
          }
      { exfalso.
        pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc ft 1)))
                                   then (fun (x:vallst) =>  false)
                                   else (fun (x:vallst) => true))).
       pose (E' := combineEnv Ds Es Et).
       specialize (modTS F E').
       eapply modTS.
       - split; try split; eauto.
         + admit.
         + admit.
       - (* destructen, dann wieder analog *) admit.  *) }
      { admit. }
(* s terminiert & t crasht *)
- pose proof (terminates_impl_models s D E s' Es H2 H5 sterm).
  assert (forall x, x ∈ fst(getAnn D') -> exists v, E x = Some v) by admit.
  pose proof (crash_impl_models D' t E Et t' H3 H8 H6 tcrash).
  specialize (H (fun _ => fun _ => true) (combineEnv Ds' Es Et)).
  exfalso. apply H. simpl. split.
  + erewrite <- combineenv_eq_left; eauto.
    * admit.
  + erewrite <- combineenv_eq_right; eauto.
    * admit.
  (* Widerspruch konstruieren aus guard = False und ~ models
    apply Lemma dass wenn es gibt i was models s und crash t --> models s /\ t
    konstruieren mit sat_extension und Lemma terminates_impl_sim*)
(* s crasht --> sim zu allem!  *)
- pose proof (star2_noFun_Crash E s Es s' H5 scrash ).
  destruct H7; destruct H9. unfold failed in H10. eapply simErr; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)