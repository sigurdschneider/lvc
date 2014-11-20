Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.

Lemma zext_nil_eq_O:
forall k, zext k nil = zext k (O::nil).

Proof.
induction k.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma minus_n_0: forall n, n-0 = n.

Proof.
intros; general induction n; eauto.
Qed.

Lemma not_zero_implies_uneq:
forall a b k, bvZero a = false ->b = zext k (O::nil) ->  val2bool(bvEq a b) -> False.

Proof.
intros. general induction a.
-  destruct a.
   + specialize (IHa (tl (zext k (O::nil))) (k-1)).   simpl in H. specialize (IHa H).  eapply IHa.
     * destruct k; eauto.
       simpl. rewrite zext_nil_eq_O.   erewrite minus_n_0. reflexivity.
     * destruct k; eauto. simpl in H1.  exfalso. assumption.
   +  simpl in H1. destruct k;  assumption.
Qed.

 Lemma guard_true_if_eval:
forall F E e s v,
 exp_eval E e = Some v
->  undef e = Some s
->  models F E s.

Proof.
intros. general induction e; simpl.
- simpl in *. monad_inv H. destruct u.
  + apply (IHe F E s x); eauto.
  + destruct u.
    *  apply (IHe F E s x); eauto.
    * exfalso; discriminate H0.
- simpl in H.  monad_inv H.  simpl in H0. destruct b.
  +  case_eq (undef e1); case_eq (undef e2); intros.
     *  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
        { eapply IHe1; eauto. }
        { eapply IHe2; eauto. }
     * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
     *rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
     * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
  + destruct b.
    *  case_eq (undef e1); case_eq (undef e2); intros.
     {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
        - eapply IHe1; eauto.
        - eapply IHe2; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0. }
    * destruct b.
      { case_eq (undef e1); case_eq (undef e2); intros.
        -  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
           + eapply IHe1; eauto.
           + eapply IHe2; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0. }
      { destruct b.
        -  case_eq (undef e1); case_eq (undef e2); intros.
           +  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
              * eapply IHe1; eauto.
              * eapply IHe2; eauto.
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
            +rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
        - destruct b.
          +  case_eq (undef e1); case_eq (undef e2); intros.
             *  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0. simpl; split.
                { eapply IHe1; eauto. }
                { eapply IHe2; eauto. }
             * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
             *rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
             * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl. exfalso; discriminate H0.
          + destruct b.
            * case_eq (undef e1); case_eq (undef e2); intros.
              {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.  unfold binop_eval in EQ2.  clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ _  k) in H0;  eauto.
                 - split.
                   + eapply IHe1; eauto.
                   + eapply IHe2; eauto.  }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply ( not_zero_implies_uneq _ _ k) in H0; eauto.
                 -  eapply IHe1; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ _ k) in H0; eauto.
                 -  eapply IHe2; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2. simpl.
                   case_eq(bvZero x0).
                   - intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   - intros A.   unfold evalSexp. intros. clear H3. clear EQ2.  hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ _ k) in H0; eauto.    }
                 * case_eq (undef e1); case_eq (undef e2); intros; simpl.
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl; split.
                     - eapply IHe1; eauto.
                     - eapply IHe2; eauto. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl.
                     - eapply IHe1; eauto. rewrite <- H3. assumption. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. simpl.
                     - eapply IHe2; eauto. rewrite <- H3. assumption. }
                   {  rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0. }
      }
Qed.

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
-  inversion H2. exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
   rewrite H18 in X; simpl in *. cset_tac; intuition.  hnf. hnf in X. intros.
    unfold update in X. specialize (X x0).  assert (x0 ∈ D0 ++ {x; {}}) by (cset_tac; left; assumption).
    specialize (X H10). decide (x === x0).
    + rewrite  e0 in H14; exfalso; apply H14; assumption.
    + assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H25 in X; simpl in *. assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H26 in X; simpl in *; assumption.
- inversion H0.
Qed.

Lemma guardList_true_if_eval:
forall F E el s vl,
omap (exp_eval E) el = Some vl
-> undefLift el = Some s
-> models F E s.

Proof.
intros. general induction el.
- simpl in *.  case_eq (undef a); intros.
  + rewrite H1 in H0. simpl in H0.  case_eq (undefLift el); intros; simpl.
    * rewrite H2 in H0. inversion H0. simpl. split.
      { monad_inv H. eapply (guard_true_if_eval); eauto. }
      { monad_inv H. eapply IHel; eauto. }
    * rewrite H2 in H0. inversion H0. monad_inv H. eapply (guard_true_if_eval); eauto.
  + rewrite H1 in H0; monad_inv H. eapply IHel; eauto.
Qed.

Lemma exp_eval_if_list_eval:
  forall el E vl,
    omap (exp_eval E) el = Some vl
    -> forall e, List.In e el -> exists v, exp_eval E e = Some v.

Proof.
intros.
general induction el.
- simpl in H. exists (O::nil). intros. inversion H0.
- unfold omap in H. monad_inv H. decide (e=a).
  + exists x. intros. rewrite e0. assumption.
   + specialize (IHel E x0 EQ1). specialize (IHel e).  simpl in H0.  destruct H0.
     * exfalso. apply n. rewrite H; reflexivity.
     * destruct (IHel H).  exists x1.
       rewrite H0. reflexivity.
Qed.

Lemma models_if_eval :
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

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

Lemma noFun_impl_term_crash :
forall E  s, noFun s
->  exists E'   s', Terminates (nil,E,s) (nil,E',s') \/ Crash (nil,E,s) (nil,E',s').

Proof.
intros.
general induction H.
- admit.
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
admit.
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
            * rewrite H7 in H5. simpl in H; eauto.
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
            * rewrite H7 in H5. simpl in H5. cset_tac. rewrite H12 in H11.  apply H11.
              simpl. cset_tac.  left. apply H9.  destruct H5; eauto.
              { eapply (freeVars_undef _ _ _ H7 H5). }
            * rewrite H7 in H5. simpl in H5. cset_tac. rewrite H12 in H11; apply H11.
              simpl; cset_tac. left; apply H9; eauto.
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

Definition combineEnv D (E1:onv val) E2 :=
fun x => if [x ∈ D] then E1 x else E2 x.

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

Lemma forall_move_and:
forall F s1 s2,
(forall E, models F E (smtAnd s1 s2)) <-> ((forall E, models F E s1) /\ (forall E, models F E s2)).

Proof.
intros. split.
- intros. simpl in *. split.
  + intros; specialize (H E). destruct H; assumption.
  + intros; specialize (H E); destruct H; assumption.
- intros. simpl. destruct H. econstructor.
  + exact (H E).
  + exact (H0 E).
Qed.

Lemma agree_on_impl_models:
forall F E s E',
agree_on eq (freeVars s) E E'
-> ((models F E s) <-> (models F E' s)).

Proof.
admit.
Qed.

Lemma crash_impl_sim:
forall (E:onv val) s Es s' E t,
Crash (nil, E, s) (nil, Es, s')
-> @sim _ statetype_F _ statetype_F (nil, E, s) (nil, E, t).

Proof.
intros E s Es s' E' t crash.
general induction crash.
- eapply simErr.
  + instantiate (1:=(nil,E',s0)). assumption.
  + econstructor.
  + hnf. intros. inversion H1.  inversion H0.  admit.
- destruct sigma'. destruct p. inversion crash.
  + admit.
  + admit.
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
forall  l e e',
(forall (F:lab->vallst->bool), (~(~ ((F l (e::nil)) = ( F l (e'::nil)))))) -> (e = e').

Proof.
intros. hnf in H.
decide (e = e').
- assumption.
- specialize (H (fun _ => fun x => toBool (bvEq e (hd (O::nil) x)))).
 exfalso. eapply H. hnf. intros. eapply n. eapply bvEq_equiv_eq. simpl in H0.
 rewrite <- H0. eapply bvEq_refl.
Qed.

Lemma combineenv_eq_subset:
forall s D F E E',
 freeVars s ⊆ D
->(  models F E s  <-> models F (combineEnv D E E') s).

Proof.
intros.  admit. (* general induction s.
- rewrite forall_move_and.  rewrite (IHs1 D ).  rewrite (IHs2 D).
  + instantiate (1:=E'). instantiate (1:=E'). split; intros.
    * destruct H0. simpl.  specialize (H0 E); specialize (H1 E). econstructor; eauto.
    *  split;  intros; specialize (H0 E); destruct H0; eauto.
  + cset_tac. hnf in H. apply (H a); cset_tac. simpl. cset_tac. right; assumption.
  + cset_tac. hnf in H. apply (H a); cset_tac. simpl; cset_tac. left; assumption.
- simpl in *. split; intros.
  + specialize (H0 E).  destruct H0.
    * (* rewrite (IHs1 D) in H0.  rewrite (IHs2 D). *) admit.
    * admit.
  + admit. (*instantiate (1:=E'). instantiate (1:=E'). intuition.*)
- simpl in *. admit. (*rewrite (IHs D). instantiate (1:=E'). split; intros; eauto.*)
- admit.
- admit.
- admit.
- admit.
- admit.
- simpl; intuition.
- simpl; intuition.*)
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
- pose proof (extend_not_models _ (constr (Con (O::nil)) (Con (O::nil))) H) .
  pose proof (unsat_extension D E Es s s' source _ _ H7 ).
  specialize (H8 H2 H5 sterm).
  destruct H8 as [Q [M [ fvQ modS]]].
  assert (smodS: forall F, forall E0:onv val, models F E0 (smtAnd (constr (Con (O :: nil)) (Con (O :: nil))) Q) ->
       ~  models F E0 (smtAnd (translateStmt t target) (translateStmt s' source) )).
  + intros. eapply (smtand_neg_comm).  apply (modS F E0 H8).
  + clear modS. clear H7.
    pose proof (unsat_extension D' E Et t t' target _ (smtAnd (constr (Con (O::nil)) (Con (O::nil))) Q) smodS)
      as modTS.
    clear smodS. clear H.
    specialize (modTS H3 H6 tterm).
    destruct modTS as [Q' [modQ' [fvQ' modTS]]].
    exploit (terminates_impl_star2 nil E s nil Es s' sterm).
    exploit (terminates_impl_star2 nil E t nil Et t' tterm).
    destruct X as [ [a sstep]  X]; destruct X0 as [ [b tstep]  X0].
    destruct X as [ [es sRet] | [fs [Xs sFun]]]; destruct X0 as [ [et tRet] | [ft [Xt tFun]]].
    * subst. eapply simTerm; eauto.
      { instantiate (1:= (nil, Es, stmtReturn es)); admit. }
      { admit. }
      { unfold normal2.  unfold reducible2. hnf.  intros.  destruct H as [evt [σ step]].  inversion step.
      }
      { unfold normal2.  unfold reducible2. hnf.  intros. destruct H as [evt [σ step]]. inversion step. }
    *  subst. simpl in modTS. exfalso.
       pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc ft 1)))
                                   then (fun (x:vallst) =>  false)
                                   else (fun (x:vallst) => true))).
       pose (E' := combineEnv Ds' Es Et).
       specialize (modTS F E' ).
       eapply modTS.
       { split; try split; eauto.
         - specialize (M F).
           unfold E'.   rewrite <- (combineenv_eq_subset); eauto.
           rewrite H0 in fvQ. simpl in fvQ. assumption.
         - specialize (modQ' F).
           unfold E'. admit.
       }
       { case_eq (undef es); case_eq (undefLift Xt); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s1).
           + eapply (guardTrue_if_Terminates_ret _ s); eauto.
             instantiate (1:= E).
             (* analoges rewrite Lemma *)
             admit.
           + split.
             *  intros. unfold evalSpred in H10.  unfold F in H10.
                rewrite <- (beq_nat_refl (labN (labInc ft 1))) in H10.
                hnf in H10. assumption.
             * split; eauto. unfold evalSpred. unfold F. simpl; destruct ft; simpl; econstructor.
         - assert (models F E' s0).
           +  eapply (guardTrue_if_Terminates_ret _ s); eauto.
             instantiate (1:= E).
             (* analoges rewrite Lemma *)
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
           unfold E'.   rewrite <- (combineenv_eq_subset); eauto.
           rewrite H0 in fvQ. simpl in fvQ. assumption.
         - specialize (modQ' F).
           unfold E'. admit.
       }
       { (* destructen und analog *) admit. }
    * subst. simpl in modTS.  decide (fs = ft).
      { eapply simTerm; eauto.
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
       - (* destructen, dann wieder analog *) admit. }
(* s terminiert & t crasht *)
-  admit.
(* s crasht --> sim zu allem! *)
- eapply crash_impl_sim; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)


(*
Lemma combineenv_eq_subset_exp:
forall e D E v,
Exp.freeVars e ⊆ D
-> forall E', (evalSexp E e = v <-> evalSexp (combineEnv D E E') e = v).

Proof.
intros. general induction e.
- split; intros; unfold evalSexp in *; simpl in *; assumption.
- split; intros; unfold evalSexp in *.
  + hnf in H. simpl in H. specialize (H v). unfold combineEnv.  simpl. decide (v ∈ D).
    * simpl in H0. destruct (E v); eauto.
    * exfalso. eapply n. eapply H. cset_tac. reflexivity.
  + hnf in H; simpl in H. specialize (H v). unfold combineEnv in H0. simpl in *. decide (v ∈ D).
    * destruct (E v); eauto.
    * exfalso. eapply n. eapply H. cset_tac; reflexivity.
- simpl in *. split; intros.
  + (* specialize (IHe D E). unfold evalSexp in H0. simpl in *.
    case_eq (exp_eval E e); intros.
    * unfold evalSexp at 1 in IHe.  specialize (IHe v0 H E').  destruct IHe. unfold evalSexp in *.
      unfold exp_eval. rewrite H1 in H2. eapply H2.   simpl in H0.  exploit IHe; eauto. *)
    admit.
  + admit.
- admit.
Qed.

Lemma combineenv_eq_subset_move:
forall F s D E',
freeVars s ⊆ D
-> ((forall E, models F E s)  <-> (forall E, models F (combineEnv D E E') s))
-> (forall E, ((models F E s) <-> (models F (combineEnv D E E') s))).

Proof.
intros; admit.
Qed.
*)