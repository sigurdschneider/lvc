Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim.
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
- inversion H.
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
  + inversion H0. case_eq(undef e); intros; simpl; split; eauto.
    * eapply (guard_true_if_eval _ E'0 e s0 v ); eauto.
      eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
      { eapply (ssa_eval_agree  (stmtExp x e s) _ s'0); eauto.
        econstructor; eauto. }
      { eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
    * split; eauto; subst.
      assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0[x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))).
          + subst.  eapply (ssa_eval_agree s' _ s'0 _ E'0); eauto.
          + rewrite H12. unfold fst. cset_tac. right; rewrite H5; reflexivity.
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
    * assert (X1: exp_eval E' (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E[x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))).
          + eapply (ssa_eval_agree b _ s'); eauto.
          + rewrite H10. unfold fst. cset_tac. right; rewrite H5; reflexivity.
        - unfold exp_eval. unfold update. decide (x===x).
          + reflexivity.
          + exfalso.  apply n; reflexivity. }
      assert (X2: exp_eval E' e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E E').
        - eapply (ssa_eval_agree  (stmtExp x e b) _ s'); eauto.
        econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold evalSexp. rewrite X1; rewrite X2.
         eapply  bvEq_equiv_eq. reflexivity.  }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by (hnf; intros; hnf in H6; specialize (H6 a); exact (H6 H3)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E E') by ( eapply (ssa_eval_agree (stmtIf e b1 b2) _ s'); eauto; econstructor; eauto).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condTrue.
      rewrite <- H7 in *.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e _ v); eauto.
          + assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
                   by (hnf; intros; hnf in H6; specialize (H6 a); hnf; cset_tac; simpl;  exact (H6 H4)).
            assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E E')
              by ( eapply (ssa_eval_agree (stmtIf e b1 b2) _ s'); eauto; econstructor; eauto).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.
            eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by (hnf; intros; hnf in H6; specialize (H6 a); exact (H6 H3)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E E') by ( eapply (ssa_eval_agree (stmtIf e b1 b2) _ s'); eauto; econstructor; eauto).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condFalse.
      rewrite <- H7 in *.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e _ v); eauto.
          + assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
                   by (hnf; intros; hnf in H6; specialize (H6 a); hnf; cset_tac; simpl;  exact (H6 H4)).
            assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E E')
              by ( eapply (ssa_eval_agree (stmtIf e b1 b2) _ s'); eauto; econstructor; eauto).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.
            eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + assert (X: models (fun (_:pred) (_:vallst) => true) E' (funcApp l Y)) by isTrue.
   case_eq(undefLift Y); intros; simpl; eauto.
   split; eauto.
   eapply (guardList_true_if_eval _ E' Y s vl); eauto.
   eapply (omap_exp_eval_agree (E:= E) (E':=E')); eauto.
   eapply (agree_on_incl (lv:=D0)); eauto.
   change (agree_on eq (fst (getAnn (ann0 (D0, D')))) E E').
   eapply (ssa_eval_agree (stmtGoto l Y) (ann0 (D0, D')) (s')); eauto.
   econstructor; eauto.
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
- simpl in *. destruct sigma' . destruct p.  inv H.
  + simpl in *. inv H1.
    specialize (IHTerminates an (E[x <- Some v]) (E') s0 s').
    inv H3. destruct pol; simpl in *.
    * specialize (IHTerminates source P (smtAnd Q (guardGen (undef e) source (constr (Var x) e)))).
      destruct IHTerminates as [Q' IHT]; intros; eauto; simpl in *.
      { specialize (H0 F E0). destruct H4 as [H4 H4']. specialize (H0 H4).  hnf in H0; hnf; intros.
        eapply H0. destruct H6. split; simpl; eauto. destruct (undef e); simpl in *; eauto. destruct H4'.
        split; eauto. }
      { exists (smtAnd Q' (guardGen (undef e) source (constr (Var x) e))).
        simpl in *. intros.
        destruct IHT as [IHT1 [ IHT2 IHT3 ]].
        split; eauto; split.
        - exact (IHT1 F).
        -  assert (models F E' (constr (Var x) e)).
           + simpl. unfold evalSexp.
              assert (exp_eval E' (Var x) = Some v).
             * eapply (exp_eval_agree (E:= E[x <- Some v])).
               { simpl. hnf. intros. inv H3. eapply (ssa_eval_agree s0); eauto. rewrite H11.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E' e = Some v).
              { eapply (exp_eval_agree (E:=E)); eauto; hnf; intros; eapply (ssa_eval_agree); eauto.
                econstructor; eauto. }
              rewrite H4; rewrite H6; simpl.  eapply bvEq_equiv_eq. reflexivity.
           + case_eq (undef e); intros; simpl.
             * split; eauto.
               eapply (guard_true_if_eval _ _ e); eauto.
               eapply (exp_eval_agree (E:=E)); eauto. hnf; intros. eapply (ssa_eval_agree); eauto.
               econstructor; eauto.
             * simpl in H4. assumption.
        - hnf. intros. hnf in H8. specialize (H8 a).  eapply ssa_incl in H1. hnf in H1. specialize (H1 a).
          simpl in H1. hnf in IHT2. specialize (IHT2 a). cset_tac. destruct H4.
          +  rewrite H11 in IHT2. exact (IHT2 H4).
          + apply H1.  eapply H8. case_eq (undef e); intros.
            * rewrite H6 in H4. simpl in H4. cset_tac. destruct H4; eauto.
              { eapply (freeVars_undef _ _ _ H6 H4). }
            * rewrite H6 in H4. simpl in H; eauto.
        - intros. eapply IHT3. destruct H4 as [H4 [H4' H4'']]; split; eauto; split; eauto.
      }
    * specialize (IHTerminates target P (smtAnd Q (guardGen (undef e) target (constr (Var x) e)))).
      destruct IHTerminates as [Q' IHT]; intros; eauto; simpl in *.
      { specialize (H0 F E0). destruct H4 as [H4 H4']. specialize (H0 H4).  hnf in H0; hnf; intros.
        eapply H0. destruct H6. split; simpl; eauto. destruct (undef e); simpl in *; eauto. }
      { exists (smtAnd Q' (guardGen (undef e) target (constr (Var x) e))).
        simpl in *. intros.
        destruct IHT as [IHT1 [ IHT2 IHT3 ]].
        split; eauto; split.
        - exact (IHT1 F).
        -  assert (models F E' (constr (Var x) e)).
           + simpl. unfold evalSexp.
              assert (exp_eval E' (Var x) = Some v).
             * eapply (exp_eval_agree (E:= E[x <- Some v])).
               { simpl. hnf. intros. inv H3. eapply (ssa_eval_agree s0); eauto. rewrite H11.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E' e = Some v).
              { eapply (exp_eval_agree (E:=E)); eauto; hnf; intros; eapply (ssa_eval_agree); eauto.
                econstructor; eauto. }
              rewrite H4; rewrite H6; simpl.  eapply bvEq_equiv_eq. reflexivity.
           + case_eq (undef e); intros; simpl.
             * intros; eauto.
             * simpl in H4. assumption.
        - hnf. intros. hnf in H8. specialize (H8 a).  eapply ssa_incl in H1. hnf in H1. specialize (H1 a).
          simpl in H1. hnf in IHT2. specialize (IHT2 a). cset_tac. destruct H4.
          +  rewrite H11 in IHT2. exact (IHT2 H4).
          + apply H1.  eapply H8. case_eq (undef e); intros.
            * rewrite H6 in H4. simpl in H4. cset_tac. destruct H4; eauto.
              { eapply (freeVars_undef _ _ _ H6 H4). }
            * rewrite H6 in H4. simpl in H; eauto.
        - intros. eapply IHT3. destruct H4 as [H4 [H4' H4'']]; split; eauto; split; eauto.
      }
  + simpl in *; inv H1. inv H3.
    specialize (IHTerminates ans o E' s0 s').
    destruct pol; simpl in *.
    * specialize (IHTerminates  source P (smtAnd Q (guardGen (undef e) source (ite e (smtTrue) (smtFalse))))).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { specialize (H0 F E). destruct H4. specialize (H0 H4). hnf. intros. eapply H0.
        destruct H12. split; eauto.
        case_eq (undef e); intros; simpl in *.
        - rewrite H17 in H5. simpl in H5. destruct H5. split; eauto. case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + exfalso. rewrite H19 in H18. assumption.
        - rewrite H17 in H5. simpl in H5. case_eq (val2bool (evalSexp E e)); intros.
          + assumption.
          + rewrite H18 in H5. exfalso; assumption.
      }
      { exists (smtAnd Q' (guardGen (undef e) source (ite e smtTrue smtFalse))).
        simpl in *; intros.
        destruct IHT as [IHT1 [IHT2 IHT3]].
        split; eauto; split.
        - exact (IHT1 F).
        - case_eq (undef e); intros.
          + simpl. (* Obvious construction needed *) admit.
          + (* same as before *) admit.
        - rewrite H13 in IHT2.  cset_tac. hnf in IHT2. simpl in IHT2.  destruct H4.
          +  eapply H9. left; apply IHT2; assumption.
          +  case_eq (undef e); intros; simpl in *.
             * rewrite H5 in H4. simpl in H4. cset_tac. destruct H4 as [ H4 | [[H4 | H4] | H4]]; intuition.
               { eapply (freeVars_undef a) in H5; eauto. eapply H9. hnf in H7. specialize (H7 a H5).
                 rewrite <- (H8 a) in  H7. destruct H7; eauto. }
               { hnf in H7. specialize (H7 a H4). eapply H9; erewrite <- H8 in H7. destruct H7; eauto. }
             * rewrite H5 in H4. simpl in *. cset_tac. destruct H4 as [[H4 | H4] | H4]; intuition.
               hnf in H7. specialize (H7 a H4).  eapply H9; erewrite <- H8 in H7. destruct H7; eauto.
        - intros. destruct H4 as [H4 [H4' H4'']].
          hnf. intros.  eapply (IHT3 F E); eauto.
        }
    * (* analog *) admit.
  + (* analog zu vorherigem If *) admit.
  + simpl in *. inv H1. destruct pol; simpl in *.
    * specialize (IHTerminates (ann0 (D0, D')) E E' (stmtGoto l0 Y) s' source P Q).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { admit. (*TODO:???*) }
    * specialize (IHTerminates (ann0 (D0, D')) E E' (stmtGoto l0 Y) s' target P Q).
      destruct IHTerminates as [Q' IHT]; intros; eauto.
      { admit. (* TODO *) }
  + exfalso. inv H3.
  + exfalso; inv H3.
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
-  destruct sigma'; destruct p; exploit IHTerminates; try reflexivity.
   destruct X  as [ [a' step ]  H1 ]. split.
  + pose (evts:= filter_tau a a').  exists evts. econstructor; eauto.
  +  destruct H1 as [ [e stmtRet] | [f [ Y stmtGo]] ].
     * left; exists e. rewrite stmtRet. reflexivity.
     * right; exists f, Y; rewrite stmtGo; reflexivity.
Qed.

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

Lemma combineenv_eq_subset:
forall s D F E',
 freeVars s ⊆ D
->(  (forall E, models F E s)  <-> (forall E,  models F (combineEnv D E E') s)).

Proof.
intros.  general induction s.
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
- simpl; intuition.
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

Lemma combineenv_eq_subset_move:
forall F s D E',
freeVars s ⊆ D
-> ((forall E, models F E s)  <-> (forall E, models F (combineEnv D E E') s))
-> (forall E, ((models F E s) <-> (models F (combineEnv D E E') s))).

Proof.
intros; admit.
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
eapply (noFun_impl_term_crash E s) in H5.
eapply (noFun_impl_term_crash E t) in H6.
destruct H5 as [ Es  [s' [ sterm| scrash ]]]. destruct H6 as [Et [t' [ tterm | tcrash ]]].
- pose proof (extend_not_models _ (constr (Con (O::nil)) (Con (O::nil))) H) .
assert (X: forall P, (forall (A:pred->vallst->bool) (B:onv val), P A B <-> forall B A, P A B)) by admit.
  pose proof (unsat_extension D F E Es _ s' source _ _ H5 ).
  specialize (H6 H2 sterm).
  destruct H6 as [Q [M H6]].
  assert (H7: forall E0:onv val, models F E0 (smtAnd (constr (Con (O :: nil)) (Con (O :: nil))) Q) ->
       ~  models F E0 (smtAnd (translateStmt t target) (translateStmt s' source) )).
  + intros. eapply (smtand_neg_comm). destruct H6. apply (H8 E0 H7).
  +  pose proof (unsat_extension D' _ E Et _ t' target _ (smtAnd (constr (Con (O::nil)) (Con (O::nil))) Q) H7).
     specialize (H8 H3 tterm).
     destruct H8 as [Q' [M2 H8]].
     destruct H8.
     specialize (H9 (combineEnv Ds Es Et)).
     exploit (terminates_impl_star2 nil E s nil Es s' sterm).
     exploit (terminates_impl_star2 nil E t nil Et t' tterm).
     clear H. clear H5. destruct H6. clear H5.
     destruct X as [ [a sstep]  X]; destruct X0 as [ [b tstep]  X0].
     destruct X as [ [es sRet] | [fs [Xs sFun]]]; destruct X0 as [ [et tRet] | [ft [Xt tFun]]].
     * subst. eapply simTerm.
       {  instantiate (1:=(nil, Es, stmtReturn es)). instantiate (1:=(nil, Et, stmtReturn et)).
         simpl. case_eq (undef es); case_eq (undef et); intros; simpl.
         - simpl in H9. rewrite H5 in H9; rewrite H6 in H9; simpl in H9. unfold evalSexp in H9.
           assert ( X: (True /\ models F (combineEnv Ds Es Et) Q) /\ models F (combineEnv Ds Es Et) Q').
           +  split; try split; try eauto.
              *  rewrite agree_on_impl_models; eauto. admit.
              * rewrite agree_on_impl_models; eauto. admit.
           + specialize (H9 X). clear X. hnf in H9.
             (* Nun aus H9 konstruieren, dass die Werte gleich sein müssen, mit Lemma? *)
             admit.
           - (* analog zu Fall davor, ohne guard *) admit.
           - admit.
           - admit. }
       { (* Dieser Fall scheint kaputt zu sein! *) admit. }
       { (* Dito *) admit. }
       { simpl. hnf. intros. inversion H5. inversion H6. inversion H10. }
       { simpl; hnf; intros. inversion H5; inversion H6. inversion H10. }
     * admit.
     * admit.
     * admit.
- (* target crasht --> nicht semantisch äquivalent --> muss E geben. *)
  admit.
-

 general induction scrash.
  +  eapply simErr; eauto.
     * econstructor.
     * hnf. admit. (* TODO: normal2 konstruieren *)
  +

(* source crasht --> egal was Ergebnis is, weil env immer! unsat sein wird, da zwei widersprücliche Constraints enthalten sind *)
  (* Induktion Crash *)
  (* beweis Crahs -> star 2 step + result = None  dann simErr Constr.*)
  admit.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
