Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim.
Require Import sexp smt nofun Terminates bitvec Crash freeVars.

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
  general induction H1; invt ssa; try invt F.step; simpl.
  - reflexivity.
-  inversion H2. exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H6 in X; simpl in *. cset_tac; intuition.  hnf. hnf in X. intros.
    unfold update in X. specialize (X x0).  assert (x0 ∈ D0 ++ {x; {}}) by (cset_tac; left; assumption).
    specialize (X H9). decide (x === x0).
    + rewrite <- e0 in H7; exfalso; apply H3; assumption.
    + assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H8 in X; simpl in *. assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H9 in X; simpl in *; assumption.
- inversion H.  inversion Ldef0.
- inversion H2.
- inversion H2.
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
- inv H; invt ssa; invt noFun; simpl in * |- *.
  + case_eq(undef e); intros; simpl; split; eauto.
    * eapply (guard_true_if_eval _ E' e s v ); eauto.
      eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E E').
      { eapply (ssa_eval_agree  (stmtExp x e b) _ s'); eauto.
        econstructor; eauto. }
      { eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
    * split; eauto.
      assert (X1: exp_eval E' (Var x) = Some v).
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

Lemma unsat_extension:
forall D F E E' s s' pol P Q,
(forall E, models F E Q -> ~ models F E (smtAnd (translateStmt s pol) P))
-> ssa s D
->Terminates (nil, E, s) (nil, E', s')
-> exists Q', models F E'  Q' /\
              freeVars Q' ⊆  fst(getAnn D) /\
              (forall E, models F E (smtAnd Q Q') -> ~ models F E (smtAnd (translateStmt s' pol) P)).

Proof.
intros.
Admitted.

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
forall F  s Q,
(forall E, ~ models F E s)
-> (forall E, models F E Q -> ~ models F E s).

Proof.
intros.
specialize (H E). assumption.
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
forall F E s E' D,
freeVars s ⊆ D
-> agree_on eq (freeVars s) E E'
-> ((models F E s) <-> (models F (combineEnv D E E') s)).

Proof.
intros. general induction s.
- simpl in *.  split; intros.
  +  destruct H1; split.
     * rewrite <- IHs1; eauto.
       { cset_tac; intuition. }
       { hnf. hnf in H0. intros. eapply H0. cset_tac. left; assumption. }
     * rewrite <- IHs2; eauto.
       { cset_tac; intuition. }
       { hnf. hnf in H0. intros. eapply H0; cset_tac; right; assumption. }
  + destruct H1; split.
    * rewrite <- IHs1 in H1; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros. eapply H0. cset_tac; left; assumption. }
    * rewrite <- IHs2 in H2; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros; eapply H0. cset_tac; right; assumption. }
- simpl in *; split; intros.
  + destruct H1.
    * left; rewrite IHs1 in H1; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros; eapply H0. cset_tac; left; assumption. }
    * right; rewrite IHs2 in H1; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros; eapply H0. cset_tac; right; assumption. }
  + destruct H1.
    * left; rewrite <- IHs1 in H1; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros; eapply H0. cset_tac; left; assumption. }
    * right; rewrite <- IHs2 in H1; eauto.
      { cset_tac; intuition. }
      { hnf; hnf in H0; intros; eapply H0. cset_tac; right; assumption. }
- simpl in *; split; intros.
  + rewrite <- IHs in H2; eauto.
  + rewrite IHs in H2; eauto.
-


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
  + specilaize (H0 E)  rewrite (IHs1 D). rewrite (IHs2 D).
  instantiate (1:=E'). instantiate (1:=E'). intuition.
  + cset_tac.  hnf in H. apply (H a). cset_tac. right; assumption.
  + cset_tac. hnf in H. apply (H a); cset_tac; left; assumption.
- simpl in *. rewrite (IHs D). instantiate (1:=E'). split; intros; eauto.
  + assumption.
- simpl in *.  case_eq (evalSexp E e); intros.
  + simpl.  rewrite (IHs2 D). instantiate (1 := E').  admit.
    * cset_tac; hnf in H; apply (H a). cset_tac. left; right; assumption.
  + admit.
- simpl in *.  rewrite (IHs1 D).  rewrite (IHs2 D).
  instantiate (1:=E'). instantiate (1:=E'). intuition; eauto.
  + cset_tac; hnf in H; apply (H a). cset_tac. right; assumption.
  + cset_tac; hnf in H; apply (H a). cset_tac. left; assumption.
- simpl in *. case_eq (evalSexp E e); case_eq (evalSexp E e0); intros; simpl; eauto.
  + admit.
  + admit.
  + admit.
  + admit.
- admit.
- simpl. admit.
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
  +

Lemma unsat_impl_sim:
forall D D' Ds Ds' Dt Dt' F E s t,
(forall E, ~ models F E (smtCheck s t))
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
- pose proof (extend_not_models _ _ (constr (Con (O::nil)) (Con (O::nil))) H) .
  pose proof (unsat_extension D _ E Es _ s' source _ _ H5 ).
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
       { simpl in H3.  instantiate (1:=(nil, Es, stmtReturn es)). instantiate (1:=(nil, Et, stmtReturn et)).
         simpl. case_eq (undef es); case_eq (undef et); intros; simpl.
         - simpl in H9. rewrite H5 in H9; rewrite H6 in H9; simpl in H9. unfold evalSexp in H9.
           assert ( X: (True /\ models F (combineEnv Ds Es Et) Q) /\ models F (combineEnv Ds Es Et) Q').
           +  split; try split; try eauto.
              * rewrite <- combineenv_eq_subset; eauto. rewrite H0 in H. simpl in H; eauto.
              * (*Beweis konstruieren: models F Et Q', weil freeVars Q' not in Ds *) admit.
           + specialize (H9 X). clear X.
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
