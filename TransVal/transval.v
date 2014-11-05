Require Import List.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim.
Require Import sexp smt nofun Terminates bitvec Crash.

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
    rewrite H6 in X; simpl in *.
    admit.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H8 in X; simpl in *. assumption.
- inversion H2; exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
  rewrite H9 in X; simpl in *; assumption.
- admit.
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

Lemma in_if_get:
forall XL n  (x:exp),
get XL n x
-> List.In x XL.

Proof. intros.
general induction H.
- simpl. left; eauto.
- simpl. right. eapply IHget. reflexivity.
Qed.

Fixpoint freeVarsList el :=
match el with
| nil => ∅
| e::el' => freeVars e ∪ freeVarsList el'
end.

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
 + admit.
(*
+ case_eq (undefLift Y); intros; simpl; eauto.
    *  split; eauto.  eapply (guardList_true_if_eval); eauto.
       assert ( list_union (List.map freeVars  Y)  ⊆ fst (getAnn D)) by ( rewrite <- H7 in H0; inversion H0; simpl; assumption).
       assert (agree_on eq (list_union (List.map freeVars Y)) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
       erewrite omap_agree; eauto.
       intros. 
       destruct Y. 
       { inversion H12. }
       { assert (X: exists v, (exp_eval E x) = Some v).
         - eapply exp_eval_if_list_eval; eauto. eapply in_if_get; eauto. 
         - destruct X.  rewrite H13.
         assert (freeVars x ⊆ fst (getAnn D)).
           +  cset_tac. hnf in H10. specialize (H10 a). eapply H10.  unfold list_union.  simpl.  eapply list_union_start_swap.  cset_tac. left; right; assumption. 
         - assert (agree_on eq (freeVars x) E E'). 
           + cset_tac. hnf.  hnf in H11.  intros. eapply (H11 x2). unfold list_union. simpl. eapply list_union_start_swap. cset_tac.  left;right; assumption.
           + eapply exp_eval_agree; eauto. }
*)
Qed.

(*
  +  assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
      assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4))).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condFalse.
      rewrite <- H7 in *.
      inversion H0; inversion H3.
      eapply IHterminates; eauto.
      admit.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.  }
(* exploit IHTerminates; [ | |reflexivity | reflexivity |   ]; eauto.
    exploit ssa_eval_agree; try eapply H1; eauto.
    case_eq (undef e); intros; simpl; split; eauto.
    * eapply guard_true_if_eval; eauto.
      eapply (exp_eval_agree (E:=E) (E':=E') _ (v:=Some v) ).
      { eapply (agree_on_incl (lv:= fst(getAnn an)) ); eauto. 
        eapply ssa_eval_agree; eauto.
        - eapply agree_on_incl; eauto.
      rewrite H10. simpl. rewrite H7. cset_tac; intuition.
      (* E [x <- Some v] and E agree on freeVars e *) exfalso; admit.
    * split.
      unfold evalSexp.
      erewrite exp_eval_agree; eauto.
      instantiate (1:=E[x <- Some v]).
      setoid_rewrite exp_eval_agree at 2.
      Focus 2. instantiate (1:=E[x <- Some v]). admit.
      Focus 2. instantiate (1:=exp_eval E e). admit.
      simpl. lud. rewrite def. eapply bvEq_equiv_eq; reflexivity.
      isabsurd. admit.
      eauto.
   * admit. *)
(*  + assert (X: models (fun (_:pred) (_:vallst) => true) E' (smtAnd (constr (Var x) e) (translateStmt b source))).
    * split; simpl.
      {  unfold evalSexp.
         assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
         assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x0); specialize (H9 x0); exact (H1 (H9 H4))).
         eapply (exp_eval_agree (E:=E) (E' := E')) in def; eauto.
         - rewrite def. rewrite <- H7 in *. clear H7. rewrite <- H8 in *. clear H8.  simpl.
           assert (X1:E' x = Some v).
           + admit.
(*           eapply (agree_on_update_dead (R:=eq) (lv:=freeVars e) (E:=E) (E':=E')(x:=x) (Some v))in H10; eauto.

           assert ( X1: exp_eval E'  (Var x) = Some v).
           + eapply (exp_eval_agree (E:=E[x <-Some v]) (E':=E')).
             * eapply agree_on_update_dead. hnf.  cset_tac. simpl in H11.
             * simpl. unfold update. decide (x === x).
               { reflexivity. }
               { exfalso; apply n; reflexivity. } *)
           + rewrite X1.  unfold val2bool. eapply bvEq_equiv_eq. reflexivity. }
      { rewrite <- H7 in *. inversion H0.  inversion H3. eapply IHterminates; eauto.
        - hnf. cset_tac. admit. }
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x0); specialize (H10 x0); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.
          } *)
  + assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption). 
      assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4))).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condTrue.
      rewrite <- H7 in *.
      inversion H0; inversion H3.
      eapply IHterminates; eauto.
      admit.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.  }
  +  assert (X: models  (fun (_:pred) (_:vallst) => true) E'( ite e (translateStmt b1 source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
      assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H9;  intros; specialize(H1 x); specialize (H9 x); exact (H1 (H9 H4))).
      erewrite (exp_eval_agree (E:=E) (E':=E')); eauto. simpl. rewrite condFalse.
      rewrite <- H7 in *.
      inversion H0; inversion H3.
      eapply IHterminates; eauto.
      admit.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E' e s0 v); eauto.
          + assert (freeVars e ⊆ fst (getAnn D)) by  (rewrite <- H7 in H0; inversion H0; simpl; assumption).
            assert (agree_on eq (freeVars e) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
            eapply (exp_eval_agree (E:=E) (E':=E')); eauto.  }
+ case_eq (undefLift Y); intros; simpl; eauto.
    *  split; eauto.  eapply (guardList_true_if_eval); eauto.
       assert ( list_union (List.map freeVars  Y)  ⊆ fst (getAnn D)) by ( rewrite <- H7 in H0; inversion H0; simpl; assumption).
       assert (agree_on eq (list_union (List.map freeVars Y)) E E') by (cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4))).
       erewrite omap_agree; eauto.
       intros. 
       destruct Y. 
       { inversion H12. }
       { assert (X: exists v, (exp_eval E x) = Some v).
         - eapply exp_eval_if_list_eval; eauto. eapply in_if_get; eauto. 
         - destruct X.  rewrite H13.
         assert (freeVars x ⊆ fst (getAnn D)).
           +  cset_tac. hnf in H10. specialize (H10 a). eapply H10.  unfold list_union.  simpl.  eapply list_union_start_swap.  cset_tac. left; right; assumption. 
         - assert (agree_on eq (freeVars x) E E'). 
           + cset_tac. hnf.  hnf in H11.  intros. eapply (H11 x2). unfold list_union. simpl. eapply list_union_start_swap. cset_tac.  left;right; assumption.
           + eapply exp_eval_agree; eauto. }

 destruct H12.
       { unfold omap in def. monad_inv def. rewrite EQ.
         assert (freeVars x ⊆ fst (getAnn D)).
         -  cset_tac. hnf in H10. specialize (H10 a). eapply H10.  unfold list_union.  simpl.  eapply list_union_start_swap.  cset_tac. left; right; assumption. 
         - assert (agree_on eq (freeVars x) E E'). 
           + cset_tac. hnf.  hnf in H11.  intros. eapply (H11 x2). unfold list_union. simpl. eapply list_union_start_swap. cset_tac.  left;right; assumption.
           + eapply exp_eval_agree; eauto. }
       { assert (X: exists v, (exp_eval E x) = Some v).
         - eapply  exp_eval_if_list_eval; eauto. 
           + cset_tac. hnf. right. hnf. left; reflexivity.
           + decide (x = x'0).
             * hnf. left; eauto.
             * hnf. right. eapply IHget; eauto.
           
         - eapply exp_eval_if_list_eval.   }
(*intros. 
       unfold omap in def. eapply (omap_inversion _ _ (exp_eval E) Y) . assumption.
        { inversion H12.  }
        { inversion H12.  rewrite <- H16.  monad_inv def.  rewrite EQ. 
         assert (freeVars x ⊆ fst (getAnn D)).
         -  cset_tac. hnf in H10. specialize (H10 a). eapply H10.  unfold list_union.  simpl.  eapply list_union_start_swap.  cset_tac. left; right; assumption. 
         - assert (agree_on eq (freeVars x) E E'). 
           + cset_tac. hnf.  hnf in H11.  intros. eapply (H11 x0). unfold list_union. simpl. eapply list_union_start_swap. cset_tac.  left;right; assumption.
           + eapply exp_eval_agree; eauto. 
         - eapply exp_eval_if_list_eval.   }
             
           cset_tac; hnf; hnf in H1;  hnf in H10;  intros; specialize(H1 x); specialize (H10 x); exact (H1 (H10 H4)).
         eapply (exp_eval_agree (E:=E) (E':=E')); eauto.
eapply exp_eval_agree.
         
       { simpl in def. monad_inv def.  
}
       { simpl in H9.  case_eq (undef a); intros; simpl.
         - eapply IHY; eauto.
       { simpl  in H9. unfold omap in def. monad_inv def.  case_eq (undef a0); intros.
         - 
    * simpl. econstructor.
    * simpl. case_eq (undefLift (a
      { simpl. split; eapply IHY;  admit. (* TODO: Build List Lemma from guard_true_if_eval *) *) admit.
  + rewrite <-  H7 in H3. exfalso. inversion H3.
  + rewrite <- H7 in H3. exfalso. inversion H3.
Qed.
*)

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** Checks wether two lists agree on their values. But the environment needs to be defined on every
variable. Otherwise the result is false **)
Fixpoint agreeOnList (E:onv val) (k:nat) XL YL:=
match k with
| 0 => True
| S k' =>  match XL, YL with
             |nil , nil => True
             | nil, _ => False
             | _, nil => False
             | a::XL', b::YL' => match (exp_eval E a), (exp_eval E b) with
                                   | Some v1, Some v2 => v1 = v2 /\ (agreeOnList E k' XL' YL')
                                   | None, None =>  False
                                   | _,_ => False
                                 end
           end
end.

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
forall F E E' s s' pol P Q,
(forall E, models F E Q -> ~ models F E (smtAnd (translateStmt s pol) P))
->Terminates (nil, E, s) (nil, E', s')
-> exists Q', models F E'  Q' /\
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

Definition combineEnv (E1:onv val) E2 :=
fun x => match E1 x with
             |Some v => Some v
             | None => E2 x
         end.

Lemma extend_not_models:
forall F  s Q, 
(forall E, ~ models F E s)
-> (forall E, models F E Q -> ~ models F E s).

Proof.
intros.
admit.
Qed.

Lemma unsat_impl_sim:
forall F E s t, 
(forall E, ~ models F E (smtCheck s t))
-> noFun s
-> noFun t
-> sim (nil, E, s) (nil, E, t).

Proof.
intros.
unfold smtCheck in H.
eapply (noFun_impl_term_crash E s) in H0.
eapply (noFun_impl_term_crash E t) in H1.
destruct H0 as [ Es  [s' [ sterm| scrash ]]]; destruct H1 as [Et [t' [ tterm | tcrash ]]]. 
- pose proof (extend_not_models _ _ (constr (Con (O::nil)) (Con (O::nil))) H) .
  pose proof (unsat_extension _ E Es _ s' source _ _ H0 ). 
  specialize (H1 sterm).
  destruct H1 as [Q [M H1]].
  assert (H2: forall E0:onv val,    models F E0 (smtAnd (constr (Con (O :: nil)) (Con (O :: nil))) Q) ->
       ~  models F E0 (smtAnd (translateStmt t target) (translateStmt s' source) )).
  + intros. eapply (smtand_neg_comm). apply (H1 E0 H2). 
  +  pose proof (unsat_extension _ E Et _ t' target _ (smtAnd (constr (Con (O::nil)) (Con (O::nil))) Q) H2).
     specialize (H3 tterm).
     destruct H3 as [Q' [M2 H3]].
     specialize (H3 (combineEnv Es Et)).
     (* jetzt Lemma, dass combineEnv Es Et ~ Es / Et für jeweiliges models wgn Annahme von terminates *)
     admit.
- (* target crasht --> nicht semantisch äquivalent --> muss E geben. *)
  admit.
- (* source crasht --> egal was Ergebnis is, weil env immer! unsat sein wird, da zwei widersprücliche Constraints enthalten sind *)
  admit.
- (* s. Fall davor *)
  admit.
Qed.
  
(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
