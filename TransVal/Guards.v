Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.
Require Import tvalTactics TUtil.

 Lemma guard_true_if_eval:
forall F E e s v,
 exp_eval E e = Some v
->  undef e = Some s
->  models F E s.

Proof.
intros. general induction e; simpl.
- simpl in *. monad_inv H. destruct u.
  + apply (IHe F E s x); eauto.
  +  apply (IHe F E s x); eauto.
- simpl in H.  monad_inv H.  simpl in H0. destruct b.
  +  case_eq (undef e1); case_eq (undef e2); intros.
     *  rewrite H in H0; rewrite H1 in H0. simpl in H0.
        inversion H0. simpl; split.
        { eapply IHe1; eauto. }
        { eapply IHe2; eauto. }
     * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
       eapply IHe1; eauto. rewrite <- H0; eauto.
     * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
       eapply IHe2; eauto. rewrite <- H0; eauto.
     * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl.
       exfalso; discriminate H0.
  + destruct b.
    *  case_eq (undef e1); case_eq (undef e2); intros.
     {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.
        simpl; split.
        - eapply IHe1; eauto.
        - eapply IHe2; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
       eapply IHe1; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
       eapply IHe2; eauto. rewrite <- H0; eauto. }
     { rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl.
       exfalso; discriminate H0. }
    * destruct b.
      { case_eq (undef e1); case_eq (undef e2); intros.
        -  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.
simpl; split.
           + eapply IHe1; eauto.
           + eapply IHe2; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
          eapply IHe1; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0; simpl.
          eapply IHe2; eauto. rewrite <- H0; eauto.
        - rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl.
          exfalso; discriminate H0. }
      { destruct b.
        -  case_eq (undef e1); case_eq (undef e2); intros.
           +  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.
              simpl; split.
              * eapply IHe1; eauto.
              * eapply IHe2; eauto.
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0.
             simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
           + rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0.
             simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
            +rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl.
             exfalso; discriminate H0.
        - destruct b.
          +  case_eq (undef e1); case_eq (undef e2); intros.
             *  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.
                simpl; split.
                { eapply IHe1; eauto. }
                { eapply IHe2; eauto. }
             * rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0.
               simpl. eapply IHe1; eauto. rewrite <- H0; eauto.
             *rewrite H in H0; rewrite H1 in H0; simpl in H0; inversion H0.
              simpl. eapply IHe2; eauto. rewrite <- H0; eauto.
             * rewrite H in H0; rewrite H1 in H0; simpl in H0;  simpl.
               exfalso; discriminate H0.
          + destruct b.
            * case_eq (undef e1); case_eq (undef e2); intros.
              {  rewrite H in H0; rewrite H1 in H0. simpl in H0. inversion H0.
                 unfold binop_eval in EQ2.  clear H0. unfold bvDiv in EQ2.
                 simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.
                     hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ k  A) in H0;  eauto.
                 - split.
                   + eapply IHe1; eauto.
                   + eapply IHe2; eauto.  }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0.
                   unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2.
                   simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.
                     hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply ( not_zero_implies_uneq _ k) in H0; eauto.
                 -  eapply IHe1; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0.
                   unfold binop_eval in EQ2. clear H0. unfold bvDiv in EQ2.
                   simpl. split.
                 - case_eq(bvZero x0).
                   + intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   + intros A.   unfold evalSexp. intros. clear H3. clear EQ2.
                     hnf in H0.  rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ k) in H0; eauto.
                 -  eapply IHe2; eauto. }
                 { rewrite H in H0; rewrite H1 in H0; simpl in H0. inversion H0.
                   unfold binop_eval in EQ2. clear H0.
                   unfold bvDiv in EQ2. simpl.
                   case_eq(bvZero x0).
                   - intros.  rewrite H0 in EQ2.  exfalso; discriminate EQ2.
                   - intros A.   unfold evalSexp. intros. clear H3. clear EQ2.
                     hnf in H0. rewrite EQ1 in H0.  simpl in H0. simpl  in A.
                     eapply  (not_zero_implies_uneq _ k) in H0; eauto.    }
                 * case_eq (undef e1); case_eq (undef e2); intros; simpl.
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0.
                     inversion H0. simpl; split.
                     - eapply IHe1; eauto.
                     - eapply IHe2; eauto. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0.
                     inversion H0. simpl.
                     - eapply IHe1; eauto. rewrite <- H3. assumption. }
                   { rewrite H in H0; rewrite H1 in H0; simpl in H0.
                     inversion H0. simpl.
                     - eapply IHe2; eauto. rewrite <- H3. assumption. }
                   {  rewrite H in H0; rewrite H1 in H0; simpl in H0.
                      inversion H0. } }
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
    * rewrite H2 in H0. inversion H0. monad_inv H.
      eapply (guard_true_if_eval); eauto.
  + rewrite H1 in H0; monad_inv H. eapply IHel; eauto.
Qed.

Lemma noguard_impl_eval:
forall E e,
(forall x, x ∈ Exp.freeVars e -> exists v,  E x = Some v)
-> undef e = None
-> exists v, exp_eval E e = Some v.

Proof.
  intros. general induction e.
  - exists v. unfold exp_eval. reflexivity.
   - destruct (H v); simpl; cset_tac; eauto.
   - simpl in H. specialize (IHe E H). simpl in H0.
     destruct IHe; eauto.
     simpl. rewrite H1. simpl. destruct u; simpl.
     + case_eq (val2bool x); intros.
       * exists val_true; unfold option_lift1; simpl.
                rewrite H2; eauto.
       * exists val_false; unfold option_lift1; simpl.
                rewrite H2; eauto.
      + exists (neg x); unfold option_lift1.
               destruct u; eauto.





(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)