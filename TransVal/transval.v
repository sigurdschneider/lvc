Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.
Require Import tvalTactics TUtil Guards crashProps termProps.

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

Definition combineEnv D (E1:onv val) E2 :=
fun x => if [x ∈ D] then E1 x else E2 x.

Lemma noFun_impl_term_crash :
forall E s,
noFun s
->  exists E' s', forall L, Terminates (L, E, s)(L, E', s')
                            \/ Crash (L, E, s) (L, E', s').

Proof.
intros.
general induction H.
-  case_eq (exp_eval E e); intros.
   + destruct (IHnoFun (E[x<- Some v])) as [E' [s' termcrash]].
     exists E'; exists s'; intros.
     destruct (termcrash L) as [ term | crash].
     * left. econstructor; eauto.
              { econstructor; eauto. }
              { intros. hnf; isabsurd. }
     * right. econstructor; eauto; try  econstructor; eauto; intros; isabsurd.
   + exists E; exists (stmtExp x e s).
       right. econstructor; eauto; intros; try hnf; try isabsurd.
       intros. unfold reducible2 in H1.  destruct H1. destruct H1.
       isabsurd.
- case_eq (exp_eval E e); intros.
  + case_eq (val2bool v); intros.
    * destruct (IHnoFun1 E) as [E' [s' termcrash]].
      exists E'; exists s'; intros.
      destruct (termcrash L) as [term | crash].
      { left. econstructor; eauto.
       - econstructor; eauto.
       - hnf; intros; isabsurd. }
      { right. econstructor; eauto. econstructor; eauto.
      intros; isabsurd. }
    * destruct (IHnoFun2 E) as [E' [s' termcrash]];
      exists E'; exists s'; intros.
      destruct (termcrash L) as [ term | crash ].
      { left. econstructor; eauto.
       - econstructor; eauto.
       - hnf; intros; isabsurd. }
      { right. econstructor; eauto. econstructor; eauto.
      intros; isabsurd. }
  +  exists E; exists (stmtIf e s t).
            right. econstructor; eauto; intros; try hnf; try isabsurd.
            intros. unfold reducible2 in H2. destruct H2. destruct H2.
            isabsurd.
- case_eq (omap (exp_eval E) Y); intros.
  + exists E; exists (stmtGoto l Y); left; econstructor; eauto.
  + exists E; exists (stmtGoto l Y); right.
           econstructor; eauto; intros; try hnf; try isabsurd.
- case_eq (exp_eval E e).
  + exists E; exists (stmtReturn e).
           left; econstructor; eauto.
  + exists E; exists (stmtReturn e). right.
           econstructor; eauto; intros; try hnf; try isabsurd.
           intros. unfold reducible2 in H0. destruct H0.
           destruct H0. inversion H0.
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

Lemma freeVars_undefLift:
forall a el ul,
undefLift el = Some ul
-> a ∈  freeVars ul
-> a ∈ list_union (List.map Exp.freeVars el).

Proof.
  intros a el ul udef inclFV.
  general induction el.
  - simpl in *. admit.
Qed.

Lemma unsat_extension:
forall L D E E' s s' pol P Q,
(forall F E, models F E Q -> ~ models F E (smtAnd (translateStmt s pol) P))
-> ssa s D
-> noFun s
->Terminates (L, E, s) (L, E', s')
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
    specialize (IHTerminates L' an (E0[x <- Some v]) E'0 s' s'0).
    inv H4. destruct pol; simpl in *.
    * specialize (IHTerminates source P (smtAnd Q (guardGen (undef e) source (constr (Var x) e)))).
      destruct IHTerminates as [Q' IHT]; intros; eauto; simpl in *.
      { specialize (H1 F E). destruct H5 as [H5 H5'].
        specialize (H1 H5).  hnf in H0; hnf; intros.
        eapply H1. destruct H7. split; simpl; eauto.
        destruct (undef e); simpl in *; eauto. destruct H5'.
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
               { simpl. hnf. intros. inv H3; subst.
                 eapply (term_ssa_eval_agree L' L' s'); eauto. rewrite H12.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E'0 e = Some v).
              { eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto. }
              rewrite H5; rewrite H7; simpl.  eapply bvEq_equiv_eq. reflexivity.
           + case_eq (undef e); intros; simpl.
             * split; eauto.
               eapply (guard_true_if_eval _ _ e); eauto.
               eapply (exp_eval_agree (E:=E0)); eauto. hnf; intros.
               eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
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
               { simpl. hnf. intros. inv H4.
                 eapply (term_ssa_eval_agree L' L' s'); eauto. rewrite H12.
                 simpl. cset_tac. right; eauto. }
               { simpl. unfold update. decide (x === x).
                 - reflexivity.
                 - exfalso; eapply n; reflexivity. }
             * assert (exp_eval E'0  e = Some v).
              { eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto. }
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
    specialize (IHTerminates L' ans E' E'0 s' s'0).
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
              hnf. intros.
              eapply (term_ssa_eval_agree L' L' s' _ s'0 E' E'0); eauto.
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
            hnf. intros.
            eapply (term_ssa_eval_agree L' L' s' _ s'0 E' E'0); eauto.
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
    specialize (IHTerminates L' ant E' E'0 s' s'0).
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
            hnf. intros. eapply (term_ssa_eval_agree L' L' s' _ s'0 E' E'0); eauto.
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
            hnf. intros. eapply (term_ssa_eval_agree L' L' s' _ s'0 E' E'0); eauto.
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
  + specialize (H0 l Y); isabsurd.
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

Lemma guardTrue_if_Terminates_ret:
forall L L' E s E' e g,
noFun s
-> undef e = Some g
-> Terminates (L, E, s)(L', E', stmtReturn e)
-> forall F, models F E' g.

Proof.
intros. general induction H1.
- eapply (guard_true_if_eval); eauto.
- specialize (IHTerminates L0 L'0 E' s' E'0 e g).
  inversion H2.
  + rewrite <- H5 in *. inversion H; subst.
    eapply IHTerminates; eauto.
  + rewrite <- H6 in *; inversion H; subst.
    * eapply IHTerminates; eauto.
    * eapply IHTerminates; eauto.
  + rewrite <- H4 in H0. exfalso; specialize (H0 l Y); isabsurd .
  + rewrite <- H4 in *.  exfalso. inversion H.
Qed.

Lemma guardTrue_if_Terminates_goto:
forall L L' E s E' f x g,
noFun s
-> undefLift x = Some g
-> Terminates (L, E, s) (L', E' , stmtGoto f x)
-> forall F, models F E' g.

Proof.
intros. general induction H1.
- eapply guardList_true_if_eval; eauto.
- specialize (IHTerminates L0 L'0  E' s' E'0 f x g).
  inversion H2.
  + rewrite <- H5 in *. inversion H; subst.
    eapply IHTerminates; eauto.
  + rewrite <- H6 in *. inversion H; subst.
    * eapply IHTerminates; eauto.
    * eapply IHTerminates; eauto.
  + rewrite <- H4 in *; specialize (H0 l Y); isabsurd.
  + rewrite <- H4 in *; inversion H.
Qed.

Lemma predeval_uneq_ret:
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

Lemma labeq_incr:
forall n1 n2,
LabI (1 + n1) = LabI (1 + n2)
-> LabI n1  = LabI n2.

Proof.
intros; general induction n1; eauto.
Qed.

Lemma predeval_uneq_goto:
forall E l1 l2 et es el el' P,
omap (exp_eval E) et = Some el
-> omap (exp_eval E) es = Some el'
(*-> l1 = l2 *)
->(forall F, models F E P)
-> (forall (F:lab->vallst->bool),
      models F E P ->
      ~ (models F E (guardGen (undefLift et) target (smtNeg (funcApp l1 et))) /\
         models F E (guardGen (undefLift es) source (funcApp l2 es))))
-> (el = el').

Proof.
  intros. decide (el = el').
  - assumption.
  - decide (l1 = l2).
    + pose (F:= (fun (_:lab) => fun x => if [ x = el' ] then true else false )).
    specialize (H2 F). specialize (H1 F). specialize (H2 H1). clear H1.
    case_eq (undefLift et); case_eq (undefLift es); intros;
    rewrite H1 in H2; rewrite H3 in H2; simpl in H2; unfold evalSpred in H2;
    rewrite e in H2; destruct l2; simpl in H2;
    unfold evalList in H2; rewrite H in H2; rewrite H0 in H2; simpl in H2.
      *exfalso. eapply H2.
        split; intros; simpl; try split.
        { unfold F in H5. decide (el = el'); isabsurd. }
        { eapply (guardList_true_if_eval); eauto. }
        { unfold F. decide (el' = el'); try isabsurd; econstructor; eauto. }
      * exfalso. eapply H2.
        split; intros; simpl; try split.
        { unfold F in H5. decide (el = el'); isabsurd. }
        { unfold F. decide (el' = el'); try isabsurd; econstructor; eauto. }
      *exfalso. eapply H2.
        split; intros; simpl; try split.
        { unfold F in H4. decide (el = el'); isabsurd. }
        { eapply (guardList_true_if_eval); eauto. }
        { unfold F. decide (el' = el'); try isabsurd; econstructor; eauto. }
      *exfalso. eapply H2.
        split; intros; simpl; try split.
        { unfold F in H4. decide (el = el'); isabsurd. }
        { unfold F. decide (el' = el'); try isabsurd; econstructor; eauto. }
    + pose (F:= fun l => fun (_:vallst) => if [l = labInc l2 1] then true else false).
      specialize (H1 F); specialize (H2 F).
      specialize (H2 H1).
      case_eq (undefLift es); case_eq (undefLift et); intros; simpl in H2;
      rewrite H3 in H2; rewrite H4 in H2; simpl in H2; unfold evalSpred in H2;
     exfalso; apply H2;
      split; intros; simpl; try split.
      * unfold F in H6. decide (labInc l1 1 = labInc l2 1); try isabsurd.
        eapply n0. unfold labInc in e.  destruct l1; destruct l2; eauto.
        eapply labeq_incr; eauto.
      * eapply (guardList_true_if_eval); eauto.
      * unfold F.  decide (labInc l2 1 = labInc l2 1);
                  try isabsurd; econstructor; eauto.
      * unfold F in H5. decide (labInc l1 1 = labInc l2 1); try isabsurd.
        eapply n0. unfold labInc in e.  destruct l1; destruct l2; eauto.
        eapply labeq_incr; eauto.
      * eapply (guardList_true_if_eval); eauto.
      * unfold F.  decide (labInc l2 1 = labInc l2 1);
                  try isabsurd; econstructor; eauto.
      * unfold F in H6. decide (labInc l1 1 = labInc l2 1); try isabsurd.
        eapply n0. unfold labInc in e.  destruct l1; destruct l2; eauto.
        eapply labeq_incr; eauto.
      * unfold F.  decide (labInc l2 1 = labInc l2 1);
                  try isabsurd; econstructor; eauto.
      * unfold F in H5. decide (labInc l1 1 = labInc l2 1); try isabsurd.
        eapply n0. unfold labInc in e.  destruct l1; destruct l2; eauto.
        eapply labeq_incr; eauto.
      * unfold F.  decide (labInc l2 1 = labInc l2 1);
                  try isabsurd; econstructor; eauto.
Qed.

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
    + simpl; simpl in H; hnf in H;  unfold evalSexp.
      pose proof (exp_combineenv_eql a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
      destruct H0; hnf; intros; try setSubstUnion H.
      * rewrite H0; eauto. erewrite IHel; eauto.
        hnf; intros; setSubstUnion H.
Qed.

Lemma models_agree F E E' s:
  agree_on eq (freeVars s) E E'
  -> (models F E s <-> models F E' s).

Proof.
intros agree; general  induction s; simpl in *; try reflexivity.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs F E E'); try reflexivity; setSubst2 agree.
- assert (agree_on eq (Exp.freeVars e) E E') by setSubst2 agree.
  assert (exp_eval E e = exp_eval E' e)
  by( eapply exp_eval_agree; symmetry; eauto).
  case_eq (exp_eval E e); intros; unfold evalSexp.
  +  rewrite <- H0. rewrite H1. case_eq(val2bool v); intros.
     * rewrite (IHs1 F E E'); try reflexivity; setSubst2 agree.
     * rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
  + rewrite <- H0; rewrite H1; simpl.
    rewrite (IHs2 F E E'); try reflexivity; setSubst2 agree.
- rewrite (IHs1 F E E'), (IHs2 F E E'); try reflexivity; setSubst2 agree.
-  assert (exp_eval E e = exp_eval E' e)
    by ( eapply exp_eval_agree; symmetry; eauto; setSubst2 agree).
  assert (exp_eval E e0 = exp_eval E' e0)
    by (eapply exp_eval_agree; symmetry; eauto; setSubst2 agree).
  unfold evalSexp; rewrite <- H; rewrite <- H0.
  unfold val2bool.
  case_eq (exp_eval E e); case_eq (exp_eval E e0); intros;
  rewrite bvEq_equiv_eq; reflexivity.
- unfold evalSpred. destruct p.  unfold evalList.
  assert (omap (exp_eval E) a = omap (exp_eval E')  a).
  + eapply omap_exp_eval_agree; symmetry; eauto.
  + rewrite <- H. destruct (omap (exp_eval E) a); reflexivity.
- unfold evalSexp.
  assert (exp_eval E e = exp_eval E' e)
    by (eapply  exp_eval_agree; symmetry; eauto; setSubst2 agree).
  rewrite <- H. case_eq (exp_eval E e); intros; reflexivity.
Qed.

Lemma combineenv_eql:
forall F s D Es Et,
 freeVars s ⊆  D
->(  models F Es s  <-> models F (combineEnv D Es Et) s).

Proof.
  intros. eapply models_agree. eapply (agree_on_incl (lv:=D)); eauto; symmetry.
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
    + simpl in *; hnf in H. unfold evalSexp.
      pose proof (exp_combineenv_eqr a D Es Et (exp_eval Et a)).
      destruct H0.
      * hnf; intros; cset_tac. eapply H. split; eauto.
        unfold list_union; simpl. eapply list_union_start_swap; cset_tac; eauto.
      * rewrite H1; eauto. f_equal.
        symmetry. rewrite (IHel D Es Et (omap (exp_eval  Et) el)); eauto.
        hnf. intros. cset_tac. eapply H. split; eauto.
        unfold list_union. simpl. eapply list_union_start_swap. cset_tac; eauto.
Qed.

Lemma combineenv_eqr:
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
       * destruct H1; eauto.
         specialize (H1 H0). rewrite H1.
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
       * destruct H1; eauto.  specialize (H1 H0). rewrite H1.
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
       * destruct H2; eauto. specialize (H2 H0). rewrite H2.
         pose proof (exp_combineenv_eqr e0 D Es Et (Some v0)).
         assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
       { hnf; intros. hnf in H. simpl in H. cset_tac. eapply H.
         split; eauto. }
       { destruct H5; eauto. specialize (H5 H1). rewrite H5.
         split; intros; eauto.
       }
    + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { destruct H5; eauto. specialize (H5 H1). rewrite H5.
          split; intros; eauto. }
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et (Some v)).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { destruct H5; eauto. specialize (H5 H1). rewrite H5.
          split; intros; eauto. }
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H2; eauto. specialize (H2 H0). rewrite H2.
        pose proof (exp_combineenv_eqr e0 D Es Et None).
        assert (agree_on eq (Exp.freeVars e0 ∩ D) Es Et).
        { setSubst2 H. }
        { destruct H5; eauto.  specialize (H5 H1). rewrite H5.
          split; intros; eauto. }
  -unfold evalSpred; simpl. unfold labInc. destruct p.
   unfold evalList.
   pose proof (explist_combineenv_eqr a D Es Et (omap (exp_eval (combineEnv D Es Et)) a)).
   destruct H0; eauto.
   rewrite H0; eauto. reflexivity.
  - unfold evalSpred. unfold evalSexp.
    case_eq (exp_eval (combineEnv D Es Et) e); intros.
    + pose proof (exp_combineenv_eqr e D Es Et (Some v)).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H1; eauto.  specialize (H1 H0). rewrite H1.
        split; intros; eauto.
    + pose proof (exp_combineenv_eqr e D Es Et None).
      assert (agree_on eq (Exp.freeVars e ∩ D) Es Et).
      * setSubst2 H.
      * destruct H1; eauto. specialize (H1 H0). rewrite H1.
        split; intros; eauto.
Qed.

Lemma terminates_impl_eval:
forall L L' E s E' e,
noFun s
-> Terminates (L, E, s) (L', E',stmtReturn  e)
-> exists v, exp_eval E' e = Some v.

Proof.
intros. general induction H0.
- exists v; eauto.
- exploit (IHTerminates L0 L'0 E' s' E'0 e); eauto.
  + inversion H2; subst; try isabsurd.
    * inversion H. rewrite <- H13; eauto.
    * inversion H;  rewrite <- H14; eauto.
  + inversion H; subst; eauto; isabsurd.
Qed.

Lemma terminates_impl_evalList:
forall L  L' E s E' f el,
noFun s
-> Terminates (L, E, s) (L', E', stmtGoto f el)
-> exists v, omap (exp_eval E') el = Some v.

Proof.
intros. general induction H0.
- exists vl; eauto.
- exploit (IHTerminates L0 L'0 E' s' E'0 f el); eauto.
  + inversion H2; subst; inversion H; subst; eauto; isabsurd.
  + inversion H; subst; eauto; isabsurd.
Qed.

Lemma ssa_move_return:
  forall D (L:F.labenv) E s E' e,
    noFun s
    -> ssa s D
    -> Terminates (L, E, s) (L, E', stmtReturn e)
    -> exists D', ssa (stmtReturn e) D'
                  /\ fst (getAnn D) ⊆ fst (getAnn D')
                  /\ snd (getAnn D') ⊆ snd (getAnn D).

Proof.
  intros. general induction H1.
  - exists D. split; eauto. split; cset_tac; eauto.
 -  inversion H3; subst; isabsurd.
    + inversion H; inversion H2; subst. exploit (IHTerminates an L' (E0[x<-Some v]) s' ); eauto.
      destruct X. exists x0.
      destruct H8 as [H8 [H9 H10]].
      split; eauto; split;  simpl; cset_tac; rewrite H7 in *;
      simpl in *; hnf in *; eauto. eapply H9; cset_tac; eauto.
    + inversion H; inversion H2; subst.
      * exploit (IHTerminates ans); eauto.
        destruct X. exists x.
        destruct H11 as [ H11 [ H12 H13]].
        split; eauto; split; simpl; cset_tac; rewrite H9 in *;
        simpl in *; hnf in *; eauto. eapply H6.
        left; eapply H13; eauto.
      * exploit (IHTerminates ant); eauto.
        destruct X; exists x.
        destruct H11 as [ H11 [ H12 H13]].
        split; eauto; split; simpl; cset_tac; rewrite H10 in *;
        simpl in *; hnf in *; eauto; eapply H6.
        right; eapply H13; eauto.
Qed.

Lemma ssa_move_goto:
  forall D (L:F.labenv) E s E' f el,
    noFun s
    -> ssa s D
    -> Terminates (L, E, s) (L, E', stmtGoto f el)
    -> exists D', ssa (stmtGoto f el) D'
                  /\ fst (getAnn D) ⊆ fst (getAnn D')
                  /\ snd (getAnn D') ⊆ snd (getAnn D).

Proof.
  intros D L E s E' f el nfS ssaS sterm.
  general induction sterm.
  - exists D; eauto. split; eauto; split; cset_tac; eauto.
  - inversion ssaS; subst; try isabsurd.
    + inversion nfS; inversion ssaS; inversion H;
      subst; exploit (IHsterm an L' (E0 [ x<- Some v]) s'); eauto.
      destruct X as [D'' [ssaGoto [fstSubset sndSubset]]].
      exists D''; simpl.
      split; eauto; split; cset_tac; rewrite H18 in *;
      simpl in *; hnf in *; eauto.
      eapply fstSubset. cset_tac; eauto.
    +  inversion nfS; inversion ssaS; inversion H; subst.
       * exploit (IHsterm ans); eauto.
         destruct X as [D'' [ssaGoto [fstSubset sndSubset]]].
         exists D''; simpl.
         split; eauto. split; simpl; cset_tac; rewrite H25 in *;
         simpl in *; hnf in *; eauto.
         eapply H22. left; eapply sndSubset; eauto.
       * exploit (IHsterm ant); eauto.
         destruct X as [D'' [ssaGoto [fstSubset sndSubset]]].
         exists D''; simpl.
         split; eauto.
         split; cset_tac; rewrite H26 in *; simpl in *;
         hnf in *; eauto.
         eapply H22. right; eapply sndSubset; eauto.
Qed.

Lemma agree_on_ssa_combine:
  forall D D' Ds' Dt' L E s t Es Et es et,
    getAnn D = (Ds' ∩ Dt', Ds')
    -> getAnn D' = (Ds' ∩ Dt', Dt')
    -> ssa s D
    -> ssa t D'
    -> noFun s
    -> noFun t
    -> (forall x, x ∈ (Ds' ∩ Dt') -> exists v, E x = Some v)
    ->Terminates (L, E, s) (L, Es, stmtReturn es)
    -> Terminates (L, E, t) (L, Et, stmtReturn et)
    -> (agree_on eq (Exp.freeVars et) Et (combineEnv Ds' Es Et)
        /\ agree_on eq (Exp.freeVars es) Es (combineEnv Ds' Es Et)).

Proof.
  intros D D' Ds' Dt' L E s t Es Et es et.
  intros getD getD' ssaS ssaT nfS nfT liveness sterm tterm.
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
     * specialize (liveness x  H2); destruct liveness.
       pose proof (term_ssa_eval_agree L L s D (stmtReturn es) E Es ssaS nfS sterm).
       pose proof (term_ssa_eval_agree L L t D' (stmtReturn et) E Et ssaT nfT tterm).
       rewrite getD  in H4. rewrite getD'  in H5. simpl in *.
       rewrite <- H4; eauto. rewrite <- H5; eauto.
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

Lemma unsat_impl_sim:
forall L D D' Df  Ds' Dt'  E s t,
(forall F E, ~ models F E (smtCheck s t))
-> getAnn D = (Df, Ds') (*To acces the environments from ssa *)
-> getAnn D' = (Df, Dt') (* Same *)
-> ssa s D (* Every variable gets defined only once *)
-> ssa t D' (* Same *)
-> Ds' ∩ Dt' = Df (* The free Variables do not get overwritten? *)
-> noFun s (* disallow function definitions and external function calls *)
-> noFun t (* same*)
-> (forall x, x ∈ Df -> exists v, E x = Some v) (* Free Variables must be defined *)
-> @sim _ statetype_F _ statetype_F  (L, E, s) (L, E, t).

Proof.
intros.
unfold smtCheck in H.
pose proof  (noFun_impl_term_crash E s H5).
pose proof  (noFun_impl_term_crash E t H6).
destruct H8 as [ Es  [s' termcrash ]]. destruct H9 as [Et [t' termcrash2 ]].
destruct (termcrash L) as [sterm | scrash].
clear termcrash.
destruct (termcrash2 L) as [tterm | tcrash].
clear termcrash2.
(* s terminiert & t terminiert *)
- pose proof (extend_not_models _ smtTrue H).
  pose proof (unsat_extension L D E Es s s' source _ _ H8 ).
  specialize (H9 H2 H5 sterm).
  destruct H9 as [Q [M [ fvQ modS]]].
  assert (smodS: forall F, forall E0:onv val, models F E0 (smtAnd smtTrue Q) ->
       ~  models F E0 (smtAnd (translateStmt t target) (translateStmt s' source) )).
  + intros. eapply (smtand_neg_comm).  apply (modS F E0 H9).
  + clear modS. clear H8.
    pose proof (unsat_extension L D' E Et t t' target _ (smtAnd smtTrue Q) smodS)
      as modTS.
    clear smodS. clear H.
    specialize (modTS H3 H6 tterm).
    destruct modTS as [Q' [modQ' [fvQ' modTS]]].
    exploit (terminates_impl_star2  L E s L Es s' H5 sterm).
    exploit (terminates_impl_star2 L E  t L Et t' H6 tterm).
    destruct X as [ sstep X]; destruct X0 as [ tstep  X0].
    destruct X as [ [es sRet] | [fs [Xs sFun]]];
    destruct X0 as [ [et tRet] | [ft [Xt tFun]]].
    * subst. eapply simTerm.
      instantiate (1:=(L, Et, stmtReturn et)).
      instantiate (1:= (L, Es, stmtReturn es)).
      { simpl.
        assert (exists evs, exp_eval Es es = Some evs)
          by (eapply (terminates_impl_eval L L E s Es es H5 sterm)).
        assert (exists evt, exp_eval Et et = Some evt)
          by (eapply terminates_impl_eval; eauto).
        destruct H as [evs evalEs].
        destruct H4 as [evt evalEt].
        rewrite evalEs, evalEt in *.
        f_equal.
        pose (P := smtAnd (smtAnd smtTrue Q) Q').
        pose proof (predeval_uneq_ret (combineEnv Ds' Es Et) et es evt evs P).
        symmetry.
        pose proof (agree_on_ssa_combine D D' Ds' Dt' L E s t Es Et es et).
        destruct H4; eauto.
        eapply H; clear H; intros;
        try erewrite exp_eval_agree; eauto.
        - intros. unfold P. specialize (M F). specialize (modQ' F).
          simpl. split; try split; eauto.
          + rewrite H0 in fvQ. simpl in fvQ.
            erewrite <- combineenv_eql; eauto.
          + rewrite H1 in fvQ'. simpl in fvQ'.
            erewrite <- combineenv_eqr; eauto.
            cut (agree_on eq (Ds' ∩ Dt') Es Et).
            * intros. hnf in H. hnf. intros. cset_tac. eapply H. split; eauto.
            *  hnf; intros.  specialize (H7 x H).
               destruct H7.
               assert (agree_on eq (fst (getAnn D')) E Et)
                 by (eapply term_ssa_eval_agree; eauto).
               assert (agree_on eq (fst (getAnn D)) E Es)
                 by (eapply term_ssa_eval_agree; eauto).
               rewrite H0 in H10; simpl in H10.
               rewrite H1 in H9; simpl in H9.
               rewrite <- H9, H10; eauto.
      }
      { eauto. }
      { eauto. }
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
           pose proof (combineenv_eql F Q Ds' Es Et).
           assert (forall v, v ∈ freeVars Q -> v ∈ Ds').
           + intros. hnf in fvQ. rewrite H0 in fvQ. simpl in fvQ.
             exact (fvQ v H4).
           + specialize (H H4).
           rewrite <- H; eauto.
         - specialize (modQ' F).
           unfold E'.  pose proof (combineenv_eqr F Q' Ds'  Es Et).
           assert (agree_on eq (freeVars Q' ∩ Ds') Es Et).
           + hnf. intros. cset_tac. hnf in fvQ'. rewrite H1 in fvQ'.
             specialize (fvQ' x); simpl in fvQ'.
             assert (x ∈ Ds' ∩ Dt') by (cset_tac; eauto).
             eapply (term_ssa_eval_agree) in H2; eauto.
             eapply (term_ssa_eval_agree) in H3; eauto.
             hnf in H2. hnf in H3. rewrite H0 in H2. rewrite H1 in H3.
             specialize (H2 x); specialize (H3 x). simpl in H2; simpl in H3.
             rewrite <- H2; eauto; rewrite <- H3; eauto.
           + rewrite <- (H H4); eauto. }
       { case_eq (undef es); case_eq (undefLift Xt); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s1).
           + unfold E'. rewrite <- combineenv_eql.
             * eapply (guardTrue_if_Terminates_ret L L _ s); eauto.
             *  hnf; intros. eapply (freeVars_undef a es s1 H4) in H8.
                (* freeVars -> Ds' *)
                pose proof (ssa_move_return D L E s Es es).
                destruct H9 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
                rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
                eapply sndSubset. rewrite <- H11. eapply H10; eauto.
           + split.
             *  intros. unfold evalSpred in H10.  unfold F in H10.
                rewrite <- (beq_nat_refl (labN (labInc ft 1))) in H10; isabsurd.
             * split; eauto. unfold evalSpred. unfold F.
               simpl; destruct ft; simpl; econstructor.
         - assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eql.
             * eapply (guardTrue_if_Terminates_ret L L _ s); eauto.
             * hnf; intros. eapply (freeVars_undef a es s0 H4) in H8.
               (* freeVars -> Ds' *)
               pose proof (ssa_move_return D L E s Es es).
                destruct H9 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
                rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
                eapply sndSubset. rewrite <- H11. eapply H10; eauto.
           + split; try split; eauto; intros.
             * unfold evalSpred in H9; unfold F in H9.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H9; intuition.
             * unfold evalSpred; unfold F; simpl; destruct ft; simpl; econstructor.
         - split; try split; eauto; intros.
           + unfold evalSpred in H9; unfold F in H9.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H9; intuition.
           + unfold evalSpred; unfold F; simpl; destruct ft; simpl; econstructor.
         - split; try split; eauto; intros.
           + unfold evalSpred in H8; unfold F in H8.
               rewrite <- (beq_nat_refl (labN(labInc ft 1))) in H8; intuition.
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
           unfold E'.   rewrite <- (combineenv_eql); eauto.
           rewrite H0 in fvQ. simpl in fvQ. assumption.
         - specialize (modQ' F).
           unfold E'.
           unfold E'.  pose proof (combineenv_eqr F Q' Ds'  Es Et).
           assert (agree_on eq (freeVars Q' ∩ Ds') Es Et).
           + hnf. intros. cset_tac. hnf in fvQ'. rewrite H1 in fvQ'.
             specialize (fvQ' x); simpl in fvQ'.
             assert (x ∈ Ds' ∩ Dt') by (cset_tac; eauto).
             eapply (term_ssa_eval_agree) in H2; eauto.
             eapply (term_ssa_eval_agree) in H3; eauto.
             hnf in H2. hnf in H3. rewrite H0 in H2. rewrite H1 in H3.
             specialize (H2 x); specialize (H3 x). simpl in H2; simpl in H3.
             rewrite <- H2, H3; eauto.
           +  eapply (H H4); eauto.  }
       { case_eq (undef et); case_eq (undefLift Xs); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eql.
             * eapply (guardTrue_if_Terminates_goto L L _ s); eauto.
             * hnf; intros. eapply (freeVars_undefLift a Xs s0 H) in H8.
               (* freeVars -> Ds' *)
               pose proof (ssa_move_goto D L E s Es fs Xs).
                destruct H9 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
                rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
                eapply sndSubset. rewrite <- H13. eapply H11; eauto.
           + split.
             *  intros. unfold evalSpred in H10.  unfold F in H10.
                exfalso; assumption.
             * split; eauto. unfold evalSpred. unfold F.
               simpl; destruct fs; simpl; econstructor.
         - assert (models F E' s0).
           + unfold E'. rewrite <- combineenv_eqr.
             * eapply (guardTrue_if_Terminates_ret  L L _ t); eauto.
             * hnf; intros. cset_tac. eapply (freeVars_undef x et s0 H4) in H9.
               (* freeVars -> Ds' *)
               pose proof (ssa_move_return D' L E t Et et H6 H3).
                destruct H8 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
                rewrite H1 in *. simpl in *.
                rewrite <- H13 in fstSubset,sndSubset; simpl in fstSubset, sndSubset.
                assert (x ∈ Dt')
                  by (eapply sndSubset; rewrite <- H12; eapply H11; eauto).
                destruct (H7 x); eauto.
                assert (agree_on eq (fst (getAnn D)) E Es)
                   by (eapply term_ssa_eval_agree; eauto).
                assert (agree_on eq (fst (getAnn D')) E Et)
                  by (eapply term_ssa_eval_agree; eauto).
                rewrite <- H16, <- H17; eauto.
                { rewrite H1; simpl. cset_tac; eauto. }
                { rewrite H0; simpl. cset_tac; eauto. }
           + split; try split; eauto; intros.
             * unfold F; destruct fs; unfold labInc; simpl; eauto.
         - split; try split; eauto; intros.
           + unfold E'.  rewrite <- combineenv_eql.
             * eapply (guardTrue_if_Terminates_goto L L _ s); eauto.
             * hnf; intros. eapply (freeVars_undefLift a Xs s0 H) in H8.
               (* freeVars -> Ds' *)
               pose proof (ssa_move_goto D L E s Es fs Xs).
                destruct H9 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
                rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
                eapply sndSubset. rewrite <- H13. eapply H11; eauto.
           + unfold F; destruct fs; unfold labInc; simpl; eauto.
         - unfold evalSpred; unfold F; simpl; destruct fs;
           simpl; econstructor; eauto. }
    * subst. eapply simTerm.
      instantiate (1:=(L, Et, stmtGoto ft Xt)).
      instantiate (1:= (L, Es, stmtGoto fs Xs)).
      { simpl in modTS; simpl; eauto.
(*      pose proof (terminates_impl_evalList E s Es fs Xs H5 sterm).
      pose proof (terminates_impl_evalList E t Et ft Xt H6 tterm).
      destruct H as [es seval]; destruct H8 as [et teval].
      pose proof (predeval_uneq_goto (combineEnv Ds' Es Et) ft fs Xt Xs x0 x).
      pose proof (explist_combineenv_eq_left Xs Ds' Es Et (Some x)).
      destruct H10.
      { admit. }
      { pose proof (explist_combineenv_eqr Xt Ds' Es Et (Some x0)).
        destruct H12.
        - admit.
        - specialize (H9 (smtAnd smtTrue  (smtAnd Q Q'))).
          specialize (H9 (H13 H8) (H11 H)).
          simpl in H.
          assert (forall F, models F (combineEnv Ds' Es Et) (smtAnd smtTrue (smtAnd Q Q'))).
          + admit.
          + specialize (H9 H14).
            simpl in H14. specialize


      {  admit. }
      { admit. }
 } *) }
     { eauto. }
      { eauto. }
      { admit. (* hnf. intros. unfold reducible2 in H. destruct H. destruct H.
        inversion H. inversion Ldef. *) }
      { admit. (* hnf. intros. unfold reducible2 in H. destruct H. destruct H.
        inversion H. inversion Ldef.*) }
(* s terminiert & t crasht *)
- pose proof (terminates_impl_models L  s D E s' Es H2 H5 sterm).
  assert (forall x, x ∈ fst(getAnn D') -> exists v, E x = Some v).
  + intros. destruct (H7 x); eauto. rewrite H1 in H9; eauto.
  + pose proof (crash_impl_models L L D' t E Et t' H3 H9 H6 tcrash).
  specialize (H (fun _ => fun _ => true) (combineEnv Ds' Es Et)).
  exfalso. apply H. simpl. split.
    * assert (agree_on eq (freeVars (translateStmt s source)) Es (combineEnv Ds' Es Et)).
      { hnf; intros. unfold combineEnv.
        destruct if; try isabsurd; eauto.
        pose proof (ssa_freeVars H2).
        pose proof (ssa_incl H2).
        rewrite H0 in *. simpl in *.
        exfalso; eapply n; eapply H13; eapply H12; eauto.

Lemma freeVars_eq:
forall s D,
  noFun s
  ->ssa s D
  -> freeVars (translateStmt s source) ⊆  IL.freeVars s.

Proof.
  intros s D nfS ssaS.
  general induction ssaS.
  -  simpl in *. case_eq (undef e); intros; simpl.
    +  inversion nfS; rewrite <- IHssaS;  eauto; subst.
       cset_tac. destruct H3 as [H3 | [ [H3 | H3] | H3]].
       * eapply (freeVars_undef) in H3; eauto.
       * left.  split; isabsurd.  inversion H. right. exfalso. eapply H5. specialize
         { destruct H0.

      { eapply models_agree; eauto.

  + erewrite <- combineenv_eqr; eauto.
    * admit.
  (* Widerspruch konstruieren aus guard = False und ~ models
    apply Lemma dass wenn es gibt i was models s und crash t --> models s /\ t
    konstruieren mit sat_extension und Lemma terminates_impl_sim*)
(* s crasht --> sim zu allem!  *)
- pose proof (crash_impl_err E s Es s' L L H5 scrash ).
  destruct H8. destruct H9. unfold failed in H10. eapply simErr; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)