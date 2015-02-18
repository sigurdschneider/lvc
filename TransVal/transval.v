Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import bitvec sexp smt nofun noGoto freeVars CombineEnv.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil GuardProps ComputeProps.

(** Function Definitions **)

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** Lemmata **)
Lemma freeVars_incl:
  forall s D Ds Ds' p,
    ssa s D
    -> noFun s
    -> pe (getAnn D) (Ds, Ds')
    -> freeVars (translateStmt s p) ⊆ Ds'.

Proof.
  intros s D Ds Ds' p ssaS nfS getD.
  general induction nfS; inv ssaS; inv getD; subst; simpl.
  - pose proof (ssa_incl ssaS); simpl in *.
    rewrite H4, H8 in H6.
    specialize (IHnfS an (Ds ++ {x; {}}) (Ds') p H5 H6).
    cset_tac.
    case_eq (undef e); intros; rwsimpl H1 H0;
    cset_tac.
    + destruct p; simpl in *; cset_tac.
      * destruct H0 as [guardVars | [ [ varx | expVars ] | ind]]; eauto.
        { eapply (freeVars_undef) in guardVars; eauto.
        eapply H8. eapply H; eauto. }
        { rewrite <- varx.
         pose proof (ssa_incl H5). rwsimpl H6 H0.
         eapply H0; cset_tac; eauto. }
        { eapply H8. eapply H; eauto. }
      * destruct H0 as [guardVars | [ [ varx | expVars ] | ind]]; eauto.
        { eapply (freeVars_undef) in guardVars; eauto.
        eapply H8. eapply H; eauto. }
        { rewrite <- varx.
         pose proof (ssa_incl H5). rwsimpl H6 H0.
         eapply H0; cset_tac; eauto. }
        { eapply H8. eapply H; eauto. }
    + destruct H0 as [ [varx | expVars] | ind]; eauto.
       * rewrite <- varx.
         pose proof (ssa_incl H5). rwsimpl H6 H0.
         eapply H0; cset_tac; eauto.
       * eapply H8; eapply H; eauto.
  -  pose proof (ssa_incl ssaS); simpl in *.
     rewrite <- H3 in *.
     specialize (IHnfS1 ans (Ds0 ∩ Dt) Ds0 p H5 H8).
     specialize (IHnfS2 ant (Ds0 ∩ Dt) Dt p H6 H9).
     cset_tac.
     case_eq (undef e); intros; simpl; rewrite H1 in *; simpl in *;
     cset_tac.
     + destruct p; simpl in *; cset_tac.
       * destruct H0 as [ guardVars | [[indS | indT ] |  expVars ]].
         { eapply (freeVars_undef) in guardVars; eauto.
         eapply H11; eapply H; eapply H2; eauto. }
         { eapply H11; eapply H4; left; eapply IHnfS1; eauto. }
         { eapply H11; eapply H4; right; eapply IHnfS2; eauto. }
         { eapply H11; eapply H; eapply H2; eauto. }
       * destruct H0 as [ guardVars | [[indS | indT ] |  expVars ]].
         { eapply (freeVars_undef) in guardVars; eauto.
         eapply H11; eapply H; eapply H2; eauto. }
         { eapply H11; eapply H4; left; eapply IHnfS1; eauto. }
         { eapply H11; eapply H4; right; eapply IHnfS2; eauto. }
         { eapply H11; eapply H; eapply H2; eauto. }
     + destruct H0 as [ [indS | indT] | expVars].
       * eapply H11; eapply H4; left; eapply IHnfS1; eauto.
       * eapply H11; eapply H4; right; eapply IHnfS2; eauto.
       * eapply H11; eapply H; eapply H2; eauto.
  - pose proof (ssa_incl ssaS);  simpl in *.
    cset_tac.
    eapply H6; eapply H; eapply H1.
    destruct p; simpl in *; cset_tac.
    + case_eq (undefLift Y); intros; rewrite H2 in *;
      simpl in *; eauto.
      cset_tac.
      destruct H0; eauto using freeVars_undefLift.
    + case_eq (undefLift Y); intros; rewrite H2 in *;
      simpl in *; eauto; cset_tac.
      destruct H0; eauto using freeVars_undefLift.
  - pose proof (ssa_incl ssaS); simpl in *.
    cset_tac.
    eapply H6; eapply H; eapply H0.
    case_eq (undef e); intros; rewrite H3 in *;
    destruct p;
    simpl in *; eauto.
    + cset_tac.
      destruct H2; eauto using freeVars_undef.
    + cset_tac.
      destruct H2; eauto using freeVars_undef.
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
    * subst; eapply sim'_sim.
      eapply sim'_expansion_closed; eauto.
      eapply sim_sim'.
      decide (fs = ft).
      { subst.
        destruct (get_dec L (counted ft)) as [[[bE bZ bs]]|].
        - pose proof (terminates_impl_evalList L L E s Es ft Xs H5 sterm).
            pose proof (terminates_impl_evalList L L E t Et ft Xt H6 tterm).
            destruct H as [es seval]; destruct H4 as [et teval].
            pose proof (predeval_uneq_goto (combineEnv Ds' Es Et) ft ft Xt Xs et es).
            specialize (H (smtAnd (smtAnd smtTrue Q) Q')).
            pose proof (explist_combineenv_eql Xs Ds' Es Et (Some es)).
            destruct H4.
            * pose proof (ssa_move_goto D L E s Es ft Xs).
              destruct H4 as [D'' [ssaGoto [fstSubset sndSubset]]]; eauto.
              inversion ssaGoto.
              hnf; intros.
              rwsimpl H0 sndSubset.
              rwsimplB H10 sndSubset.
              eapply sndSubset; eapply H11; eapply H9; eauto.
            *  pose proof (explist_combineenv_eqr Xt Ds' Es Et (Some et)).
               destruct H9.
               { (* freeVars ∩ Ds' agree *)
                 pose proof (ssa_move_goto D' L E t Et ft Xt H6 H3 tterm).
                 destruct H9 as [D'' [ ssaGoto [ fstSubset sndSubset ]]].
                 inversion ssaGoto.
                 eapply (agree_on_incl (lv:=D0 ∩ Ds')); cset_tac; eauto.
                 rwsimpl H1 fstSubset; rwsimpl H1 sndSubset.
                 eapply (agree_on_incl (lv:= Ds' ∩ Dt')).
                 - hnf; intros.
                   (* Es and Et agree on the free variables. *)
                   destruct (H7 x) as [ v Exv]; cset_tac; eauto.
                   assert ( Es x = Some v /\ Et x = Some v).
                   + split.
                     * pose proof (term_ssa_eval_agree L L s D (stmtGoto ft Xs) E Es).
                       rwsimpl H0 H9; rewrite <- H9; cset_tac; eauto.
                     * pose proof (term_ssa_eval_agree L L t D' (stmtGoto ft Xt) E Et).
                       rwsimpl H1 H9; rewrite <- H9; cset_tac; eauto.
                   + destruct H9 as [Esx Etx]; rewrite Esx, Etx; eauto.
                 - cset_tac; eauto.
                   eapply sndSubset; eapply H13; eauto. }
               { specialize (H (H10 teval) (H8 seval)).
                 simpl in H.
                 (* Clean up now *)
                 clear H4. clear H9.
                 specialize (H8 seval); specialize (H10 teval).
                 (* Now make the result value the same everywhere *)
                 rewrite H in teval.
                 Focus 2.
                 - intros.  split.  split; eauto.
                   + specialize (M F).
                     assert (agree_on eq (snd (getAnn D)) Es (combineEnv Ds' Es Et)).
                     * hnf; intros. rewrite H0 in H4.
                       unfold combineEnv; destruct if; eauto; isabsurd.
                     * eapply models_agree; eauto. hnf; intros.  symmetry.
                       eapply H4; cset_tac. hnf in fvQ. eapply fvQ; eauto.
                   + specialize (modQ' F).
                     assert (agree_on eq (snd(getAnn D')) Et (combineEnv Ds' Es Et)).
                     * hnf; intros; rewrite H1 in H4.
                       unfold combineEnv; destruct if; eauto.
                       simpl in H4. destruct (H7 x); cset_tac; eauto.
                       (* Es and Et agree on the free variables *)
                       assert ( Es x = Some x0 /\ Et x = Some x0).
                       { split.
                         - pose proof (term_ssa_eval_agree L L s D (stmtGoto ft Xs) E Es).
                           rwsimpl H0 H11; rewrite <- H11; cset_tac; eauto.
                         - pose proof (term_ssa_eval_agree L L t D' (stmtGoto ft Xt) E Et).
                           rwsimpl H1 H11; rewrite <- H11; cset_tac; eauto. }
                       { destruct H11 as [Esx Etx]; rewrite Esx, Etx; eauto. }
                     * eapply models_agree; eauto. hnf; intros. symmetry.
                       eapply H4. eapply fvQ'; eauto.
                       Focus 2.
                       intros. specialize (modTS F (combineEnv Ds' Es Et)).
                       simpl in modTS. specialize (modTS H4); eauto.
          - pose proof (omap_length exp val es (exp_eval Es) Xs seval).
            pose proof (omap_length exp val es (exp_eval Et) Xt teval).
           decide (length Xs = length bZ).
          + one_step.
            * simpl. rewrite <- e.
                   rewrite H4, H9; eauto.
            * eapply sim_refl.
          + no_step. get_functional.
            * subst. simpl in *; congruence.
            * (* Construct a contradiction as both argument lists are equal
                    and len contains the assumption that the lengths are equal *)
              eapply n.  pose proof (get_functional g Ldef).
              rwsimplB H11 len.
              rewrite len. rewrite H4, H9; eauto.  }
        - no_step; eauto. }
      { exfalso.
      pose (F := (fun l => fun (_:vallst) => if [labInc fs 1 = l] then true else false)).
      specialize (modTS F (combineEnv Ds' Es Et)).
      eapply modTS.
      - simpl; split; try split; eauto.
        + pose proof (combineenv_agree Ds' Es Et).
          eapply (models_agree F (combineEnv Ds' Es Et) Es Q); eauto.
          rwsimpl H0 fvQ.
          eapply (agree_on_incl (lv:= Ds')); cset_tac; eauto.
        + pose proof (combineenv_eqr F Q' Ds' Es Et).
          rewrite <- H; eauto.
          rwsimpl H1 fvQ'.
          eapply (agree_on_incl (lv:= Ds' ∩ Dt')); cset_tac; eauto.
          hnf; intros.
          destruct (H7 x) as [v Exv]; cset_tac; eauto.
          (* Es and Et agree on free variables *)
          assert ( Es x = Some v /\ Et x = Some v).
          * split.
            { pose proof (term_ssa_eval_agree L L s D (stmtGoto fs Xs) E Es).
              rwsimpl H0 H4; rewrite <- H4; cset_tac; eauto. }
            { pose proof (term_ssa_eval_agree L L t D' (stmtGoto ft Xt) E Et).
              rwsimpl H1 H4; rewrite <- H4; cset_tac; eauto. }
          * destruct H4 as [Esx Etx]; rewrite Esx, Etx; eauto.
      - unfold F;  simpl.
        (* Case_eq over guards *)
        case_eq (undefLift Xt); case_eq (undefLift Xs); simpl;
        unfold evalSpred; intros; simpl.
        + split; intros.
          * decide (labInc fs 1 = labInc ft 1); eauto.
            eapply n. destruct fs,ft. simpl in *.
            pose proof (labeq_incr). specialize (H10 n0 n1 e); eauto.
          * split.
            { pose proof (terminates_impl_evalList L L E s Es fs Xs ).
              destruct H8; eauto.
              eapply guardList_true_if_eval; eauto.
              pose proof (explist_combineenv_eql Xs Ds' Es Et (Some x)).
              destruct H9; cset_tac; eauto.
              pose proof (ssa_move_goto D L E s Es fs Xs).
              destruct H10 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
              inversion ssaRet.
              rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
              eapply sndSubset. rewrite <- H14. eapply H12; eauto. }
            { destruct if; isabsurd; econstructor; eauto. }
        + split; intros.
          * decide (labInc fs 1 = labInc ft 1); eauto.
            eapply n. destruct fs,ft. simpl in *.
            pose proof (labeq_incr). specialize (H10 n0 n1 e); eauto.
          * destruct if; isabsurd; econstructor; eauto.
         + split; intros.
          * decide (labInc fs 1 = labInc ft 1); eauto.
            eapply n. destruct fs,ft. simpl in *.
            pose proof (labeq_incr). specialize (H9 n0 n1 e); eauto.
          * split.
            { pose proof (terminates_impl_evalList L L E s Es fs Xs ).
              destruct H8; eauto.
              eapply guardList_true_if_eval; eauto.
              pose proof (explist_combineenv_eql Xs Ds' Es Et (Some x)).
              destruct H9; cset_tac; eauto.
              pose proof (ssa_move_goto D L E s Es fs Xs).
              destruct H10 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
              inversion ssaRet.
              rewrite H0 in fstSubset, sndSubset; cset_tac; simpl in *.
              eapply sndSubset. rewrite <- H14. eapply H12; eauto. }
            { destruct if; isabsurd; econstructor; eauto. }
         + split; intros.
           * decide (labInc fs 1 = labInc ft 1); eauto.
            eapply n. destruct fs,ft. simpl in *.
            pose proof (labeq_incr). specialize (H9 n0 n1 e); eauto.
          * destruct if; isabsurd; econstructor; eauto. }
(* s terminiert & t crasht *)
- pose proof (terminates_impl_models L  s D E s' Es H2 H5 sterm).
  assert (forall x, x ∈ fst(getAnn D') -> exists v, E x = Some v).
  + intros. destruct (H7 x); eauto. rewrite H1 in H9; eauto.
  + pose proof (crash_impl_models L L D' t E Et t' H3 H9 H6 tcrash (fun _ => fun _ => true)).
    pose proof (combineenv_agree Ds' Es Et).
    specialize (H (fun _ => fun _ => true) (combineEnv Ds' Es Et)).
    exfalso. apply H. simpl. split.
    * eapply models_agree; eauto.
      eapply (agree_on_incl (lv:= Ds' )); eauto.
      eapply (freeVars_incl s D Df Ds'); eauto.
      rewrite H0; reflexivity.
    * pose proof (freeVars_incl t D' Df Dt' target H3 H6).
      rewrite <- combineenv_eqr; eauto.
      eapply (agree_on_incl (lv:= Dt' ∩ Ds')).
      { hnf; intros. rewrite <- H4 in H7.
        destruct (H7 x )  as [v  Ex];
         cset_tac; eauto.
        assert (Es x = Some v).
        - pose proof (term_ssa_eval_agree L L s D s' E Es).
          rewrite <- H13; eauto. rewrite H0; simpl; cset_tac; eauto.
        - assert (Et x = Some v).
          + pose proof (crash_ssa_eval_agree L L t D' t' E Et).
            rewrite <- H15; eauto; rewrite H1; simpl; cset_tac; eauto.
          + rewrite H13, H15; eauto. }
      { cset_tac; eauto.
         eapply H12; eauto. rewrite H1; reflexivity. }
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
