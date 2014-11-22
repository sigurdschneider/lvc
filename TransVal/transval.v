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

Lemma star2_nofun:
forall E s Es s',
noFun s
-> Terminates (nil, E, s) (nil, Es, s')
-> star2 F.step  (nil, E, s) nil (nil, Es, s') /\
   ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtGoto f X)).

Proof.
intros. general induction H0; eauto.
- split.
  + econstructor.
  + left. exists e. reflexivity.
- split.
  + econstructor.
  + right; exists f; exists x; reflexivity.
- inversion H2.
  + rewrite <- H4 in *.  inversion H2.
    exploit IHTerminates; try reflexivity.  instantiate (1:=s); eauto. instantiate (1:= E').
    inversion H; eauto.
    destruct X; split.
    * admit. (*eapply S_star2.*)
    * admit.
  + admit.
  + admit.
  + admit.
Qed.

Lemma crash_impl_sim:
forall (E:onv val) s Es s' t,
Crash (nil, E, s) (nil, Es, s')
-> @sim _ statetype_F _ statetype_F (nil, E, s) (nil, E, t).

Proof.
intros E s Es s'  t crash.
general induction crash.
- eapply simErr.
  + instantiate (1:=(nil,E0,s0)). assumption.
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
forall  E et es e e' P,
evalSexp E et = e
-> evalSexp E es = e'
-> (forall F E, models F E P)
-> (forall (F:lab->vallst->bool) E,
      models F E P ->
      ~ ((True -> F (LabI 0) (evalSexp E et :: nil) -> False) /\
        True /\ F (LabI 0) (evalSexp E es :: nil)))
-> (e = e').

Proof.
intros. decide (e = e').
- assumption.
- specialize (H1 (fun _ => fun x => toBool (bvEq e' (hd (O::nil) x))) E).
  specialize (H2 (fun _ => fun x => toBool (bvEq e' (hd (O::nil) x))) E).
  specialize (H2 H1).
  rewrite H in H2.  rewrite H0 in H2. exfalso.
  eapply H2. simpl.
  pose proof (bvEq_equiv_eq e' e).
  rewrite H3.
  split; try split; eauto.
  eapply bvEq_refl.
Qed.

Lemma exp_combineenv_eq:
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

  Lemma explist_combineenv_eq:
forall el D Es Et rl,
list_union (List.map Exp.freeVars el) ⊆ D
-> evalList (combineEnv D Es Et) el = rl
-> evalList Es el = rl.

Proof.
intros.  general induction el.
- simpl. reflexivity.
- simpl. simpl in H. hnf in H. unfold evalSexp.
  rewrite (exp_combineenv_eq a D Es Et (exp_eval (combineEnv D Es Et) a)); eauto.
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
    * pose proof (exp_combineenv_eq e D Es Et (Some v) H1 H0).
      rewrite H2. destruct (val2bool v).
      { rewrite (IHs1 F D Es Et).
        + reflexivity.
        + setSubst H; left; left; assumption.
      }
      { rewrite (IHs2 F D Es Et).
        + reflexivity.
        + setSubst H; left; right; assumption.
      }
  + assert (Exp.freeVars e ⊆ D).
    * setSubst H; right; assumption.
    * pose proof (exp_combineenv_eq e D Es Et None H1 H0).
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
      pose proof (exp_combineenv_eq e D Es Et (Some v) H2 H0);
      pose proof (exp_combineenv_eq e0 D Es Et (Some v0) H3 H1);
      rewrite H4; rewrite H5;
      reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq e D Es Et (Some v) H2 H0);
    pose proof (exp_combineenv_eq e0 D Es Et None H3 H1).
    rewrite H4; rewrite H5; reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq e D Es Et None H2 H0);
    pose proof (exp_combineenv_eq e0 D Es Et (Some v) H3 H1).
    rewrite H4; rewrite H5; reflexivity.
  + destruct H2.
    pose proof (exp_combineenv_eq e D Es Et None H2 H0);
    pose proof (exp_combineenv_eq e0 D Es Et None H3 H1).
    rewrite H4; rewrite H5; reflexivity.
- unfold evalSpred.
  pose proof (explist_combineenv_eq a D Es Et (evalList (combineEnv D Es Et) a)).
  rewrite H0; eauto. reflexivity.
- unfold evalSexp.  simpl in H.
  case_eq (exp_eval (combineEnv D Es Et) e); intros.
  + pose proof (exp_combineenv_eq e D Es Et (Some v) H H0).
    rewrite H1. reflexivity.
  + pose proof (exp_combineenv_eq e D Es Et None H H0).
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
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
-  admit.
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
    exploit (star2_nofun  E s Es s' H5 sterm).
    exploit (star2_nofun E t Et t' H6 tterm).
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
        - intros. unfold P. admit.
        - intros.specialize (modTS F E0 H7). simpl in modTS.
          case_eq (undef es); case_eq (undef et); intros.
          + rewrite H8 in modTS; rewrite H9 in modTS. simpl in modTS.
            admit.
          + admit.
          + admit.
          + admit.
      }
      { assumption. }
      { assumption. }
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
           + rewrite <- (H H7); eauto.
       }
       { case_eq (undef es); case_eq (undefLift Xt); intros; simpl.
         - (* assert that guards are true *)
           assert (models F E' s1).
           + eapply (guardTrue_if_Terminates_ret _ s); eauto.
             instantiate (1:= E).
             (* Lemma dass wenn freeVars Q ⊆ D \ (Ds ∩ Dt) --> Es sonst Et *)
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
             (* analoges rewrite Lemma *)             admit.
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
*)