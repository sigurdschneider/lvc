Require Import List Arith.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util.
Require Import SetOperations Sim Var.
Require Import sexp smt nofun noGoto Terminates bitvec Crash freeVars.
Require Import tvalTactics TUtil Guards.

Lemma term_ssa_eval_agree L L' s D s' (E:onv val) (E':onv val)
 : ssa s D
   -> noFun s
   -> Terminates (L, E, s) (L', E', s')
   -> agree_on eq (fst (getAnn D)) E E'.

Proof.
  intros.
  general induction H1; invt ssa; try invt F.step;try invt noFun; simpl;
  try reflexivity; isabsurd.
  - exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
   rewrite H7 in X; simpl in *. cset_tac; intuition.
   hnf. hnf in X. intros.
   unfold update in X. specialize (X x0).
   assert (x0 ∈ D0 ++ {x; {}}) by (cset_tac; left; assumption).
   specialize (X H10). decide (x === x0); eauto.
    + rewrite  <- e0 in H8; exfalso; apply H4 ; assumption.
  - exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H9 in X; simpl in *. assumption.
  - exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
    rewrite H10 in X; simpl in *; assumption.
Qed.

Lemma terminates_impl_star2:
  forall L E s L' Es s',
    noFun s
    -> Terminates (L, E ,s ) (L', Es, s')
    -> (star2 F.step (L, E, s) nil (L', Es, s'))
       /\ ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtGoto f X)).

Proof.
intros.
general induction H0; eauto.
-split; eauto; econstructor.
- split; eauto; econstructor.
- inversion H2; subst; try isabsurd.
  + exploit (IHTerminates L' E' s'); try reflexivity.
    * inversion H; subst; eauto.
    * destruct X as [step X]; split.
      { change (star2 F.step (L0, E0, stmtExp x e s) (filter_tau EvtTau nil) (L'0, Es, s'0)).
        econstructor; eauto. destruct a; eauto; isabsurd. }
      { destruct X; eauto. }
  + exploit (IHTerminates L' E' s'); eauto.
    * inversion H; subst; eauto.
    * destruct X as [step X]; split.
      { change (star2 F.step (L0, E0, stmtIf e s t)(filter_tau EvtTau nil) (L'0, Es, s'0)).
        econstructor; eauto; destruct a; eauto; isabsurd. }
      {destruct X; eauto. }
Qed.

Lemma terminates_impl_models :
forall L s D E s' E',
ssa  s D
-> noFun s
-> Terminates (L,E, s) (L, E', s')
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
      { eapply (term_ssa_eval_agree L' L' (stmtExp x e s') _ s'0 _ _);
        econstructor; eauto. }
      { eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
    * split; eauto; subst.
      assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0[x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))); subst.
          + eapply (term_ssa_eval_agree L' L' s' _ s'0 _ E'0); eauto.
          + rewrite H11. unfold fst. cset_tac. right; rewrite H6; reflexivity.
        - unfold exp_eval. unfold update. decide (x===x); eauto; isabsurd. }
      assert (X2: exp_eval E'0 e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
        - eapply (term_ssa_eval_agree L' L' (stmtExp x e s') _ s'0 _ _);
          econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold evalSexp. rewrite X1; rewrite X2.
         eapply  bvEq_equiv_eq. reflexivity. }
    * assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0 [x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))).
          + eapply (term_ssa_eval_agree L' L' s' _ s'0 _ _); eauto.
          + rewrite H11. unfold fst. cset_tac. right; rewrite H6; reflexivity.
        - unfold exp_eval. unfold update. decide (x===x); eauto; isabsurd. }
      assert (X2: exp_eval E'0 e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
        - eapply (term_ssa_eval_agree  L' L' (stmtExp x e s') _ s'0);
          econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold evalSexp. rewrite X1; rewrite X2.
         eapply  bvEq_equiv_eq. reflexivity.  }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'0 ( ite e (translateStmt s' source) (translateStmt b2 source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
        by (hnf; intros; hnf in H7; specialize (H7 a); exact (H7 H4)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (term_ssa_eval_agree L' L' (stmtIf e s' b2) _ s'0 _ _); econstructor; eauto).
      erewrite (exp_eval_agree (E:=E') (E':=E'0)); eauto. simpl. rewrite condTrue.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e _ v); eauto.
          assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
            by (hnf; intros; hnf in H7; specialize (H7 a); hnf; cset_tac; simpl;  exact (H7 H5)).
          assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
            by ( eapply (term_ssa_eval_agree L' L' (stmtIf e s' b2) _ s'0 _ _); econstructor; eauto).
          eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
          eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + assert (X: models  (fun (_:pred) (_:vallst) => true) E'0( ite e (translateStmt b1 source) (translateStmt s' source))).
    * simpl. unfold evalSexp.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
        by (hnf; intros; hnf in H7; specialize (H7 a); exact (H7 H4)).
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
      by ( eapply (term_ssa_eval_agree L' L' (stmtIf e b1 s') _ s'0 _ _);econstructor;  eauto).
      erewrite (exp_eval_agree (E:=E') (E':=E'0)); eauto. simpl. rewrite condFalse.
      eapply IHTerminates; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
    * case_eq (undef e); intros; eauto.
      { simpl; split; eauto.
        - eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e _ v); eauto.
          + assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant)))
              by (hnf; intros; hnf in H7; specialize (H7 a); hnf; cset_tac; simpl;  exact (H7 H5)).
            assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
              by ( eapply (term_ssa_eval_agree L' L' (stmtIf e b1 s') _ s'0 _ _); econstructor; eauto).
            eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
            eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      }
 + specialize (H0 l Y); isabsurd.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)