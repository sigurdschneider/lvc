Require Import List Arith.
Require Import AutoIndTac Annotation Exp IL MoreExp RenamedApart Util.
Require Import SetOperations Sim.
Require Import bitvec smt nofun freeVars.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil GuardProps.

(*
(** TODO Remove as unused **)
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
   + specialize (IHel E x0 EQ1). specialize (IHel e).
     simpl in H0.  destruct H0.
     * exfalso. apply n. rewrite H; reflexivity.
     * destruct (IHel H).  exists x1.
       rewrite H0. reflexivity.
Qed. *)

(** Lemma 2 in Thesis
Proves that Terminates ignores the label environment **)
Lemma term_swap_fun L1 L2 L1'  V V' s s':
Terminates (L1,V,s) (L1',V',s')
-> exists L2', Terminates (L2, V, s) (L2', V', s').

Proof.
intros term. general induction term.
- eexists; econstructor;  eauto.
- eexists; econstructor; eauto.
- inversion H.
  + specialize (IHterm L' L2 L1' E' V' s' s'0).
  destruct IHterm as [L2'  IHterm]; eauto.
  eexists; econstructor; eauto. instantiate (1:=a).
    * rewrite <- H7.  subst. econstructor; eauto.
    * intros; isabsurd.
  + specialize (IHterm L' L2 L1' E' V' s' s'0).
  destruct IHterm as [L2'  IHterm]; eauto.
 eexists; econstructor; eauto.
    instantiate (1:=EvtTau); subst.
    * econstructor; eauto.
    * intros; isabsurd.
  + specialize (IHterm L' L2 L1' E' V' s' s'0).
  destruct IHterm as [L2'  IHterm]; eauto.
  eexists; econstructor; eauto.
  instantiate(1:=EvtTau); subst.
    * econstructor; eauto.
    * intros; isabsurd.
  + subst. specialize (H0 l Y); isabsurd.
  + subst. exploit IHterm; eauto.
    edestruct H1 as [L2' ?].
    eexists. econstructor; eauto.
    econstructor; eauto.
  + subst. edestruct IHterm as [L2' IHterm']; eauto.
    eexists; econstructor; eauto.
    econstructor; eauto.
Qed.

(** Part 1 of Lemma 1 in the Thesis **)
Lemma term_ssa_eval_agree L L' s D s' (E:onv val) (E':onv val)
 : renamedApart s D
   -> noFun s
   -> Terminates (L, E, s) (L', E', s')
   -> agree_on eq (fst(getAnn D)) E E'.

Proof.
  intros.
  general induction H1; invt renamedApart; try invt F.step;try invt noFun; simpl;
  try reflexivity.
  - exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H8 in H9; simpl in *. cset_tac.
    hnf in *. intros x0 inD0.
    specialize (H9 x0).
    assert (x0 ∈ {x; D0}) by (cset_tac; left; assumption).
   specialize (H9 H11). unfold update in H9. cases in H9; eauto.
  - exploit IHTerminates; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H9 in H11; simpl in *. assumption.
  - exploit IHTerminates; [| | reflexivity | reflexivity |]; eauto.
    rewrite H10 in H11; simpl in *; assumption.
  - specialize (H0 f Y); isabsurd.
Qed.

Lemma terminates_impl_star2:
  forall L E s L' Es s',
    noFun s
    -> Terminates (L, E ,s ) (L', Es, s')
    -> (star2 F.step (L, E, s) nil (L', Es, s'))
       /\ ((exists e, s' = stmtReturn e) \/ (exists f X, s' = stmtApp f X)).

Proof.
  intros L E s L' Es s' noFun_s Terminates_s.
  general induction Terminates_s.
  - split; eauto; econstructor.
  - split; eauto; econstructor.
  - inversion noFun_s; subst; try isabsurd.
    + exploit (IHTerminates_s L' E' s'); try reflexivity.
      * inversion H; subst; eauto.
      * destruct H2 as [step H2]; split.
        { change (star2 F.step (L0, E0, stmtLet x e s) (filter_tau EvtTau nil) (L'0, Es, s'0)).
          econstructor; eauto. destruct a; eauto; isabsurd. }
        { destruct H2; eauto. }
  + exploit (IHTerminates_s L' E' s'); eauto.
    * inversion H; subst; eauto.
    * destruct H3 as [step H3]; split.
      { change (star2 F.step (L0, E0, stmtIf e s t)(filter_tau EvtTau nil) (L'0, Es, s'0)).
        econstructor; eauto; destruct a; eauto; isabsurd. }
      {destruct H3; eauto. }
  + specialize (H0 l Y); isabsurd.
Qed.

(** Lemma 13 in Thesis
Proves that all terminating source translations can be modeled
with the end environment **)
Lemma terminates_impl_models :
forall L s D E s' E',
renamedApart s D
-> noFun s
-> Terminates (L,E, s) (L, E', s')
->  models (fun (f:pred) (x:vallst) => true)  (to_total E')  (translateStmt s source).

Proof.
intros L s D E s' E' ren_s noFun_s Term_s.
general induction Term_s; simpl.
- assert (X: models (fun (_:pred) (_:vallst) => true) (to_total E0) (funcApp (LabI 0) (e::nil))).
  + simpl; intuition.
  + eapply models_guardGen_source; simpl. split; eauto.
      eapply (guard_true_if_eval); eauto.
- eapply models_guardGen_source; simpl; split; eauto.
  eapply (guardList_true_if_eval _ E0); eauto.
- inv H; invt renamedApart; invt noFun; simpl in * |- *; subst.
  + eapply models_guardGen_source; simpl; split; eauto.
    * eapply (guard_true_if_eval _ E'0 e v ); eauto.
      eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
      { eapply (term_ssa_eval_agree L' L' (stmtLet x e s') _ s'0 _ _);
        econstructor; eauto. }
      { eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
    * split; eauto; subst.
      assert (X1: exp_eval E'0 (Var x) = Some v).
      { eapply (exp_eval_agree (E:= E0[x <- Some v])) ; eauto.
        - simpl. eapply (agree_on_incl (bv:={x} ) (lv:= fst (getAnn an))); subst.
          + eapply (term_ssa_eval_agree L' L' s' _ s'0 _ E'0); eauto.
          + rewrite H9. unfold fst. cset_tac.
        - unfold exp_eval. unfold update. decide (x===x); eauto; isabsurd. }
      assert (X2: exp_eval E'0 e = Some v).
      { eapply exp_eval_agree; eauto.
      assert (A: agree_on eq (fst (getAnn (ann1 (D0, D') an))) E0 E'0).
        - eapply (term_ssa_eval_agree L' L' (stmtLet x e s') _ s'0 _ _);
          econstructor; eauto.
        - eapply (agree_on_incl  (bv:=Exp.freeVars e) (lv:=fst (getAnn (ann1 (D0, D') an)))); eauto. }
      {  unfold smt_eval;
        repeat erewrite exp_eval_partial_total; eauto.
         eapply  bvEq_equiv_eq; reflexivity. }
  + assert (X: models  (fun (_:pred) (_:vallst) => true) (to_total E'0) ( ite e (translateStmt s' source) (translateStmt b2 source))).
    * simpl.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by cset_tac.
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (term_ssa_eval_agree L' L' (stmtIf e s' b2) _ s'0 _ _); econstructor; eauto).
      unfold smt_eval.
      erewrite (exp_eval_agree (E:=to_partial (to_total E')) (E':=to_partial (to_total E'0))); eauto.
      { erewrite exp_eval_partial_total; eauto.
        rewrite condTrue.
        eapply IHTerm_s; eauto. }
      { eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
        simpl.
        eapply agree_on_partial; eauto.
        eapply agree_on_total; eauto. }
    * erewrite models_guardGen_source.
      simpl.
      pose proof (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e v); eauto.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by cset_tac.
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (term_ssa_eval_agree L' L' (stmtIf e s' b2) _ s'0 _ _); econstructor; eauto).
      assert (exp_eval E'0 e = Some v)
        by (eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto;
        eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto).
      split; eauto.
  + assert (X: models  (fun (_:pred) (_:vallst) => true) (to_total E'0) ( ite e (translateStmt b1 source) (translateStmt s' source))).
    * simpl.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by cset_tac.
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
      by ( eapply (term_ssa_eval_agree L' L' (stmtIf e b1 s') _ s'0 _ _);econstructor;  eauto).
      unfold smt_eval.
      erewrite (exp_eval_agree (E:=to_partial (to_total E')) (E':=to_partial (to_total E'0))); eauto. simpl.
      erewrite exp_eval_partial_total; eauto.
      rewrite condFalse.
      eapply IHTerm_s; eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
      eapply agree_on_partial, agree_on_total; eauto.
    * erewrite models_guardGen_source; simpl.
      simpl; split; eauto.
      eapply (guard_true_if_eval  (fun (_:pred) (_:vallst) => true) E'0 e v); eauto.
      assert (Exp.freeVars e ⊆ fst (getAnn (ann2 (D0, D') ans ant))) by cset_tac.
      assert (agree_on eq (fst (getAnn (ann2 (D0, D') ans ant))) E' E'0)
        by ( eapply (term_ssa_eval_agree L' L' (stmtIf e b1 s') _ s'0 _ _);
             econstructor; eauto).
      eapply (exp_eval_agree (E:=E') (E':=E'0)); eauto.
      eapply (agree_on_incl (bv:= Exp.freeVars e) (lv:= fst (getAnn (ann2 (D0, D') ans ant)))); eauto.
 + specialize (H0 l Y); isabsurd.
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
    * specialize (H1 l Y); isabsurd.
  + inversion H; subst; eauto; isabsurd. specialize (H1 l Y); isabsurd.
Qed.

Lemma terminates_impl_evalList:
forall L  L' E s E' f el,
noFun s
-> Terminates (L, E, s) (L', E', stmtApp f el)
-> exists v, omap (exp_eval E') el = Some v.

Proof.
intros. general induction H0.
- exists vl; eauto.
- exploit (IHTerminates L0 L'0 E' s' E'0 f el); eauto.
  + inversion H2; subst; inversion H; subst; eauto; isabsurd.
    specialize (H1 l Y); isabsurd.
  + inversion H; subst; eauto; isabsurd.
    specialize (H1 l Y); isabsurd.
Qed.

(** Lemma cannot be proven with star2 step because in the
goto case, ssa is not proven! **)
Lemma ssa_move_return:
  forall D (L:F.labenv) E s E' e,
    noFun s
    -> renamedApart s D
    -> Terminates (L, E, s) (L, E', stmtReturn e)
    -> exists D', renamedApart (stmtReturn e) D'
                  /\ fst (getAnn D) ⊆ fst (getAnn D')
                  /\ snd (getAnn D') ⊆ snd (getAnn D).

Proof.
  intros. general induction H1; invt renamedApart; invt noFun; try invt F.step.
  - eexists. split; eauto.
  - edestruct (IHTerminates an L' (E0[x<-Some v]) s' ); eauto; dcr.
    pe_rewrite. simpl. eexists; split; eauto.
    rewrite H7. split; eauto with cset.
    rewrite <- H13. eauto with cset.
  - edestruct (IHTerminates ans); eauto; dcr.
    eexists; split; eauto. simpl.
    rewrite <- H6. pe_rewrite.
    rewrite H16, H17. eauto with cset.
  - edestruct IHTerminates; eauto; dcr.
    pe_rewrite. simpl.
    eexists; split; eauto.
    rewrite <- H6. eauto with cset.
  - exfalso. eapply H0; eauto.
Qed.

(** See Lemma before **)
Lemma ssa_move_goto:
  forall D (L:F.labenv) E s E' f el,
    noFun s
    -> renamedApart s D
    -> Terminates (L, E, s) (L, E', stmtApp f el)
    -> exists D', renamedApart (stmtApp f el) D'
                  /\ fst (getAnn D) ⊆ fst (getAnn D')
                  /\ snd (getAnn D') ⊆ snd (getAnn D).

Proof.
  intros D L E s E' f el nfS ssaS sterm.
  general induction sterm; invt renamedApart; invt noFun; try invt F.step.
  - eexists; eauto.
  - edestruct (IHsterm an L' (E0[x<-Some v]) s' ); eauto; dcr.
    pe_rewrite. simpl. eexists; split; eauto.
    rewrite H4. split; eauto with cset.
    rewrite <- H10. eauto with cset.
  - edestruct (IHsterm ans); eauto; dcr.
    eexists; split; eauto. simpl.
    rewrite <- H3. pe_rewrite.
    rewrite H13, H14. eauto with cset.
  - edestruct IHsterm; eauto; dcr.
    pe_rewrite. simpl.
    eexists; split; eauto.
    rewrite <- H3. eauto with cset.
  - exfalso. eapply H0; eauto.
Qed.

(** Lemmata for Crash **)

Definition failed (s:F.state)  := result (s ) = None.

(** Lemma 3 in the thesis
Proves that Crashing is independent from the function environment **)
Lemma crash_swap_fun L1 L2 L1' V V' s s':
Crash (L1, V, s) (L1', V', s')
-> exists L2', Crash (L2, V, s) (L2', V', s').

Proof.
  intros crash; general induction crash.
  - eexists; econstructor; eauto.
  - eexists; econstructor; eauto.
    unfold normal2 in *.
    hnf. intros. eapply H0.
    unfold reducible2 in *.
    destruct H2; destruct H2.
    inversion H2; try isabsurd.
    + exists EvtTau. exists ( L1, V[x1 <- Some v], b). econstructor; eauto.
    + exists EvtTau; exists (L1, V, b1); econstructor; eauto.
    + exists EvtTau; exists (L1, V, b2); econstructor; eauto.
    + subst. specialize (H l Y); isabsurd.
    + exists EvtTau.
      eexists. econstructor.
    + exists x; subst.
        exists (L1, V[x1 <- Some v], s).
        econstructor; eauto.
   - inversion H; subst.
     + specialize (IHcrash L1 L2 L1' (V[x<-Some v]) V' b s').
       destruct IHcrash; eauto.
       eexists; econstructor; eauto.
       * instantiate (1:= EvtTau); econstructor; eauto.
     + specialize (IHcrash L1 L2 L1' V V' b1 s').
       destruct IHcrash; eauto.
       eexists; econstructor; eauto.
       * instantiate (1:=EvtTau); econstructor; eauto.
     + specialize (IHcrash L1 L2 L1' V V' b2 s').
       destruct IHcrash; eauto.
       eexists; econstructor; eauto.
       * instantiate (1:=EvtTau); econstructor; eauto.
     + specialize (H0 l Y); isabsurd.
     + edestruct IHcrash; eauto.
       eexists; econstructor; eauto.
       * instantiate (2:= EvtTau); econstructor; eauto.
     + specialize (IHcrash  L1 L2 L1' (V[x<-Some v]) V' s s').
       destruct IHcrash; eauto.
       eexists; econstructor; eauto.
       * instantiate (1:=EvtExtern {| extern_fnc := f; extern_args := vl; extern_res := v |}); subst; econstructor; eauto.
Qed.

(** Part 2 of Lemma 1 in the Thesis *)
Lemma crash_ssa_eval_agree L L' s D s' (E:onv val) (E':onv val)
: renamedApart s D
  ->noFun s
  -> Crash (L, E, s) (L', E', s')
  -> agree_on eq (fst (getAnn (D))) E E'.

Proof.
  intros.
  general induction H1; invt renamedApart; try invt F.step; try invt noFun; simpl;
  try reflexivity.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H8 in H9; unfold update in H9.
    simpl in *. hnf; hnf in H9; intros x0 inD0.
    specialize (H9 x0).
    assert (x0 ∈ {x; D0}) by cset_tac.
    specialize (H9 H11); cases in H9; eauto.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H9 in H11; eauto.
  - exploit IHCrash; [ | | reflexivity | reflexivity |]; eauto.
    rewrite H10 in H11; eauto.
  - specialize (H0 f Y); isabsurd.
Qed.

Lemma crash_impl_err:
  forall (E:onv val) s Es s' L L',
    noFun s
    -> Crash (L, E, s) (L', Es, s')
    -> ( star2 F.step (L,E,s) nil (L', Es, s'))
       /\ normal2 F.step (L', Es, s') /\ failed (L', Es, s').

Proof.
  intros E s Es s' L L' nf Crash.
  general induction Crash.
  - split; econstructor.
    +  hnf. intros. destruct H0. destruct H0. inversion H0.
       rewrite H in def; isabsurd.
    + unfold failed; eauto.
   - split; eauto;  econstructor.
- destruct sigma'. destruct p. inversion nf; subst; try isabsurd.
  + exploit (IHCrash o s1 Es s' l L') ; try reflexivity; eauto; subst.
    * inversion H; eauto.
    * destruct H2; split; eauto.
      change (star2 F.step (L0, E0, stmtLet x e s1) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto. destruct a; eauto; isabsurd.
  + inversion H; exploit (IHCrash o s Es s' l L'); subst; eauto.
    * split; eauto.
      change (star2 F.step (l, o, stmtIf e s t) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto.
    * split; eauto.
      change (star2 F.step (l, o, stmtIf e s1 s) (filter_tau EvtTau nil) (L', Es, s')).
      econstructor; eauto.
  + specialize (H0 l0 Y); isabsurd.
Qed.

Lemma nostep_let:
forall L E x e s,
normal2 F.step (L, E, stmtLet x e s)
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

(** Lemma 11 in the thesis
Proves that crashing target programs can be modeled by any
predicate environment and the environment in which they crash **)
Lemma crash_impl_models:
  forall L L' D s E Es s',
    renamedApart s D
    -> (forall x, x ∈ fst(getAnn D) -> exists v, E x = Some v)
    -> noFun s
    -> Crash (L, E, s) (L', Es, s')
    -> forall F, models F (to_total Es) (translateStmt s target).

Proof.
  (** induction over Crash **)
  intros. general induction H2; simpl.
  (** C-Goto **)
  - eapply models_guardGen_target.
    simpl; intros.
    pose proof (undefList_models F E0 Y).
    eapply H5; eauto.
    intros. eapply H1.
    inversion H0; simpl; eauto.
    (** C-Base **)
  - inversion H4; subst; simpl; eapply models_guardGen_target; simpl; intros; try isabsurd.
    (** let Statement **)
    +pose proof (nostep_let L0 E0 x e s H0).
        pose proof (undef_models F  E0 e).
        assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
     * intros; invt renamedApart. specialize (H3 x0). eapply H3.
       simpl; cset_tac; eauto.
      (** Contradiction: The expression does not evaluate, but the guard
       is satisfiable --> undef_models as contradiction **)
     * specialize(H8 H9 H7 H6); isabsurd.
       (** conditional **)
    + pose proof (nostep_if L0 E0 e s t H0).
      pose proof (undef_models F  E0 e).
     assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
     * intros; invt renamedApart. eapply (H3 x). simpl; cset_tac; eauto.
       (** Same contradiction **)
     * specialize (H9 H10 H8 H7); isabsurd.
    + pose proof (undef_models F E0 e).
         assert (forall x, x ∈ Exp.freeVars e -> exists v, E0 x = Some v).
        { intros; inversion H2; cset_tac. }
        { eapply H7; eauto. }
       (** C-Step **)
  - destruct sigma' as  [[L E'] sc].
    inversion H; intros; subst; try isabsurd;
    invt renamedApart; invt noFun; subst; simpl;
    eapply models_guardGen_target; simpl; intros.
    + split.
     Focus 2.
     exploit (IHCrash L L' an sc (E0 [x<-Some v]) Es s'); eauto; intros.
     unfold update. cases; eauto.
     destruct (H3 x0); eauto; simpl.
     rewrite H13 in H7; simpl in H7. cset_tac.
    * assert ( exp_eval Es e = Some v /\ exp_eval Es (Var x) = Some v).
    { split.
      - eapply (exp_eval_agree (E:=E0)); eauto.
        hnf. intros.  hnf in H9. specialize (H9 x0 H7).
        eapply (crash_ssa_eval_agree L L' (stmtLet x e sc) (ann1 (D0, D') an) s' E0 Es);
          eauto; econstructor; eauto.
      - eapply (exp_eval_agree (E:= E0[x<-Some v])).
        + hnf. intros; simpl in *.
          eapply (crash_ssa_eval_agree L L' sc an s' (E0[x<-Some v]) Es); eauto.
          rewrite H13; simpl. cset_tac.
        + simpl. unfold update. cases; eauto; isabsurd.
          }
    { destruct H7.
      unfold smt_eval.
      repeat erewrite exp_eval_partial_total; eauto.
      eapply bvEq_equiv_eq; eauto. }
    +  unfold smt_eval.
       assert (exp_eval Es e = Some v).
       * eapply (exp_eval_agree (E:= E')); eauto.
         hnf; intros.  hnf in H8.  specialize (H8 x H6).
         pose proof (crash_ssa_eval_agree L L' (stmtIf e sc b2) (ann2 (D0, D') ans ant) s'  E' Es).
         eapply H13; eauto; econstructor; eauto.
       * unfold smt_eval; erewrite exp_eval_partial_total; eauto.
         rewrite condTrue.
         eapply (IHCrash L L' ans sc E' Es s'); eauto.
         intros. rewrite H14 in H13. simpl in *; eauto.
    + unfold smt_eval.
       assert (exp_eval Es e = Some v).
       * eapply (exp_eval_agree (E:= E')); eauto.
         hnf; intros.  hnf in H8.  specialize (H8 x H6).
         pose proof (crash_ssa_eval_agree L L' (stmtIf e b1 sc) (ann2 (D0, D') ans ant) s'  E' Es).
         eapply H13; eauto; econstructor; eauto.
       * unfold smt_eval; erewrite exp_eval_partial_total; eauto.
         rewrite condFalse.
         eapply (IHCrash L L' ant sc E' Es s'); eauto.
         intros. rewrite H15 in H13. simpl in *; eauto.
    + apply (H0 l Y); auto.
Qed.