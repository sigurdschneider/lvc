Require Import List Arith.
Require Import IL Annotation AutoIndTac Exp MoreExp RenamedApart Fresh Util.
Require Import SetOperations Sim Var.
Require Import bitvec smt nofun freeVars CombineEnv.
Require Import Compute Guards ILFtoSMT tvalTactics TUtil GuardProps ComputeProps.

(** Function Definitions **)

Definition smtCheck (s:stmt) (t:stmt) :=
smtAnd (translateStmt s source) (translateStmt t target).

(** Lemmata **)
Lemma freeVars_incl:
  forall s D p,
    renamedApart s D
    -> noFun s
    -> freeVars (translateStmt s p) ⊆ (fst (getAnn D) ∪ (snd (getAnn D))).

Proof.
  intros s D p ssaS nfS.
  general induction nfS; inv ssaS; subst; simpl.
  - specialize (IHnfS an p H4).
    rewrite H7 in IHnfS; simpl in IHnfS.
    destruct p.
    + unfold guardGen.
      cases; simpl; cset_tac.
      * right; rewrite (H6 a); auto.
      * specialize (IHnfS a H0).
        cset_tac.
        { right; rewrite (H6 a); auto. }
        { right; rewrite (H6 a); auto. }
      * eapply (freeVars_undef) in H0.
        left; apply H3; auto.
      * right; rewrite (H6 a); auto.
      * specialize (IHnfS a H).
        cset_tac.
        { right; rewrite (H6 a); auto. }
        { right; rewrite (H6 a); auto. }
    + unfold guardGen.
      cases; simpl; cset_tac.
      * right; rewrite (H6 a); auto.
      * specialize (IHnfS a H0).
        cset_tac.
        { right; rewrite (H6 a); auto. }
        { right; rewrite (H6 a); auto. }
      * eapply (freeVars_undef) in H0.
        left; apply H3; auto.
      * right; rewrite (H6 a); auto.
      * specialize (IHnfS a H).
        cset_tac.
        { right; rewrite (H6 a); auto. }
        { right; rewrite (H6 a); auto. }
  - specialize (IHnfS1 ans p H5).
    specialize (IHnfS2 ant p H6).
    rewrite H8 in IHnfS1; rewrite H9 in IHnfS2; simpl in *.
    destruct p.
    + unfold guardGen.
      cases; simpl; cset_tac.
      * specialize (IHnfS1 a H); cset_tac.
        right; rewrite <- (H4 a); auto.
      * specialize (IHnfS2 a H); cset_tac.
        right; rewrite <- (H4 a); auto.
      * eapply freeVars_undef in H0.
        left; apply H2; auto.
      * specialize (IHnfS1 a H0); cset_tac.
        right; rewrite <- (H4 a); auto.
      * specialize (IHnfS2 a H0); cset_tac.
        right; rewrite <- (H4 a); auto.
    + unfold guardGen; cases; simpl; cset_tac.
           * specialize (IHnfS1 a H); cset_tac.
        right; rewrite <- (H4 a); auto.
      * specialize (IHnfS2 a H); cset_tac.
        right; rewrite <- (H4 a); auto.
      * eapply freeVars_undef in H0.
        left; apply H2; auto.
      * specialize (IHnfS1 a H0); cset_tac.
        right; rewrite <- (H4 a); auto.
      * specialize (IHnfS2 a H0); cset_tac.
        right; rewrite <- (H4 a); auto.
  - destruct p.
    + unfold guardGen; cases; simpl; cset_tac.
      eapply freeVars_undefLift in H0.
      left; apply H1; auto.
    + unfold guardGen; cases; simpl; cset_tac.
      eapply freeVars_undefLift in H0.
      left; apply H1; auto.
  - destruct p.
    + unfold guardGen; cases; simpl; cset_tac.
      eapply freeVars_undef in H2.
      left; apply H0; auto.
    + unfold guardGen; cases; simpl; cset_tac.
      eapply freeVars_undef in H2.
      left; apply H0; auto.
Qed.

(** Lemma 12 in the thesis
Formulas can be extended by a Q that represents the effects of
the program history
**)
Lemma unsat_extension L D E E' s s' pol P Q:
(forall F E, models F (to_total E) Q -> ~ models F (to_total E) (smtAnd (translateStmt s pol) P))
-> renamedApart s D
-> noFun s
-> Terminates (L, E, s) (L, E', s')
-> exists Q', (forall F, models F (to_total E')  Q' ) /\
              freeVars Q' ⊆  snd(getAnn D) ∪ fst(getAnn D) /\
              (forall F E, models F (to_total E) (smtAnd Q Q')
                           -> ~ models F (to_total E) (smtAnd (translateStmt s' pol) P)).
Proof.
  intros Q_impl_mod ssa_s noFun_s term_s.
  general induction term_s; destruct pol.
  - inversion ssa_s.
    exists smtTrue; simpl; cset_tac.
  - inversion ssa_s.
    exists smtTrue; simpl; cset_tac.
  - inversion ssa_s.
    exists smtTrue; simpl; cset_tac.
  - inversion ssa_s.
    exists smtTrue; simpl; cset_tac.
  - inv noFun_s.
    + inv H. inv ssa_s. specialize (IHterm_s L' an (E0 [x <- ⎣ v ⎦]) E'0 s' s'0 source).
      specialize (IHterm_s P (smtAnd Q (guardGen (undef e) source (constr (Var x) e)))).
      destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
      * intros F E mod_Q mod_P.
        specialize (Q_impl_mod F E).
        simpl in mod_Q.
        destruct mod_Q as [mod_Q mod_Constr].
        specialize (Q_impl_mod mod_Q).
        apply Q_impl_mod; simpl; simpl in mod_P; split; auto.
        apply models_guardGen_source; apply models_guardGen_source in mod_Constr.
        simpl in *; destruct mod_Constr, mod_P; split; try split; auto.
      * exists (smtAnd Q' (guardGen (undef e) source (constr (Var x) e))).
        destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
        split; try split; eauto.
        { apply models_guardGen_source; simpl; split.
          - eapply (guard_true_if_eval _ _ e v); eauto.
            eapply (exp_eval_agree (E:=E0)); eauto. hnf; intros.
            eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
          - unfold smt_eval.
            assert (exp_eval E'0 e = Some v).
            + eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros.
              eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
            + assert (exp_eval E'0 (Var x) = Some v).
              * eapply (exp_eval_agree (E:= E0[x <- Some v])).
                { hnf. intros. simpl in H4.
                  eapply (term_ssa_eval_agree L' L' s'); eauto.
                  rewrite H10; simpl; cset_tac. }
                { simpl. unfold update. cases; auto. }
              * rewrite (exp_eval_partial_total E'0 (Var x) H4).
                rewrite (exp_eval_partial_total E'0 e H2).
                eapply bvEq_equiv_eq; auto.
        }
        { rewrite H10 in fv_subset; simpl in *. cset_tac.
          - hnf in fv_subset. specialize (fv_subset a H4).
            specialize (H9 a). rewrite H9.
            cset_tac.
          - unfold guardGen in H4.
            cases in H4; simpl in *;
              rewrite (H9 a); cset_tac.
            + rewrite undef_vars_subset in H2. cset_tac.
        }
        { intros F E mod_Q_Q' mod_trans.
          apply (mod_impl_unsat F E); auto.
          - simpl in *.
            destruct mod_Q_Q' as [mod_Q [mod_E_Q' mod_constr]].
            split; try split; auto.
        }
    + inv H; inv ssa_s.
      * specialize (IHterm_s L' ans E' E'0 s' s'0 source).
        specialize (IHterm_s P (smtAnd Q (guardGen (undef e) source (ite e (smtTrue) (smtFalse))))).
        destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
        { intros F E mod_Q_ite mod_s'.
          apply (Q_impl_mod F E); simpl in mod_Q_ite, mod_s';
            destruct mod_Q_ite, mod_s'; simpl;try split; auto.
          apply models_guardGen_source; simpl; split.
          - apply models_guardGen_source in H4; simpl in H4; auto.
          - apply models_guardGen_source in H4; simpl in H4.
            destruct H4. cases in H16; try auto; isabsurd.
        }
        { exists (smtAnd Q' (guardGen (undef e) source (ite e smtTrue smtFalse))).
          destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
          split; try split; auto.
          - apply models_guardGen_source; simpl; split.
            + eapply (guard_true_if_eval _ _ e v); eauto.
              eapply (exp_eval_agree (E:=E')); eauto. hnf; intros.
              eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
            + unfold smt_eval.
              assert (exp_eval E'0 e = Some v).
              * eapply (exp_eval_agree (E:=E')); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
              * rewrite (exp_eval_partial_total E'0 e H3).
                rewrite condTrue; constructor.
          - simpl. cset_tac.
            + rewrite <- (H8 a).
              specialize (fv_subset a H4).
              rewrite H12 in fv_subset; simpl in fv_subset.
              cset_tac.
            + unfold guardGen in H4.
              rewrite <- (H8 a); cases in H4; cset_tac.
              simpl in H4. cset_tac.
              rewrite undef_vars_subset in H3; cset_tac.
          - intros F E mod_Q_Q' mod_s'.
            apply (mod_impl_unsat F E).
            + simpl in *; destruct mod_Q_Q'; auto.
            + simpl in *; destruct mod_s'; auto.
        }
      * specialize (IHterm_s L' ant E' E'0 s' s'0 source).
        specialize (IHterm_s P (smtAnd Q (guardGen (undef e) source (ite e (smtFalse) (smtTrue))))).
        destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
        { intros F E mod_Q_ite mod_s'.
          apply (Q_impl_mod F E); simpl in mod_Q_ite, mod_s';
            destruct mod_Q_ite, mod_s'; simpl;try split; auto.
          apply models_guardGen_source; simpl; split.
          - apply models_guardGen_source in H4; simpl in H4; auto.
          - apply models_guardGen_source in H4; simpl in H4.
            destruct H4. cases in H16; try auto; isabsurd.
        }
        { exists (smtAnd Q' (guardGen (undef e) source (ite e smtFalse smtTrue))).
          destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
          split; try split; auto.
          - apply models_guardGen_source; simpl; split.
            + eapply (guard_true_if_eval _ _ e v); eauto.
              eapply (exp_eval_agree (E:=E')); eauto. hnf; intros.
              eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
            + unfold smt_eval.
              assert (exp_eval E'0 e = Some v).
              * eapply (exp_eval_agree (E:=E')); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
              * rewrite (exp_eval_partial_total E'0 e H3).
                rewrite condFalse; constructor.
          - simpl. cset_tac.
            + rewrite <- (H8 a).
              specialize (fv_subset a H4).
              rewrite H13 in fv_subset; simpl in fv_subset.
              cset_tac.
            + unfold guardGen in H4.
              rewrite <- (H8 a); cases in H4; cset_tac.
              simpl in H4. cset_tac.
              rewrite undef_vars_subset in H3; cset_tac.
          - intros F E mod_Q_Q' mod_s'.
            apply (mod_impl_unsat F E).
            + simpl in *; destruct mod_Q_Q'; auto.
            + simpl in *; destruct mod_s'; auto.
        }
    + specialize (H0 l Y); isabsurd.
    + isabsurd.
  - inv noFun_s.
    + inv H. inv ssa_s. specialize (IHterm_s L' an (E0 [x <- ⎣ v ⎦]) E'0 s' s'0 target).
      specialize (IHterm_s P (smtAnd Q (guardGen (undef e) target (constr (Var x) e)))).
      destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
      * intros F E mod_Q mod_P.
        specialize (Q_impl_mod F E).
        simpl in mod_Q.
        destruct mod_Q as [mod_Q mod_Constr].
        specialize (Q_impl_mod mod_Q).
        apply Q_impl_mod; simpl; simpl in mod_P; split; auto.
        apply models_guardGen_target; apply models_guardGen_target in mod_Constr.
        simpl in *; intros; destruct mod_P; auto.
      * exists (smtAnd Q' (guardGen (undef e) target (constr (Var x) e))).
        destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
        split; try split; eauto.
        { apply models_guardGen_target; simpl; intros.
          unfold smt_eval.
          assert (exp_eval E'0 e = Some v).
          - eapply (exp_eval_agree (E:=E0)); eauto; hnf; intros.
            eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
          - assert (exp_eval E'0 (Var x) = Some v).
            + eapply (exp_eval_agree (E:= E0[x <- Some v])).
              * hnf. intros. simpl in H8.
                  eapply (term_ssa_eval_agree L' L' s'); eauto.
                  rewrite H10; simpl; cset_tac.
              * simpl. unfold update. cases; auto.
            + rewrite (exp_eval_partial_total E'0 (Var x) H8).
              rewrite (exp_eval_partial_total E'0 e H4).
              eapply bvEq_equiv_eq; auto.
        }
        { rewrite H10 in fv_subset; simpl in *. cset_tac.
          - hnf in fv_subset. specialize (fv_subset a H4).
            specialize (H9 a). rewrite H9.
            cset_tac.
          - unfold guardGen in H4.
            cases in H4; simpl in *;
              rewrite (H9 a); cset_tac.
            + rewrite undef_vars_subset in H2. cset_tac.
        }
        { intros F E mod_Q_Q' mod_trans.
          apply (mod_impl_unsat F E); auto.
          - simpl in *.
            destruct mod_Q_Q' as [mod_Q [mod_E_Q' mod_constr]].
            split; try split; auto.
        }
    + inv H; inv ssa_s.
      * specialize (IHterm_s L' ans E' E'0 s' s'0 target).
        specialize (IHterm_s P (smtAnd Q (guardGen (undef e) target (ite e (smtTrue) (smtFalse))))).
        destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
        { intros F E mod_Q_ite mod_s'.
          apply (Q_impl_mod F E); simpl in mod_Q_ite, mod_s';
            destruct mod_Q_ite, mod_s'; simpl;try split; auto.
          apply models_guardGen_target; simpl.
          - intros. apply models_guardGen_target in H4. simpl in H4.
            cases; auto; isabsurd.
        }
        { exists (smtAnd Q' (guardGen (undef e) target (ite e smtTrue smtFalse))).
          destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
          split; try split; auto.
          - apply models_guardGen_target; simpl.
            + intros.
              unfold smt_eval.
              assert (exp_eval E'0 e = Some v).
              * eapply (exp_eval_agree (E:=E')); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
              * rewrite (exp_eval_partial_total E'0 e H4).
                rewrite condTrue; constructor.
          - simpl. cset_tac.
            + rewrite <- (H8 a).
              specialize (fv_subset a H4).
              rewrite H12 in fv_subset; simpl in fv_subset.
              cset_tac.
            + unfold guardGen in H4.
              rewrite <- (H8 a); cases in H4; cset_tac.
              simpl in H4. cset_tac.
              rewrite undef_vars_subset in H3; cset_tac.
          - intros F E mod_Q_Q' mod_s'.
            apply (mod_impl_unsat F E).
            + simpl in *; destruct mod_Q_Q'; auto.
            + simpl in *; destruct mod_s'; auto.
        }
      * specialize (IHterm_s L' ant E' E'0 s' s'0 target).
        specialize (IHterm_s P (smtAnd Q (guardGen (undef e) target (ite e (smtFalse) (smtTrue))))).
        destruct IHterm_s as [Q' IHterm_s]; inv noFun_s; eauto.
        { intros F E mod_Q_ite mod_s'.
          apply (Q_impl_mod F E); simpl in mod_Q_ite, mod_s';
            destruct mod_Q_ite, mod_s'; simpl;try split; auto.
          apply models_guardGen_target; simpl.
          - intros. apply models_guardGen_target in H4. simpl in H4; cases; auto; isabsurd.
        }
        { exists (smtAnd Q' (guardGen (undef e) target (ite e smtFalse smtTrue))).
          destruct IHterm_s as [mod_Q' [fv_subset mod_impl_unsat]].
          split; try split; auto.
          - apply models_guardGen_target; simpl.
            + unfold smt_eval.
              assert (exp_eval E'0 e = Some v).
              * eapply (exp_eval_agree (E:=E')); eauto; hnf; intros.
                eapply (term_ssa_eval_agree); eauto; econstructor; eauto.
              * rewrite (exp_eval_partial_total E'0 e H3).
                rewrite condFalse; constructor.
          - simpl. cset_tac.
            + rewrite <- (H8 a).
              specialize (fv_subset a H4).
              rewrite H13 in fv_subset; simpl in fv_subset.
              cset_tac.
            + unfold guardGen in H4.
              rewrite <- (H8 a); cases in H4; cset_tac.
              simpl in H4. cset_tac.
              rewrite undef_vars_subset in H3; cset_tac.
          - intros F E mod_Q_Q' mod_s'.
            apply (mod_impl_unsat F E).
            + simpl in *; destruct mod_Q_Q'; auto.
            + simpl in *; destruct mod_s'; auto.
        }
    + specialize (H0 l Y); isabsurd.
    + isabsurd.
Qed.

Lemma predeval_uneq_ret:
forall  E et es e e' P,
exp_eval E et = Some e
-> exp_eval E es = Some e'
-> (forall F, models F (to_total E) P)
-> (forall (F:lab->vallst->bool),
      models F (to_total E) P ->
      ~ ((models F (to_total E) (translateStmt (stmtReturn et) target)) /\
    models F (to_total E) (translateStmt (stmtReturn es) source)))
-> (e = e').

Proof.
intros. decide (e = e').
- assumption.
- specialize (H1 (fun _ => fun x =>toBool (bvEq e' (hd (O::nil) x)))).
  specialize (H2 (fun _ => fun x => toBool (bvEq e' (hd (O::nil) x)))).
  specialize (H2 H1); simpl in H2.
  pose proof (exp_eval_partial_total E et H).
  pose proof (exp_eval_partial_total E es H0).
  exfalso.
  eapply H2.
  erewrite models_guardGen_target at 1.
  erewrite models_guardGen_source.
  simpl; split; intros; try split.
  +unfold smt_eval in H6.
   rewrite H3 in H6.
   eapply n.
   symmetry.
   eapply (bvEq_equiv_eq e' e); eauto.
  + eapply guard_true_if_eval; eauto.
  + unfold smt_eval.  rewrite H4.
    rewrite bvEq_refl; econstructor.
Qed.

Lemma predeval_uneq_goto:
forall E l1 l2 et es el el' P,
omap (exp_eval E) et = Some el
-> omap (exp_eval E) es = Some el'
->(forall F, models F (to_total E) P)
-> (forall (F:lab->vallst->bool),
      models F (to_total E) P ->
      ~ ((models F (to_total E) (translateStmt (stmtApp l1 et) target)) /\
         models F (to_total E) (translateStmt (stmtApp l2 es) source)))
-> (el = el').

Proof.
  intros. decide (el = el').
  - assumption.
  - decide (l1 = l2).
    + pose (F:= (fun (_:lab) => fun x => if [ x = el' ] then true else false )).
      specialize (H2 F). specialize (H1 F). specialize (H2 H1). clear H1.
      simpl in H2; exfalso; eapply H2.
      erewrite models_guardGen_source; erewrite models_guardGen_target.
      simpl; split; intros; try split.
      * erewrite (list_eval_agree _ _ H) in H3.
        unfold F in H3. cases in H3; isabsurd.
      * eapply guardList_true_if_eval; eauto.
      * unfold F. erewrite (list_eval_agree _ _ H0).
        cases; intuition.
   + pose (F:= fun l => fun (_:vallst) => if [l = labInc l2 1] then true else false).
      specialize (H1 F); specialize (H2 F).
      specialize (H2 H1).
      simpl in H2; exfalso; eapply H2.
      erewrite models_guardGen_source; erewrite models_guardGen_target.
      simpl; split; intros; try split.
      * unfold F in H4. cases in H4; try isabsurd.
         eapply n0. destruct l1, l2. eapply labeq_incr; simpl; eauto.
      * eapply guardList_true_if_eval; eauto.
      * unfold F. cases; intuition.
Qed.

(** Case 1 of final theorem.
Given source program s, target program t, if [s]^+ /\ [t]^- is unsatisfiable
the two programs must be equivalent **)
Lemma tval_term_sound L D D' E Es Et s s' t t':
  (forall F E, ~ models F E (smtCheck s t))
  (* Both programs have the same free variables *)
  -> (fst(getAnn D)) [=] (fst(getAnn D'))
  (* The programs are renamed apart from each other *)
  -> disj (snd (getAnn D)) (snd (getAnn D'))
  (* Every variable gets defined only once in s and t*)
  -> renamedApart s D
  -> renamedApart t D'
  -> noFun s (* disallow function definitions and external function calls *)
  -> noFun t (* same*)
  (* Free Variables must be defined *)
  -> (forall x, x ∈ (fst(getAnn D)) -> exists v, E x = Some v)
  -> Terminates (L,E,s) (L,Es,s')
  -> Terminates (L,E,t) (L,Et,t')
  -> @sim _ statetype_F _ statetype_F  (L, E, s) (L, E, t).

Proof.
  intros Unsat_check Eq_FVars RenApart ssa_s ssa_t nf_s nf_t val_def term_s term_t.
  unfold smtCheck in Unsat_check.
  pose proof (extend_not_models _ smtTrue Unsat_check) as extend_mod.
  assert (forall (F : pred -> vallst -> bool) (E : onv val),
             models F (to_total E) smtTrue
             -> ~ models F (to_total E) (smtAnd (translateStmt s source) (translateStmt t target)))
    as extend_mod_partial
      by (intros F E0 mod_true;specialize (extend_mod F (to_total E0) mod_true); auto).
  pose proof (unsat_extension L D E Es s s' source (translateStmt t target) smtTrue)
    as extend1.
  specialize (extend1 extend_mod_partial ssa_s nf_s term_s).
  destruct extend1 as [Q [mod_Q [fv_Q Unsat_check2]]].
  pose proof (unsat_extension L D' E Et t t' target (translateStmt s' source) (smtAnd smtTrue Q))
    as extend2.
  assert (forall (F : pred -> vallst -> bool) (E : onv val),
             models F (to_total E) (smtAnd smtTrue Q)
             -> ~ models F (to_total E) (smtAnd (translateStmt t target) (translateStmt s' source))) as sat_Q.
  - intros F E0 mod_E0_Q mod_t_s'.
    specialize (Unsat_check2 F E0 mod_E0_Q).
    apply Unsat_check2; simpl in mod_t_s'; simpl;
      destruct mod_t_s'; split; auto.
  - specialize (extend2 sat_Q).
    (** Clean up **)
    clear sat_Q Unsat_check Unsat_check2.
    specialize (extend2 ssa_t nf_t term_t).
    destruct extend2 as [Q' [mod_Q' [fv_Q' Unsat_st]]].
    (** Construct model for assumption: TODO: Make this a lemma**)
    assert (forall F,
               models F
                      (to_total (combineEnv (fst (getAnn D) ∪ snd (getAnn D)) Es Et))
                      (smtAnd (smtAnd smtTrue Q) Q')) as mod_pre.
    + intros F.
      simpl; split; try split; try auto.
      * specialize (mod_Q F).
        assert (agree_on eq
                         (fst (getAnn D) ∪ snd (getAnn D)) Es
                         (combineEnv (fst (getAnn D) ∪ snd (getAnn D)) Es Et)).
        { hnf; intros.
          unfold combineEnv; cases; try eauto; isabsurd. }
        { eapply models_agree; eauto.
          hnf; intros.
          symmetry.
          eapply (agree_on_total (lv:={x})); cset_tac; eauto.
          eapply (agree_on_incl (lv:= freeVars Q)); cset_tac; eauto.
          eapply (agree_on_incl (lv:= fst(getAnn D) ∪ snd(getAnn D)));
            cset_tac; eauto.
          hnf in fv_Q. specialize (fv_Q a H1).
          cset_tac. }
      * specialize (mod_Q' F).
        assert (agree_on eq
                         (fst (getAnn D') ∪ snd(getAnn D')) Et
                         (combineEnv (fst (getAnn D) ∪ snd (getAnn D)) Es Et)).
        { hnf; intros.
          unfold combineEnv; cases; try eauto.
          cset_tac.
          - rewrite <- (term_ssa_eval_agree L L s D s' E Es); auto.
            rewrite <- (term_ssa_eval_agree L L t D' t' E Et); auto.
          - pose proof (renamedApart_disj ssa_s).
            rewrite <- (Eq_FVars x) in H0;
              exfalso; eauto.
          - pose proof (renamedApart_disj ssa_t).
            rewrite (Eq_FVars x) in H;
              exfalso; eauto. }
        { eapply models_agree; eauto.
          hnf; intros.
          symmetry.
          eapply (agree_on_total (lv:={x})); cset_tac; eauto.
          eapply (agree_on_incl (lv:= freeVars Q')); cset_tac; eauto.
          eapply (agree_on_incl (lv:= fst (getAnn D') ∪ snd(getAnn D')));
            cset_tac; eauto.
          specialize (fv_Q' a H1); cset_tac. }
    + pose proof (terminates_impl_star2  L E s L Es s' nf_s term_s)
        as s_star2.
      pose proof (terminates_impl_star2 L E  t L Et t' nf_t term_t)
        as t_star2.
      destruct s_star2 as [s_star2 [ [es ret_s'] | [f [X fcall_s']]]];
        destruct t_star2 as [t_star2 [ [et ret_t'] | [g [Y fcall_t']]]].
    (** s' = e /\ t' = e' --> must be sim **)
      *  eapply (simTerm
                (σ1 := (L, E, s)) (σ1' := (L, Es, stmtReturn es))
                (σ2 := (L, E, t)) (σ2' := (L, Et, stmtReturn et)));
           subst; try auto.
         { simpl.
           assert (exists evs, exp_eval Es es = Some evs)
             as val_es
               by (apply (terminates_impl_eval L L E s Es es nf_s term_s)).
           assert (exists evt, exp_eval Et et = Some evt)
          as val_et
            by (apply (terminates_impl_eval L L E t Et et nf_t term_t)).
           destruct val_es as [evs evalEs].
           destruct val_et as [evt evalEt].
           rewrite evalEs, evalEt.
           f_equal.
           remember (smtAnd (smtAnd smtTrue Q) Q') as P.
           remember (fst (getAnn D) ∪ snd(getAnn D)) as vars_s.
           remember (combineEnv vars_s Es Et) as C_env.
           pose proof (predeval_uneq_ret C_env et es evt evs P).
           symmetry.
           destruct (agree_on_ssa_combine D D' L E s t Es Et es et); eauto.
           subst.
           eapply H; clear H; intros;
             try erewrite exp_eval_agree; eauto. }
         { unfold normal2.
           unfold reducible2.
           hnf; intros.
           destruct H as [evt [σ step]].
           inversion step. }
         { unfold normal2.
           unfold reducible2.
           hnf; intros.
           destruct H as [evt [σ step]]. inversion step. }
      * subst. simpl in Unsat_st. exfalso.
        pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc g 1)))
                               then (fun (x:vallst) =>  false)
                               else (fun (x:vallst) => true))).
        remember (fst (getAnn D) ∪ snd(getAnn D)) as vars_s.
        remember (combineEnv vars_s Es Et) as E'.
        specialize (Unsat_st F E' ).
        eapply Unsat_st.
        { eapply (mod_pre). }
        { erewrite models_guardGen_target.
          erewrite models_guardGen_source.
          simpl; split; intros; try split.
          - unfold F in H0.
            rewrite <- (beq_nat_refl (labN(labInc g 1))) in H0; intuition.
          - subst. rewrite <- combineenv_eql.
            + eapply (guardTrue_if_Terminates_ret L L _ s); eauto.
            + hnf; intros. eapply (freeVars_undef a es) in H.
              (* freeVars -> Ds' *)
              pose proof (ssa_move_return D L E s Es es).
              destruct H0 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
              subst.
              simpl in *.
              cset_tac.
              eapply (renamed_apart_contained); eauto.
          - unfold F. destruct g; simpl; eauto.
        }
      * subst.
        simpl in Unsat_st.
        exfalso.
        pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc f 1)))
                                   then (fun (x:vallst) =>  true)
                             else (fun (x:vallst) => false))).
        remember (fst (getAnn D) ∪ snd(getAnn D)) as vars_s.
        remember (combineEnv vars_s Es Et) as E'.
        specialize (Unsat_st F E' ).
        eapply Unsat_st.
       { eapply (mod_pre). }
       { erewrite models_guardGen_target.
         erewrite models_guardGen_source.
         simpl; split; intros; try split.
         - unfold F in H0.
           simpl in H0.
           unfold labInc in H0.
           destruct f.
           simpl in H0; isabsurd.
         - subst. rewrite <- combineenv_eql.
             * eapply (guardTrue_if_Terminates_goto L L _ s); eauto.
             * hnf; intros.
               eapply (freeVars_undefLift a X) in H.
               (* freeVars -> Ds' *)
               pose proof (ssa_move_goto D L E s Es f X).
                destruct H0 as [D'' [ssaGoto [fstSubset sndSubset]]]; eauto;
                  inversion ssaGoto; subst.
                simpl in *.
                cset_tac.
                eapply (renamed_apart_contained_list); eauto.
         - unfold F. rewrite <- (beq_nat_refl (labN (labInc f 1))); constructor.
       }
      * subst; eapply sim'_sim.
        eapply sim'_expansion_closed; eauto.
        eapply sim_sim'.
        decide (f = g).
        { subst.
          destruct (get_dec L (counted g)) as [[[bE bZ bs]]|].
          - pose proof (terminates_impl_evalList L L E s Es g X nf_s term_s).
            pose proof (terminates_impl_evalList L L E t Et g Y nf_t term_t).
            destruct H as [es seval]; destruct H0 as [et teval].
            pose proof (predeval_uneq_goto
                          (combineEnv (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)
                          g g Y X et es)
              as equal_goto.
            specialize (equal_goto (smtAnd (smtAnd smtTrue Q) Q')).
            pose proof (explist_combineenv_eql X (fst(getAnn D) ∪ (snd (getAnn D))) Es Et (Some es))
              as val_agree_left.
            destruct val_agree_left.
            + pose proof (ssa_move_goto D L E s Es g X) as ssa_goto.
              destruct ssa_goto as [D'' [ssaGoto [fstSubset sndSubset]]]; eauto.
              inversion ssaGoto.
              hnf; intros; subst.
              simpl in fstSubset, sndSubset.
              cset_tac.
              pose proof (renamed_apart_contained_list a X L E s Es g D H4)
                as a_in_fst_snd.
              destruct a_in_fst_snd; auto.
            + pose proof (explist_combineenv_eqr Y (fst(getAnn D) ∪ (snd (getAnn D))) Es Et (Some et))
                as val_agree_right.
              destruct val_agree_right.
              * (* freeVars ∩ Ds' agree *)
                pose proof (ssa_move_goto D' L E t Et g Y) as ssa_goto.
                destruct ssa_goto as [D'' [ ssaGoto [ fstSubset sndSubset ]]];
                  auto.
                inversion ssaGoto; subst.
                hnf; intros.
                cset_tac.
                { rewrite <- (term_ssa_eval_agree L L s D (stmtApp g X) E Es); auto.
                  rewrite <- (term_ssa_eval_agree L L t D'(stmtApp g Y) E Et); auto.
                  rewrite <- (Eq_FVars x); auto. }
                { pose proof (renamed_apart_contained_list x Y L E t Et g D').
                  destruct H; auto.
                  pose proof (renamedApart_disj ssa_s).
                  hnf in H6.
                  rewrite <- Eq_FVars in H.
                  exfalso; apply (H6 x); auto.
                }
            * specialize (H0 seval); specialize (H2 teval).
              specialize (equal_goto H2 H0).
              (** CLEANUP **)
              clear H H1 extend_mod extend_mod_partial.
              (** Make the result values equal **)
              { rewrite equal_goto in teval; intros;
                [ | | eapply Unsat_st]; try auto.
                pose proof (omap_length exp val es (exp_eval Es) X seval).
                pose proof (omap_length exp val es (exp_eval Et) Y teval).
                decide (length X = length bZ).
                - one_step.
                  + simpl. rewrite <- e; rewrite H; rewrite <- H1; auto.
                  + eapply sim_refl.
                - no_step. get_functional.
                  + subst. simpl in *; congruence.
                  + (* Construct a contradiction as both argument lists are equal
                    and len contains the assumption that the lengths are equal *)
                    eapply n. pose proof (get_functional g0 Ldef).
                    rwsimplB H3 len.
                    rewrite len.
                    rewrite H, H1; auto. }
          - no_step; eauto. }
        { exfalso.
          pose (F := (fun l => fun (_:vallst) => if [labInc f 1 = l] then true else false)).
          specialize (Unsat_st F (combineEnv (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)).
          eapply Unsat_st.
          - eapply (mod_pre).
          - unfold F; simpl.
            erewrite models_guardGen_source; erewrite models_guardGen_target.
            simpl. split; intros; simpl; try split.
            + cases in H0; eauto.
              eapply n. destruct f,g. simpl in *; eapply labeq_incr. simpl; eauto.
            +  pose proof (terminates_impl_evalList L L E s Es f X ).
               destruct H; eauto.
               eapply guardList_true_if_eval; eauto.
               pose proof (explist_combineenv_eql X (fst(getAnn D) ∪ (snd (getAnn D))) Es Et (Some x)).
              destruct H0; cset_tac; eauto.
              pose proof (ssa_move_goto D L E s Es f X).
              destruct H1 as [D'' [ssaRet [fstSubset sndSubset]]]; eauto;
                inversion ssaRet.
              subst; simpl in *.
              pose proof (renamed_apart_contained_list a X L E s Es f D).
              destruct H1; auto.
            + cases; isabsurd; econstructor.
        }
Qed.

(** Theorem 2 in the thesis **)
(* Unused hypothesis from legacy stuff:
Ds' ∩ Dt' = Df  The free Variables do not get overwritten?
  getAnn D = (Df, Ds') To acces the environments from ssa
-> getAnn D' = (Df, Dt') *)
Lemma tval_sound L D D' E s t:
  (forall F E, ~ models F E (smtCheck s t))
  (* Both programs have the same free variables *)
  -> (fst(getAnn D)) [=] (fst(getAnn D'))
  (* The programs are renamed apart from each other *)
  -> disj (snd (getAnn D)) (snd (getAnn D'))
  (* Every variable gets defined only once in s and t*)
  -> renamedApart s D
  -> renamedApart t D'
  -> noFun s (* disallow function definitions and external function calls *)
  -> noFun t (* same*)
  (* Free Variables must be defined *)
  -> (forall x, x ∈ (fst(getAnn D)) -> exists v, E x = Some v)
  -> @sim _ statetype_F _ statetype_F  (L, E, s) (L, E, t).

Proof.
  intros Unsat_check Eq_FVars RenApart ssa_s ssa_t nf_s nf_t val_def.
  pose proof (noFun_impl_term_crash E s nf_s) as term_crash_s.
  destruct term_crash_s as [Es [s' term_crash_s]].
  pose proof (noFun_impl_term_crash E t nf_t) as term_crash_t.
  destruct term_crash_t as [Et [t' term_crash_t]].
  specialize (term_crash_s L); specialize (term_crash_t L).
  (** Case Split for Termination of s and t **)
  destruct term_crash_s as [term_s | crash_s].
  (** Case 1: s terminates & t terminates **)
  - destruct term_crash_t as [term_t | crash_t].
    + eapply tval_term_sound; eauto.
      (** Widerspruch konstruieren aus guard = False und ~ models
      apply Lemma dass wenn es gibt i was models s und crash t --> models s /\ t
      konstruieren mit sat_extension und Lemma terminates_impl_sim **)
    + pose proof (terminates_impl_models L  s D E s' Es ssa_s nf_s term_s)
          as sat_s.
      assert (forall x, x ∈ fst(getAnn D') -> exists v, E x = Some v) as fv_def.
      * intros x in_fst.
        apply (val_def x); eauto.
        rewrite Eq_FVars; auto.
      * pose proof (crash_impl_models L L D' t E Et t' ssa_t fv_def nf_t crash_t (fun _ => fun _ => true)).
        pose proof (combineenv_agree (fst (getAnn D) ∪ snd(getAnn D)) Es Et)
          as agree_combineEnv.
        specialize (Unsat_check (fun _ => fun _ => true) (to_total (combineEnv (fst (getAnn D) ∪ snd(getAnn D)) Es Et))).
        exfalso.
        apply Unsat_check; simpl; split.
        { eapply models_agree; eauto.
          eapply agree_on_total.
          eapply (agree_on_incl (lv:= fst (getAnn D) ∪ snd(getAnn D) )); eauto.
          cset_tac.
          pose proof (freeVars_incl s D source ssa_s nf_s a H0); cset_tac. }
        { pose proof (freeVars_incl t D' target ssa_t nf_t).
          rewrite <- combineenv_eqr; eauto.
          eapply (agree_on_incl (lv:= ((fst (getAnn D') ∪ snd (getAnn D')) ∩ (fst(getAnn D) ∪ (snd (getAnn D)))))).
          - hnf; intros.
            cset_tac.
            + erewrite <- (term_ssa_eval_agree L L s D s' E Es); auto.
              erewrite <- (crash_ssa_eval_agree L L t D' t' E Et); auto.
            + exfalso; eapply (renamedApart_disj ssa_s); eauto.
              rewrite (Eq_FVars x); auto.
            + exfalso; eapply (renamedApart_disj ssa_t); eauto.
              rewrite <- (Eq_FVars x); auto.
        - cset_tac.
          + specialize (H0 a H2); cset_tac.
          + specialize (H0 a H2); cset_tac.
        }
  (** s crasht --> always sim *)
  - pose proof (crash_impl_err E s Es s' L L nf_s crash_s ) as err.
    destruct err as [star2_s [normal2_s failed_s']].
    eapply simErr; eauto.
Qed.