Require Import List Arith.
Require Import IL Annotation AutoIndTac Exp RenamedApart Fresh Util.
Require Import SetOperations SimF Var.
Require Import SMT NoFun CombineEnv.
Require Import Guards ILFtoSMT GuardProps ComputeProps.

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
  rewrite freeVars_translateStmt.
  rewrite <- renamedApart_occurVars; eauto.
  rewrite <- renamedApart_freeVars; eauto.
  rewrite occurVars_freeVars_definedVars. reflexivity.
Qed.




(** Lemma 12 in the thesis
Formulas can be extended by a Q that represents the effects of
the program history
**)
Lemma unsat_extension L D E E' s s' pol P Q:
(forall F E, models F (to_total E) Q -> ~ models F (to_total E) (smtAnd (translateStmt s pol) P))
-> renamedApart s D
-> noFun s
-> noCall s
-> star nc_step (L, E, s) (L, E', s')
-> exists Q', (forall F, models F (to_total E')  Q' ) /\
              freeVars Q' ⊆  snd(getAnn D) ∪ fst(getAnn D) /\
              (forall F E, models F (to_total E) (smtAnd Q Q')
                           -> ~ models F (to_total E) (smtAnd (translateStmt s' pol) P)).
Proof.
  intros Q_impl_mod RA noFun_s noCall_s term_s.
  general induction term_s.
  - exists smtTrue; simpl; cset_tac.
  - exploit nc_step_agree as AGR1; eauto using star_step.
    destruct H; simpl in *. hnf in H.
    invt noFun; invt renamedApart; invt F.step; invt notApp; invt noCall;
      exploit nc_step_agree' as AGR2; eauto; simpl in *.
    + exploit IHterm_s; try reflexivity; eauto.
      * intros; intro.
        eapply Q_impl_mod. eauto. simpl.
        instantiate (1:=(smtAnd P (guardGen (undef e0) source (constr (Var x) e0))))
          in H4; simpl in *; dcr.
        rewrite models_guardGen_source in H13.
        destruct pol.
        -- rewrite models_guardGen_source. simpl in *; dcr.
           repeat (split; eauto).
        -- rewrite models_guardGen_target. simpl in *; dcr.
           repeat (split; eauto).
      * destruct H2 as [P' ?]; simpl in *; dcr.
        pe_rewrite.
        eexists (smtAnd P' (guardGen (undef e0) source (constr (Var x) e0)));
          repeat split; eauto.
        -- rewrite models_guardGen_source; simpl; split.
          ** eapply guard_true_if_eval.
             eauto using op_eval_agree with cset.
          ** eapply smt_eval_var; eauto with cset.
        -- simpl. rewrite freeVars_guardGen, freeVars_undef, !H6; simpl.
           rewrite H6, H11, H9. clear; cset_tac.
        -- intros; intro. simpl in *.
           eapply H12; dcr; simpl; eauto.
    + exploit IHterm_s; try reflexivity; eauto.
      * intros; intro.
        eapply Q_impl_mod. eauto. simpl.
        instantiate (1:=(smtAnd P (guardGen (undef e) source (ite e (smtTrue) (smtFalse))))) in H4; simpl in *; dcr.
        rewrite models_guardGen_source in H17.
        destruct pol.
        -- rewrite models_guardGen_source. simpl in *; dcr.
           cases in H15; [|isabsurd].
           repeat (split; eauto).
        -- rewrite models_guardGen_target. simpl in *; dcr.
           cases in H15; [|isabsurd].
           repeat (split; eauto).
      * destruct H3 as [P' ?]; simpl in *; dcr.
        pe_rewrite.
        eexists (smtAnd P' (guardGen (undef e) source (ite e (smtTrue) (smtFalse))));
          repeat split; eauto.
        -- rewrite models_guardGen_source; simpl; split.
          ** eapply guard_true_if_eval.
             eauto using op_eval_agree with cset.
          ** erewrite smt_eval_op; eauto with cset.
             rewrite condTrue; eauto.
        -- simpl. rewrite freeVars_guardGen, freeVars_undef, !H6; simpl.
           rewrite H15, <- H8, H6. clear; cset_tac.
        -- intros; intro. simpl in *.
           eapply H16; dcr; simpl; eauto.
    + exploit IHterm_s; try reflexivity; eauto.
      * intros; intro.
        eapply Q_impl_mod. eauto. simpl.
        instantiate (1:=(smtAnd P (guardGen (undef e) source (ite e (smtFalse) (smtTrue))))) in H4; simpl in *; dcr.
        rewrite models_guardGen_source in H17.
        destruct pol.
        -- rewrite models_guardGen_source. simpl in *; dcr.
           cases in H15; [isabsurd|].
           repeat (split; eauto).
        -- rewrite models_guardGen_target. simpl in *; dcr.
           cases in H15; [isabsurd|].
           repeat (split; eauto).
      * destruct H3 as [P' ?]; simpl in *; dcr.
        pe_rewrite.
        eexists (smtAnd P' (guardGen (undef e) source (ite e (smtFalse) (smtTrue))));
          repeat split; eauto.
        -- rewrite models_guardGen_source; simpl; split.
          ** eapply guard_true_if_eval.
             eauto using op_eval_agree with cset.
          ** erewrite smt_eval_op; eauto with cset.
             rewrite condFalse; eauto.
        -- simpl. rewrite freeVars_guardGen, freeVars_undef, !H6; simpl.
          rewrite H15, <- H8, H6. clear; cset_tac.
        -- intros; intro. simpl in *.
           eapply H16; dcr; simpl; eauto.
Qed.

Lemma predeval_uneq_ret E et es e e' P
  : op_eval E et = Some e
    -> op_eval E es = Some e'
    -> (forall F, models F (to_total E) P)
    -> (forall (F:lab-> list val -> bool),
          models F (to_total E) P ->
          ~ ((models F (to_total E) (translateStmt (stmtReturn et) target)) /\
             models F (to_total E) (translateStmt (stmtReturn es) source)))
    -> (e = e').
Proof.
  intros. decide (e = e').
  - assumption.
  - exfalso.
    set (F:=(fun (l:pred) (l:list val) => if [ e' = hd e l ] then true else false)).
    eapply (H2 F); eauto.
    simpl.
    erewrite models_guardGen_target at 1.
    erewrite models_guardGen_source. simpl.
    unfold F at 2 4; simpl.
    repeat erewrite op_eval_smt_eval; eauto.
    repeat cases; eauto using guard_true_if_eval.
Qed.

Lemma predeval_uneq_goto E l1 l2 et es el el' P
  : omap (op_eval E) et = Some el
    -> omap (op_eval E) es = Some el'
    ->(forall F, models F (to_total E) P)
    -> (forall (F:lab -> list val -> bool),
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
   + pose (F:= fun l => fun (_:list val) => if [l = labInc l2 1] then true else false).
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
the two programs are equivalent **)
Lemma tval_term_sound L D D' E Es Et s s' t t'
  : (forall F E, ~ models F E (smtCheck s t))
    (* Both programs have the same free variables *)
    -> (fst(getAnn D)) [=] (fst(getAnn D'))
    (* The programs are renamed apart from each other *)
    -> disj (snd (getAnn D)) (snd (getAnn D'))
    (* Every variable gets defined only once in s and t*)
    -> renamedApart s D
    -> renamedApart t D'
    -> noFun s /\ noCall s (* disallow function definitions and external function calls *)
    -> noFun t /\ noCall t(* same*)
    (* Free Variables must be defined *)
    -> (forall x, x ∈ (fst(getAnn D)) -> exists v, E x = Some v)
    -> Terminates (L,E,s) (L,Es,s')
    -> Terminates (L,E,t) (L,Et,t')
    -> @sim _ statetype_F _ statetype_F bot3 Sim (L, E, s) (L, E, t).

Proof.
  intros Unsat_check Eq_FVars RenApart ssa_s ssa_t [nf_s nc_s] [nf_t nc_t] val_def
         [star_s trm_s] [star_t trm_t].
  unfold smtCheck in Unsat_check.
  pose proof (extend_not_models _ smtTrue Unsat_check) as extend_mod.
  assert (forall (F : pred -> list val -> bool) (E : onv val),
             models F (to_total E) smtTrue
             -> ~ models F (to_total E) (smtAnd (translateStmt s source) (translateStmt t target)))
    as extend_mod_partial
      by (intros F E0 mod_true;specialize (extend_mod F (to_total E0) mod_true); auto).
  pose proof (unsat_extension L D E Es s s' source (translateStmt t target) smtTrue)
    as extend1.
  specialize (extend1 extend_mod_partial ssa_s nf_s nc_s star_s).
  destruct extend1 as [Q [mod_Q [fv_Q Unsat_check2]]].
  pose proof (unsat_extension L D' E Et t t' target (translateStmt s' source) (smtAnd smtTrue Q))
    as extend2.
  assert (forall (F : pred -> list val -> bool) (E : onv val),
             models F (to_total E) (smtAnd smtTrue Q)
             -> ~ models F (to_total E) (smtAnd (translateStmt t target) (translateStmt s' source))) as sat_Q.
  - intros F E0 mod_E0_Q mod_t_s'.
    specialize (Unsat_check2 F E0 mod_E0_Q).
    apply Unsat_check2; simpl in mod_t_s'; simpl;
      destruct mod_t_s'; split; auto.
  - specialize (extend2 sat_Q).
    (** Clean up **)
    clear sat_Q Unsat_check Unsat_check2.
    specialize (extend2 ssa_t nf_t nc_t star_t).
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
          eapply (agree_on_total (lv:={x})); [|eauto with cset].
          eapply (agree_on_incl (lv:= freeVars Q)); [|eauto with cset].
          eapply (agree_on_incl (lv:= fst(getAnn D) ∪ snd(getAnn D)));
            cset_tac; eauto.
        }
      * specialize (mod_Q' F).
        assert (agree_on eq
                         (fst (getAnn D') ∪ snd(getAnn D')) Et
                         (combineEnv (fst (getAnn D) ∪ snd (getAnn D)) Es Et)).
        { hnf; intros.
          unfold combineEnv; cases; try eauto.
          cset_tac'.
          - rewrite <- (@nc_step_agree L L s D s' E Es); auto.
            rewrite <- (@nc_step_agree L L t D' t' E Et); auto.
          - pose proof (renamedApart_disj ssa_s).
            exfalso; eauto.
          - pose proof (renamedApart_disj ssa_t).
            exfalso; eauto.
        }
        { eapply models_agree; eauto.
          hnf; intros.
          symmetry.
          eapply (agree_on_total (lv:={x})); [|eauto with cset].
          eapply (agree_on_incl (lv:= freeVars Q')); [| eauto with cset].
          eapply (agree_on_incl (lv:= fst (getAnn D') ∪ snd(getAnn D')));
            cset_tac; eauto.
        }
    + pose proof (nc_star_step star_s) as s_star2.
      pose proof (nc_star_step star_t) as t_star2.

      inv trm_s; inv trm_t. simpl in *.
    (** s' = e /\ t' = e' --> must be sim **)
      * pfold. eapply (SimTerm);
           [| eapply s_star2 | eapply t_star2 |stuck2 | stuck2]; simpl.
         edestruct terminates_impl_eval; eauto. split; eauto.
         edestruct terminates_impl_eval; try eapply nf_s; eauto.
         split; eauto.
         rewrite H, H2.
         f_equal.
         remember (smtAnd (smtAnd smtTrue Q) Q') as P.
         remember (fst (getAnn D) ∪ snd(getAnn D)) as vars_s.
         remember (combineEnv vars_s Es Et) as C_env.
         pose proof (predeval_uneq_ret C_env e0 e x x0 P).
         symmetry.
         destruct (nc_step_agree_combine D D' L E s t Es Et e e0); eauto.
         subst; simpl in *; pe_rewrite.
         eapply H3; eauto;
           try erewrite op_eval_agree; eauto.
      * subst. simpl in Unsat_st. exfalso.
        pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc f 1)))
                               then (fun (x:list val) =>  false)
                               else (fun (x:list val) => true))).
        remember (fst (getAnn D) ∪ snd(getAnn D)) as vars_s.
        remember (combineEnv vars_s Es Et) as E'.
        specialize (Unsat_st F E' ).
        eapply Unsat_st.
        { eapply (mod_pre). }
        { erewrite models_guardGen_target.
          erewrite models_guardGen_source.
          simpl; split; intros; try split.
          - unfold F in H2.
            rewrite <- (beq_nat_refl (labN(labInc f 1))) in H2; intuition.
          - subst.
            rewrite <- combineEnv_models.
            + eapply (guardTrue_if_Terminates L L _ s); eauto.
              split; eauto.
            + rewrite freeVars_undef.
              rewrite <- (renamedApart_contained); try eapply ssa_s; simpl; eauto.
              simpl; eauto.
          - unfold F. destruct f; simpl; eauto.
        }
      * subst.
        simpl in Unsat_st.
        exfalso.
        pose (F:= (fun (l:lab) => if (beq_nat (labN l) (labN (labInc f 1)))
                               then (fun (x:list val) =>  true)
                               else (fun (x:list val) => false))).
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
          - subst. rewrite <- combineEnv_models.
            * eapply (guardTrue_if_Terminates_goto L L _ s); eauto.
              split; eauto.
            * rewrite freeVars_undefLift.
              exploit renamedApart_contained; try eapply ssa_s; eauto.
          - unfold F. rewrite <- (beq_nat_refl (labN (labInc f 1))); constructor.
        }
      * eapply sim_expansion_closed; eauto.
        decide (f = f0).
        { subst.
          destruct (get_dec L (counted f0)) as [[[bE bZ bs]]|].
          - edestruct (@terminates_impl_evalList L L E s Es f0 Y nf_s);
              [ split; eauto | ].
            edestruct (@terminates_impl_evalList L L E t Et f0 Y0 nf_t);
              [ split; eauto | ].
            pose proof (predeval_uneq_goto
                          (combineEnv (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)
                          f0 f0 Y0 Y x0 x)
              as equal_goto.
            specialize (equal_goto (smtAnd (smtAnd smtTrue Q) Q')).
            exploit (combineEnv_omap_exp_eval_left Y (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)
              as val_agree_left.
            + exploit renamedApart_contained as a_in_fst_snd; try eapply star_s; eauto.
            + exploit (combineEnv_omap_exp_eval_right Y0 (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)
                as val_agree_right.
              * (* freeVars ∩ Ds' agree *)
                edestruct (@nc_step_renamedApart D' L E t Et)
                  as [D'' [ ssaGoto [ fstSubset sndSubset ]]]; eauto.
                inv ssaGoto; simpl in *.
                exploit (@nc_step_agree L L s); eauto.
                exploit (@nc_step_agree L L t); eauto.
                rewrite <- Eq_FVars in H4. rewrite H3 in H4.
                eapply agree_on_incl; eauto.
                exploit (renamedApart_contained L E t); eauto.
                simpl in *.
                rewrite H6, Eq_FVars.
                revert RenApart.
                clear; cset_tac.
              * exploit equal_goto; eauto; clear equal_goto.
                rewrite val_agree_right; eauto.
                rewrite val_agree_left; eauto.
                subst.
                exploit omap_length; eauto.
                exploit omap_length; try eapply H; eauto.
                decide (length Y = length bZ).
                -- pone_step.
                   ++ simpl. congruence.
                   ++ simpl. left. eapply sim_refl.
                -- pno_step.
          - pno_step; eauto. }
        { exfalso.
          pose (F := (fun l => fun (_:list val) => if [labInc f 1 = l] then true else false)).
          specialize (Unsat_st F (combineEnv (fst(getAnn D) ∪ (snd (getAnn D))) Es Et)).
          eapply Unsat_st.
          - eapply (mod_pre).
          - unfold F; simpl.
            erewrite models_guardGen_source; erewrite models_guardGen_target.
            simpl. split; intros; simpl; try split.
            + cases in H2; eauto.
              eapply n. destruct f,f0. simpl in *; eapply labeq_incr. simpl; eauto.
            + pose proof (@terminates_impl_evalList L L E s Es f Y); eauto.
              destruct H; eauto.
              hnf; split; eauto.
              eapply guardList_true_if_eval; eauto.
              rewrite (combineEnv_omap_exp_eval_left Y (fst(getAnn D) ∪ (snd (getAnn D))) Es Et ); eauto.
              edestruct (@nc_step_renamedApart D L E s Es); eauto; dcr.
              inv H3.
              subst; simpl in *.
              exploit renamedApart_contained; try eapply star_s; eauto.
            + cases; eauto.
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
  -> noFun s /\ noCall s(* disallow function definitions and external function calls *)
  -> noFun t /\ noCall t(* same*)
  (* Free Variables must be defined *)
  -> (forall x, x ∈ (fst(getAnn D)) -> exists v, E x = Some v)
  -> @sim _ statetype_F _ statetype_F bot3 Sim (L, E, s) (L, E, t).

Proof.
  intros Unsat_check Eq_FVars RenApart ssa_s ssa_t [nf_s nc_s] [nf_t nc_t] val_def.
  pose proof (@noFun_impl_term_crash E s nf_s nc_s) as term_crash_s.
  destruct term_crash_s as [Es [s' term_crash_s]].
  pose proof (@noFun_impl_term_crash E t nf_t nc_t) as term_crash_t.
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
      * pose proof (crash_impl_models L L D' t E Et t' ssa_t fv_def nf_t nc_t crash_t (fun _ => fun _ => true)).
        pose proof (combineEnv_agree (fst (getAnn D) ∪ snd(getAnn D)) Es Et)
          as agree_combineEnv.
        specialize (Unsat_check (fun _ => fun _ => true) (to_total (combineEnv (fst (getAnn D) ∪ snd(getAnn D)) Es Et))).
        exfalso.
        apply Unsat_check; simpl; split.
        { eapply models_agree; eauto.
          eapply agree_on_total.
          eapply (agree_on_incl (lv:= fst (getAnn D) ∪ snd(getAnn D) )); eauto.
          cset_tac'.
          pose proof (freeVars_incl s D source ssa_s nf_s a H0); cset_tac. }
        { pose proof (freeVars_incl t D' target ssa_t nf_t).
          rewrite <- models_agree; eauto.
          eapply agree_on_total.
          rewrite freeVars_translateStmt, occurVars_freeVars_definedVars.
          rewrite renamedApart_freeVars, renamedApart_occurVars; eauto.
          rewrite <- Eq_FVars. symmetry.
          eapply agree_on_incl; [ eapply combineEnv_agree_meet | reflexivity].
          exploit nc_step_agree; try eapply term_s; eauto.
          exploit nc_step_agree; try eapply crash_t; eauto.
          rewrite <- Eq_FVars in H2. rewrite H1 in H2; clear H1.
          eapply agree_on_incl; eauto.
          cset_tac; eauto.
        }
  (** s crasht --> always sim *)
  - destruct crash_s.
    pfold. eapply SimErr; eauto using nc_star_step, nc_stuck_result_none, nc_stuck_terminal.
Qed.