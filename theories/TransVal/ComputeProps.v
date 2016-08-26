Require Import List CSet MapDefined.
Require Import AutoIndTac Annotation Exp IL RenamedApart Util.
Require Import SetOperations Sim.
Require Import SMT NoFun.
Require Import Guards ILFtoSMT GuardProps.

(** All terminating source translations can be modeled with the end environment **)

Lemma terminates_impl_models L s D E s' E'
  : renamedApart s D
    -> noFun s
    -> Terminates (L,E, s) (L, E', s')
    ->  models (fun (f:pred) (x:list val) => true)  (to_total E')  (translateStmt s source).
Proof.
  intros ren_s noFun_s [Term_s Trm].
  general induction Term_s; simpl.
  - invt nc_terminal.
    + eapply models_guardGen_source; simpl. split; eauto.
      eapply guard_true_if_eval; eauto.
    + eapply models_guardGen_source; simpl; split; eauto.
      eapply guardList_true_if_eval; eauto.
  - exploit nc_step_agree as AGR1; eauto using star_step.
    destruct H.
    inv H; invt renamedApart; invt noFun; simpl in * |- *; subst; eauto;
      exploit nc_step_agree' as AGR2; eauto; simpl in *; pe_rewrite.
    + eapply models_guardGen_source; simpl; split; [eauto | split; eauto].
      * eapply (guard_true_if_eval _ E' e v ); eauto.
        eapply op_eval_agree; eauto.
        eapply agree_on_incl; eauto.
      * eapply smt_eval_var; eauto with cset.
    + erewrite models_guardGen_source. simpl; split.
      * eapply guard_true_if_eval.
        eapply op_eval_agree; eauto with cset.
      * erewrite op_eval_smt_eval; eauto using op_eval_agree with cset.
        rewrite condTrue.
        eauto.
    + erewrite models_guardGen_source. simpl; split.
      * eapply guard_true_if_eval.
        eapply op_eval_agree; eauto with cset.
      * erewrite op_eval_smt_eval; eauto using op_eval_agree with cset.
        rewrite condFalse.
        eauto.
Qed.

(** Lemmata for Crash **)

Definition failed (s:F.state)  := result (s ) = None.

(** Lemma 11 in the thesis
Proves that crashing target programs can be modeled by any
predicate environment and the environment in which they crash **)
Lemma crash_impl_models L L' D s E Es s'
  : renamedApart s D
    -> defined_on (fst (getAnn D)) E
    -> noFun s
    -> Crash (L, E, s) (L', Es, s')
    -> forall F, models F (to_total Es) (translateStmt s target).

Proof.
  intros RA DEF NF [Star Crsh] F.
  general induction Star; simpl.
  - invt nc_stuck.
    + eapply models_guardGen_target.
      simpl; intros.
      eapply (undefList_models F Es Y); eauto.
      inv RA; simpl in *. eauto using defined_on_incl.
    + inv RA; invt noFun; invt notApp; simpl;
        eapply models_guardGen_target; simpl in *; intros.
      * exploit nostep_let; eauto.
        exfalso. eapply undef_models; eauto using defined_on_incl with cset.
      * exploit nostep_if; eauto.
        exfalso. eapply undef_models; eauto using defined_on_incl with cset.
      * eapply undef_models; eauto using defined_on_incl with cset.
  - exploit nc_step_agree as AGR1; eauto using star_step.
    destruct H; simpl in *.
    inversion H; intros; subst; try isabsurd;
    invt renamedApart; invt noFun; subst; simpl;
      eapply models_guardGen_target; simpl in *; intros;
        exploit nc_step_agree' as AGR2; eauto; simpl in *; pe_rewrite.
    + split; eauto.
      * eapply smt_eval_var; eauto with cset.
      * eapply IHStar; eauto.
        pe_rewrite. eapply defined_on_update_some.
        eapply defined_on_incl; eauto. clear; cset_tac.
    + erewrite op_eval_smt_eval; eauto using op_eval_agree with cset.
      rewrite condTrue.
      eapply IHStar; eauto.
      pe_rewrite. eauto using defined_on_incl with cset.
    + erewrite op_eval_smt_eval; eauto using op_eval_agree with cset.
      rewrite condFalse.
      eapply IHStar; eauto.
      pe_rewrite. eauto using defined_on_incl with cset.
Qed.