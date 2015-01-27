Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Bisim.

Set Implicit Arguments.
Unset Printing Records.

Instance SR : ProofRelation (params) := {
   ParamRel G Z Z' := Z = Z' /\ Z = G;
   ArgRel V V G VL VL' := VL = VL' /\ length VL = length G;
   BlockRel := fun Z b b' => length (F.block_Z b) = length Z
                           /\ length (F.block_Z b') = length Z
}.
intros; dcr; subst; split; congruence.
Defined.

Definition bisimeq s s' :=
  forall ZL L L' E, simL' _ bot2 SR ZL L L' -> bisim (L, E, s) (L', E, s').

Definition bisimeqid s s' :=
  forall (L:F.labenv) E, bisim (L, E, s) (L, E, s').


Definition bisimeq' r s s' :=
  forall ZL L L' E, simL' _ r SR ZL L L' -> bisim'r r (L, E, s) (L', E, s').

Ltac pone_step := pfold; eapply bisim'Silent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | left ].

Ltac pone_step' := pfold; eapply bisim'Silent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | right ].

Ltac pno_step := pfold; eapply bisim'Term;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2
                | stuck2  ].

Ltac pextern_step :=
  let STEP := fresh "STEP" in
  pfold; eapply bisim'Extern;
    [ eapply star2_refl
    | eapply star2_refl
    | try step_activated
    | try step_activated
    | intros ? ? STEP; inv STEP
    | intros ? ? STEP; inv STEP
    ].

Lemma bisimeq'_refl s
: forall ZL L L' E r,
    simL' _ r SR ZL L L'
    -> bisim'r r (L, E, s) (L', E, s).
Proof.
  unfold bisimeq; intros. general induction s.
  - case_eq (exp_eval E e); intros.
    + pone_step. eapply IHs; eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step. eapply IHs1; eauto.
    + pone_step. eapply IHs2; eauto.
    + pno_step.
  - edestruct (get_dec L (counted l)) as [[b]|].
    decide (length Y = length (F.block_Z b)).
    case_eq (omap (exp_eval E) Y); intros.
    + edestruct AIR5_nth1 as [? [? [? []]]]; eauto; dcr.
      inv H7. eapply bisim_drop_shift.
      eapply paco2_mon. eapply H8; eauto.
      hnf; intuition. exploit omap_length; eauto.
      hnf in H6. hnf in H1; dcr. simpl in *.
      get_functional. subst b. simpl in *.
      congruence. eauto.
    + pno_step.
    + pno_step. exploit omap_length; eauto.
      get_functional; subst. congruence.
      edestruct AIR5_nth1 as [? [? [? []]]]; eauto; dcr.
      inv H6. hnf in H5; dcr. repeat get_functional; subst. simpl in *.
      congruence.
    + pno_step.
      * edestruct AIR5_nth1 as [? [? [? []]]]; eauto; dcr.
      * edestruct AIR5_nth2 as [? [? [? []]]]; eauto; dcr. eauto.
  - pno_step.
  - case_eq (omap (exp_eval E) Y); intros.
    + pextern_step.
      * eexists; split.
        econstructor; eauto.
        left. eapply IHs; eauto.
      * eexists; split.
        econstructor; eauto.
        left. eapply IHs; eauto.
    + pno_step.
  - pone_step.
    eapply IHs2; eauto.
    eapply simL_extension'; hnf; intros; eauto.
    hnf in H; dcr; subst.
    split; simpl; eauto. intros; dcr; subst.
    eapply IHs1; eauto.
Qed.

Lemma bisimeq_refl s
: bisimeq s s.
Proof.
  hnf; intros. eapply bisim'_bisim.
  eapply bisimeq'_refl; eauto.
Qed.

Lemma bisimeq'_bisimeqid s s'
: bisimeqid s s'
  -> bisimeq s s'.
Proof.
  intros; hnf; intros.
  hnf in H. eapply bisim_trans with (S2:=F.state).
  eapply H. eapply bisim'_bisim.
  eapply bisimeq'_refl; eauto.
Qed.

Lemma simL'_refl r L
: AIR5 (simB bisim_progeq r SR) L L (List.map F.block_Z L) L L.
Proof.
  intros.
  general induction L; simpl.
  - econstructor.
  - econstructor.
    + destruct a. econstructor; eauto; try now (clear_all; intuition).
      * intros. hnf.
        hnf in H1; dcr; subst; simpl in *.
        exploit omap_length; eauto.
        exploit omap_length; try eapply H0; eauto.
        pone_step; eauto using get; simpl; eauto; try congruence.
        eapply paco2_mon. eapply bisim'_refl. clear_all; firstorder.
    + eapply IHL.
Qed.

(** * Contextual Equivalence *)

Inductive stmtCtx : Type :=
| ctxExp    (x : var) (e: exp) (C : stmtCtx) : stmtCtx
| ctxIfS     (e : exp) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxIfT     (e : exp) (s : stmt) (C : stmtCtx) : stmtCtx
(* block f Z : rt = s in b  *)
| ctxLetS    (Z:params) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxLetT    (Z:params) (s : stmt) (C : stmtCtx) : stmtCtx
| ctxExtern (x : var)  (f:external) (e:args) (C:stmtCtx) : stmtCtx
| ctxHole.

Fixpoint fill (ctx:stmtCtx) (s':stmt) : stmt :=
  match ctx with
    | ctxExp x e ctx => stmtExp x e (fill ctx s')
    | ctxIfS e ctx t => stmtIf e (fill ctx s') t
    | ctxIfT e s ctx => stmtIf e s (fill ctx s')
    | ctxLetS Z ctx t => stmtLet Z (fill ctx s') t
    | ctxLetT Z s ctx => stmtLet Z s (fill ctx s')
    | ctxExtern x f e ctx => stmtExtern x f e (fill ctx s')
    | ctxHole => s'
  end.

Fixpoint fillC (ctx:stmtCtx) (s':stmtCtx) : stmtCtx :=
  match ctx with
    | ctxExp x e ctx => ctxExp x e (fillC ctx s')
    | ctxIfS e ctx t => ctxIfS e (fillC ctx s') t
    | ctxIfT e s ctx => ctxIfT e s (fillC ctx s')
    | ctxLetS Z ctx t => ctxLetS Z (fillC ctx s') t
    | ctxLetT Z s ctx => ctxLetT Z s (fillC ctx s')
    | ctxExtern x f e ctx => ctxExtern x f e (fillC ctx s')
    | ctxHole => s'
  end.


Lemma subst_lemma a s s' V E E' Z Z' L1 L2 t
:
  ParamRel a Z Z'
  -> BlockRel a (F.blockI E Z s) (F.blockI E' Z' s')
  -> paco2 (@bisim_gen F.state _ F.state _) bot2 ((L2 ++ F.blockI E Z s :: L1)%list, V, t)
         ((L2 ++ F.blockI E' Z' s' :: L1)%list, V, t).
Proof.
  revert_all; pcofix CIH; intros.
  destruct t.
  - case_eq (exp_eval V e); intros.
    + pone_step'. eapply CIH; eauto.
    + pno_step.
  - case_eq (exp_eval V e); intros.
    case_eq (val2bool v); intros.
    + pone_step'; eapply CIH; eauto.
    + pone_step'; eapply CIH; eauto.
    + pno_step.
  - edestruct (get_dec (L2 ++ F.blockI E Z s :: L1) (counted l)) as [[]|].
    admit. admit.
  - pno_step.
  - case_eq (omap (exp_eval V) Y); intros.
    + pextern_step.
      * eexists; split.
        econstructor; eauto.
        right. eapply CIH; eauto.
      * eexists; split.
        econstructor; eauto.
        right. eapply CIH; eauto.
    + pno_step.
  - pone_step'.
    rewrite cons_app. rewrite (cons_app _ (L2 ++ F.blockI E' Z' s' :: L1)).
    repeat rewrite app_assoc.
    eapply CIH; eauto.
Qed.


Lemma simeq_contextual' s s' ctx
: bisimeqid s s'
  -> bisimeqid (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros; eauto.
  - case_eq (exp_eval E e); intros.
    + one_step. eapply IHctx; eauto.
    + no_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + one_step; eapply IHctx; eauto.
    + one_step.
      eapply bisim_refl; eauto.
    + no_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + one_step. eapply bisim_refl; eauto.
    + one_step; eapply IHctx; eauto.
    + no_step.
  - one_step.
    + admit.
  - one_step.
    eapply IHctx; eauto.
  - case_eq (omap (exp_eval E) e); intros.
    + extern_step.
      * eexists; split.
        econstructor; eauto.
        eapply IHctx; eauto.
      * eexists; split.
        econstructor; eauto.
        eapply IHctx; eauto.
    + no_step.
Qed.

(*
Lemma simeq_contextual'' s s' ctx
: bisimeq' bot2 s s'
  -> bisimeq' bot2 (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros; eauto.
  - case_eq (exp_eval E e); intros.
    + pone_step. eapply IHctx; eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step; eapply IHctx; eauto.
    + pone_step.
      eapply bisimeq'_refl; eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step. eapply bisimeq'_refl; eauto.
    + pone_step; eapply IHctx; eauto.
    + pno_step.
  - pone_step.
    + eapply subst_lemma; hnf; intros; eauto.
      * admit.
      * eapply bisimeq'_refl; eauto.
      hnf in H1; dcr; subst.
      eapply IHctx; eauto.
      hnf; intros.
      eapply bisimeq'_refl; eauto.
      eapply simL_extension'; hnf; intros; eauto.
      hnf in H1; dcr; subst.
      eapply IHctx; eauto.
      hnf; intros. eapply paco2_mon; eauto.
      eapply H.
  - pone_step.
    eapply IHctx; eauto.
    eapply simL_extension'; hnf; intros; eauto.
    hnf in H2; dcr; subst.
    eapply bisimeq'_refl; eauto.
  - case_eq (omap (exp_eval E) e); intros.
    + pextern_step.
      * eexists; split.
        econstructor; eauto.
        left. eapply IHctx; eauto.
      * eexists; split.
        econstructor; eauto.
        left. eapply IHctx; eauto.
    + pno_step.
  - eapply paco2_mon. eapply H; eauto.
Qed.
*)
Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
Qed.

(*
Lemma ctx_constr_E E' G G'
  : exists C, forall E, exists EC, forall (L:list F.block) s, star step (L, E, fill C s) (L, EC, s)
                    /\ agree_on eq G EC E'
                    /\ agree_on eq (G'\G) EC E.
Proof.
  pattern G. eapply set_induction.
  intros. eexists ctxHole. intros. eexists E.
  split. eapply star_refl. eapply empty_is_empty_1 in H.  rewrite H.
  split. hnf; intros; cset_tac; intuition. eapply agree_on_refl.
  intros. edestruct H as [C' ?].
  eexists (fillC C' (ctxExp x (Con (E' x)) ctxHole)).
  intros. specialize (H2 E). destruct H2 as[EC' ?].
  eexists (EC'[x<-E' x]). intros. rewrite fill_fillC.
  split. simpl. eapply star_right. eapply H2.
  econstructor. simpl; eauto.
  split. hnf; intros. lud; eqs. rewrite e. eauto.
  eapply H2; eauto. edestruct H1. specialize (H6 H3). destruct H6; intuition.
  eapply agree_on_update_dead. cset_tac; intuition. eapply H5. eapply H1; intuition.
  eapply agree_on_incl; eauto. eapply H2; eauto. eapply Add_Equal in H1.
  rewrite H1. cset_tac; intuition.
Qed.

Lemma ctx_constr (L:list F.block) E G L'
  : exists C E' LC, forall s, star step (L, E, fill C s) ((LC++L)%list, E', s)
                    /\ agree_on G E E'
                    /\ PIR2 approx LC L'.
Proof.
  intros. general induction L'.
  + eexists ctxHole, E, nil; simpl.
    repeat split. eapply star_refl. constructor.
  + destruct a.
    edestruct (ctx_constr_E block_E (freeVars block_s) ∅) as [CE].
    edestruct (ctx_constr_E E G) as [CE2]. instantiate (1:=∅) in H0.
    edestruct (IHL' L E G) as [CR [ER [LC' ]]].
    specialize (H ER). destruct H as [CEE ?].
    specialize (H0 CEE). destruct H0 as [CEE2 ?].
    eexists (fillC CR (fillC CE (ctxLetT block_Z block_s CE2))).
    eexists CEE2, (F.blockI CEE block_Z block_s:: LC').
    intros. rewrite fill_fillC.
    specialize (H (LC'++L)%list (fill (ctxLetT block_Z block_s CE2) s)).
    split. eapply star_trans. eapply H1.
    rewrite fill_fillC. eapply star_trans.
    eapply H. simpl. eapply S_star. econstructor.
    dcr. edestruct H0. eapply H.
    split. eapply agree_on_sym. eapply H0; eauto.
    econstructor. econstructor. eapply agree_on_incl. eapply H.
    eapply incl_minus. eapply H1; eauto.
Qed.


Lemma ctxeq_simeq s s':
  ctxeq s s' <-> simeq s s'.
Proof.
  split; intros.
  hnf; intros. edestruct (ctx_constr (nil:list F.block) E (freeVars s ∪ freeVars s')) as [C [E' [LC ?]]].
  specialize (H C E); simpl in *.
  eapply sim_cobehave in H; eauto.
  pose proof (H0 s). specialize (H0 s'); dcr.
  pose proof (sim_reduction_closed H H2 H1).
  repeat rewrite app_nil_r in H0.
  eapply sim_coincidence; eauto.
  symmetry; eauto.
  hnf; intros.
  eapply sim_cobehave. eapply simeq_contextual; eauto.
Qed.

Instance ctxeq_equivalence : Equivalence ctxeq.
Proof.
  hnf; intros. constructor.
  hnf; intros. eapply ctxeq_simeq; reflexivity.
  hnf; intros. eapply ctxeq_simeq; eapply ctxeq_simeq in H; symmetry; eauto.
  hnf; intros. eapply ctxeq_simeq. eapply ctxeq_simeq in H; eapply ctxeq_simeq in H0;
                                   transitivity y; eauto.
Qed.

*)


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
