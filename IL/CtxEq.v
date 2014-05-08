Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sim.

Set Implicit Arguments.
Unset Printing Records.

(** * Contextual Equivalence *)

Inductive stmtCtx : Type :=
| ctxExp    (x : var) (e: exp) (C : stmtCtx) : stmtCtx
| ctxIfS     (e : exp) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxIfT     (e : exp) (s : stmt) (C : stmtCtx) : stmtCtx
(* block f Z : rt = s in b  *)
| ctxLetS    (Z:params) (C : stmtCtx) (t : stmt) : stmtCtx 
| ctxLetT    (Z:params) (s : stmt) (C : stmtCtx) : stmtCtx
| ctxHole.

Fixpoint fill (ctx:stmtCtx) (s':stmt) : stmt :=
  match ctx with
    | ctxExp x e ctx => stmtExp x e (fill ctx s')
    | ctxIfS e ctx t => stmtIf e (fill ctx s') t
    | ctxIfT e s ctx => stmtIf e s (fill ctx s')
    | ctxLetS Z ctx t => stmtLet Z (fill ctx s') t 
    | ctxLetT Z s ctx => stmtLet Z s (fill ctx s')
    | ctxHole => s'
  end.

Fixpoint fillC (ctx:stmtCtx) (s':stmtCtx) : stmtCtx :=
  match ctx with
    | ctxExp x e ctx => ctxExp x e (fillC ctx s')
    | ctxIfS e ctx t => ctxIfS e (fillC ctx s') t
    | ctxIfT e s ctx => ctxIfT e s (fillC ctx s')
    | ctxLetS Z ctx t => ctxLetS Z (fillC ctx s') t 
    | ctxLetT Z s ctx => ctxLetT Z s (fillC ctx s')
    | ctxHole => s'
  end.

Definition ctxeq (s s':stmt) :=
  forall ctx E, cobehave (nil:list F.block, E, (fill ctx s)) (nil:list F.block, E, (fill ctx s')).

Lemma simeq_contextual s s' ctx
  : simeq s s' -> simeq (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros.
  + destruct (step_dec (L, E, stmtExp x e (fill ctx s))). destruct H0.
    inv H0.
    eapply simS; simpl; eauto using plus, F.step. eapply IHctx; eauto.
    eapply simE; try eapply star_refl. eauto. eauto.
    simpl. destruct 1. inv H1. eapply H0. 
    econstructor. econstructor; eauto.
  + case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    eapply simS.
    econstructor. econstructor; eauto.
    econstructor; econstructor; eauto. eapply IHctx; eauto.
    eapply simS.
    econstructor. eapply F.stepIfF; eauto.
    econstructor; eapply F.stepIfF; eauto.
    eapply sim_refl.
    eapply simE; try eapply star_refl; eauto; stuck.
  + case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    eapply simS; auto.
    econstructor. econstructor; eauto.
    econstructor; econstructor; eauto.
    eapply sim_refl.
    eapply simS.
    econstructor. eapply F.stepIfF; eauto.
    econstructor; eapply F.stepIfF; eauto. eapply IHctx; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
  + eapply simS.
    eapply plusO. econstructor.
    eapply plusO. econstructor.
    specialize (IHctx _ _ H).
    eapply obseq_simeq in IHctx.
    pose proof (subst_lemma E E Z L t IHctx). eauto.
  + econstructor.
    econstructor; econstructor.
    econstructor; econstructor.
    eapply IHctx; eauto.
  + eapply H; eauto using lsim_refl.
Qed. 

Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
Qed.


Lemma ctx_constr_E E' G G' 
  : exists C, forall E, exists EC, forall (L:list F.block) s, star step (L, E, fill C s) (L, EC, s) 
                    /\ agree_on G EC E'
                    /\ agree_on (G'\G) EC E.
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



(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)

