Require Import Util LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp MoreExp Env IL SimF.

Set Implicit Arguments.
Unset Printing Records.

Lemma bisim'r_refl s
  : forall L E r,
    @sim'r F.state _ F.state _ r Bisim (L, E, s) (L, E, s).
Proof.
  revert s. pcofix CIH.
  intros; destruct s; simpl in *; intros.
  - case_eq (exp_eval E e); intros.
    + pone_step. right. eapply (CIH); eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step. right. eapply (CIH s1); eauto.
    + pone_step. right. eapply (CIH s2); eauto.
    + pno_step.
  - edestruct (get_dec L (counted l)) as [[b]|].
    decide (length Y = length (block_Z b)).
    case_eq (omap (exp_eval E) Y); intros.
    + pone_step. right. eapply CIH.
    + pno_step.
    + pno_step.
    + pno_step; eauto.
  - pno_step.
  - case_eq (omap (exp_eval E) Y); intros.
    + pextern_step.
      * right. eapply (CIH s); eauto.
      * right. eapply (CIH s); eauto.
    + pno_step.
  - pone_step. right.
    eapply (CIH s); eauto using sawtooth_F_mkBlocks.
Qed.

Instance SR : ProofRelation (params) := {
   ParamRel G Z Z' := Z = Z' /\ Z = G;
   ArgRel G VL VL' := VL = VL' /\ length VL = length G;
   IndexRel AL n n' := n = n';
   Image AL := length AL
}.
Proof.
  - intros; dcr; subst; split; congruence.
  - intros; subst; eauto.
Defined.


Definition bisimeq t s s' :=
  forall L L' E, simLabenv t bot3 SR (block_Z ⊝ L) L L'
            -> ❬L❭ = ❬L'❭
            -> sim'r bot3 t (L, E, s) (L', E, s').

Definition bisimeq' t r s s' :=
    forall L L' E, simLabenv t r SR (block_Z ⊝ L) L L'
            -> ❬L❭ = ❬L'❭
            -> sim'r r t (L, E, s) (L', E, s').


Lemma bisimeq'_refl s t
  : forall L L' E r,
    simLabenv t r SR (block_Z ⊝ L) L L'
    -> ❬L❭ = ❬L'❭
    -> sim'r r t (L, E, s) (L', E, s).
Proof.
  unfold sim'r. sind s; destruct s; simpl in *; intros.
  - case_eq (exp_eval E e); intros.
    + pone_step; eauto.
    + time pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step. left. eapply (IH s1); eauto.
    + pone_step. left. eapply (IH s2); eauto.
    + pno_step.
  - destruct H; dcr.
    edestruct (get_dec L (counted l)) as [[b]|]; [ inv_get | ].
    decide (length Y = length (F.block_Z b)).
    case_eq (omap (exp_eval E) Y); intros.
    + destruct b, x.
      eapply H1; eauto; simpl; eauto with len.
    + pno_step.
    + pno_step. destruct b,x; simpl in *.
      exploit H1; eauto; simpl in *; dcr; subst.
      congruence.
    + pno_step. inv_get. eauto.
  - pno_step.
  - case_eq (omap (exp_eval E) Y); intros.
    + pextern_step; eauto.
    + pno_step.
  - pone_step. left.
    eapply (IH s); eauto with len.
    rewrite map_app.
    eapply simLabenv_extension_len; eauto with len.
    + intros; hnf; intros; inv_get; eauto.
      simpl in *; dcr; subst. get_functional.
      eapply IH; eauto with len. rewrite map_app; eauto.
    + hnf; intros; simpl in *; subst; inv_get; simpl; eauto.
    + simpl; eauto with len.
Qed.

Lemma bisimeq_refl t s
: bisimeq t s s.
Proof.
  hnf; intros.
  eapply bisimeq'_refl; eauto.
Qed.

Lemma bisimeq'_bisimeqid t s s'
: (forall (L:F.labenv) E, sim'r bot3 t (L, E, s) (L, E, s'))
  -> bisimeq t s s'.
Proof.
  intros; hnf; intros.
  eapply sim'_trans with (S2:=F.state).
  eapply H.
  eapply bisimeq'_refl; eauto.
Qed.

Lemma get_mutual_block (A B : Type) (H : BlockType B)
      (C : Type) (H0 : BlockType C) (R : A -> B -> C -> Prop) L1 L2 AL n
      (LEN1:length L1 = length L2) (LEN2:length AL = length L1)
  : tooth n L1
    -> tooth n L2
    -> (forall n a b1 b2, get AL n a -> get L1 n b1 -> get L2 n b2 -> R a b1 b2)
    -> mutual_block R n AL L1 L2.
Proof.
  intros. length_equify.
  general induction LEN1; inv LEN2; eauto using @mutual_block.
  - inv H1; inv H2. econstructor; eauto 20 using get.
Qed.

Lemma tooth_get_n (B : Type) (H : BlockType B) n L i b
  : tooth n L
    -> get L i b
    -> block_n b = n + i.
Proof.
  intros. general induction H0. inv H1.
  inv H2. omega.
  exploit IHtooth. eauto. omega.
Qed.

Lemma simL'_refl r L
  : sawtooth L
    -> simLabenv Bisim r SR (List.map F.block_Z L) L L.
Proof.
  intros. hnf; dcr; split; eauto using @sawtooth with len.
  intros [] []; intros; simpl in *; subst; inv_get; split; eauto.
  intros; dcr; simpl in *; subst.
  pone_step; simpl; eauto with len. left.
  eapply bisim'r_refl.
Qed.

(** * Contextual Equivalence *)

Inductive stmtCtx : Type :=
| ctxExp    (x : var) (e: exp) (C : stmtCtx) : stmtCtx
| ctxIfS     (e : exp) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxIfT     (e : exp) (s : stmt) (C : stmtCtx) : stmtCtx
(* block f Z : rt = s in b  *)
| ctxLetS    (F1: list (params*stmt)) (Z:params) (C : stmtCtx) (F2: list (params*stmt)) (t : stmt) : stmtCtx
| ctxLetT    (F: list (params*stmt)) (C : stmtCtx) : stmtCtx
| ctxExtern (x : var)  (f:external) (e:args) (C:stmtCtx) : stmtCtx
| ctxHole.

Fixpoint fill (ctx:stmtCtx) (s':stmt) : stmt :=
  match ctx with
    | ctxExp x e ctx => stmtLet x e (fill ctx s')
    | ctxIfS e ctx t => stmtIf e (fill ctx s') t
    | ctxIfT e s ctx => stmtIf e s (fill ctx s')
    | ctxLetS F1 Z ctx F2 t => stmtFun (F1 ++ (Z,fill ctx s')::F2) t
    | ctxLetT F ctx => stmtFun F (fill ctx s')
    | ctxExtern x f e ctx => stmtExtern x f e (fill ctx s')
    | ctxHole => s'
  end.

Fixpoint fillC (ctx:stmtCtx) (s':stmtCtx) : stmtCtx :=
  match ctx with
    | ctxExp x e ctx => ctxExp x e (fillC ctx s')
    | ctxIfS e ctx t => ctxIfS e (fillC ctx s') t
    | ctxIfT e s ctx => ctxIfT e s (fillC ctx s')
    | ctxLetS F1 Z ctx F2 t => ctxLetS F1 Z (fillC ctx s') F2 t
    | ctxLetT F ctx => ctxLetT F (fillC ctx s')
    | ctxExtern x f e ctx => ctxExtern x f e (fillC ctx s')
    | ctxHole => s'
  end.

Lemma simeq_contextual' s s' ctx r
: (forall r, bisimeq' Bisim r s s')
  -> bisimeq' Bisim r (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros; eauto.
  - case_eq (exp_eval E e); intros.
    + pone_step. left. eapply IHctx; eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step; left; eapply IHctx; eauto.
    + pone_step. left.
      eapply bisimeq'_refl; eauto.
    + pno_step.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    + pone_step. left.
      eapply bisimeq'_refl; eauto.
    + pone_step; left; eapply IHctx; eauto.
    + pno_step.
  - pone_step. left.
    eapply bisimeq'_refl; eauto 20 with len.
    rewrite map_app.
    eapply simLabenv_extension_len; simpl; eauto 20 with len.
    + intros; hnf; intros.
      { destruct (get_subst _ _ _ H4) as [? |[?|?]].
        - inv_get; simpl in *; dcr; subst.
          simpl; repeat split; eauto. inv_get.
          eapply bisimeq'_refl; eauto 20 with len.
          rewrite map_app. eauto.
        - simpl in *. dcr; subst. subst. invc H9.
          inv_get. simpl in *.
          eapply IHctx; eauto 20 with len.
          rewrite map_app. eauto.
        - simpl in *; dcr; subst.
          inv_get. simpl in *.
          eapply bisimeq'_refl; eauto 20 with len.
          rewrite map_app; eauto.
      }
    + hnf; intros; simpl in *; subst; inv_get; simpl.
      destruct (get_subst _ _ _ H4) as [? |[?|?]].
      * inv_get; simpl in *; dcr; subst; eauto.
      * dcr; subst. invc H5. inv_get; eauto with len.
      * simpl in *; dcr; subst. inv_get; eauto.
  - pone_step. left.
    eapply IHctx; eauto with len.
    rewrite map_app.
    eapply simLabenv_extension_len; simpl; eauto 20 with len.
    + intros; hnf; simpl; intros; dcr; subst; inv_get. simpl in *.
      eapply bisimeq'_refl; eauto 20 with len.
      rewrite map_app; eauto.
    + hnf; simpl; intros; subst; inv_get; simpl; eauto.
  - case_eq (omap (exp_eval E) e); intros.
    + pextern_step.
      * left. eapply IHctx; eauto.
      * left. eapply IHctx; eauto.
    + pno_step.
  - eapply H; eauto.
Qed.

Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
  rewrite IHC; eauto.
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
