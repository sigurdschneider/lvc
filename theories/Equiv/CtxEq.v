Require Import Util MapDefined LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp Envs IL SimF.

Set Implicit Arguments.
Unset Printing Records.

(** * Program Equivalence *)

Instance SR : PointwiseProofRelationF (nat) := {
   ParamRelFP G Z Z' := ❬Z❭ = ❬Z'❭ /\ ❬Z❭ = G;
   ArgRelFP E E' G VL VL' := VL = VL' /\ length VL = G;
}.

Definition bisimeq r t s s' :=
    forall L L' E, labenv_sim t (sim r) SR (@length _ ⊝ F.block_Z ⊝ L') L L'
            -> ❬L❭ = ❬L'❭
            -> sim r t (L:F.labenv, E, s) (L', E, s').

(** ** Reflexivity *)

Lemma bisimeq_refl s t
  : forall L L' E r,
    labenv_sim t (sim r) SR (@length _ ⊝ block_Z ⊝ L') L L'
    -> sim r t (L, E, s) (L', E, s).
Proof.
  sind s; destruct s; simpl in *; intros.
  - destruct e.
    + eapply (sim_let_op il_statetype_F); eauto.
    + eapply (sim_let_call il_statetype_F); eauto.
  - eapply (sim_cond il_statetype_F); eauto.
  - edestruct (get_dec L' (counted l)) as [[b]|]; [ inv_get | ].
    + eapply labenv_sim_app; eauto.
      simpl.
      intros; split; intros; dcr; inv_get; simpl in *; subst; try cases; eauto with len.
    + pno_step. edestruct H; eauto. len_simpl. inv_get.
  - pno_step.
  - pone_step. left.
    eapply (IH s); eauto with len.
    rewrite !map_app. intros.
    eapply labenv_sim_extension_ptw; eauto with len.
    + intros; hnf; intros; inv_get; eauto.
      simpl in *; dcr; subst. get_functional.
      eapply IH; eauto with len. rewrite !map_app; eauto.
    + hnf; intros; simpl in *; subst; inv_get; simpl; eauto.
Qed.

Lemma labenv_sim_refl t r L
  : smaller L
    -> labenv_sim t (sim r) SR (@length _ ⊝ F.block_Z ⊝ L) L L.
Proof.
  intros. hnf; dcr; do 4 try split; eauto with len.
  - intros [] []; intros; simpl in *; subst; inv_get; split; eauto.
  - split. hnf; intros; simpl in *; inv_get; eauto.
    hnf; intros; simpl in *. destruct f, f'; simpl in *; subst.
    get_functional; dcr; subst; inv_get.
    pone_step; simpl; eauto with len.
    left. eapply sim_refl.
Qed.

Lemma labenv_sim_sym L L'
  : labenv_sim Bisim (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L') L L'
    -> labenv_sim Bisim (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L) L' L.
Proof.
  intros []; intros; dcr; do 4 (try split; eauto with len).
  - hnf; intros. destruct f,f'; simpl in *; subst.
    exploit (H2 (LabI n0) (LabI n0)); eauto. simpl in *. dcr; subst; eauto.
    inv_get. eauto.
  - split.
    + hnf; intros; simpl in *; inv_get; eauto.
    + hnf; intros.
      eapply bisim_sym. simpl in *; dcr; subst.
      destruct f, f'; simpl in *; subst.
      eapply H6; eauto. simpl. eauto with len.
Qed.


Lemma bisimeq_sym s1 s2
  : bisimeq bot3 Bisim s1 s2
    -> bisimeq bot3 Bisim s2 s1.
Proof.
  intros. hnf; intros.
  eapply bisim_sym. eapply H; eauto.
  eapply labenv_sim_sym; eauto.
Qed.

Lemma bisimeq_trans t s1 s2 s3
  : bisimeq bot3 t s1 s2
    -> bisimeq bot3 t s2 s3
    -> bisimeq bot3 t s1 s3.
Proof.
  intros. hnf; intros.
  eapply sim_trans with (S2:=F.state). eauto.
  eapply H0; eauto.
  intros. eapply labenv_sim_refl; eauto.
  eapply H1; eauto.
Qed.

Lemma labenv_sim_trans t (L1 L2 L3:F.labenv)
  : labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L2) L1 L2
    -> labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L3) L2 L3
    -> labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L3) L1 L3.
Proof.
  intros.
  assert (❬L1❭ = ❬L2❭). {
    destruct H; dcr. rewrite <- H. eauto with len.
  }
  assert (❬L2❭ = ❬L3❭). {
    destruct H0; dcr. rewrite <- H0. eauto with len.
  }
  hnf; dcr; do 4 try split; eauto with len.
  - destruct H, H0; dcr; eauto.
  - eapply H.
  - hnf; intros; simpl in *; destruct f,f'; simpl in *; subst; inv_get.
    simpl. destruct x.
    destruct H as [_ [_ [_ [PA1 _]]]]. destruct H0 as [_ [_ [_ [PA2 _]]]].
    exploit (PA1 (LabI n0) (LabI n0)); eauto; simpl in *; dcr; subst.
    exploit (PA2 (LabI n0) (LabI n0)); eauto; simpl in *; dcr; subst.
    split; omega.
  - split.
    + hnf; intros; simpl in *; inv_get; eauto.
    + hnf; intros; simpl in *. destruct f, f'; simpl in *; subst.
      inv_get; dcr; subst; simpl in *.
      eapply sim_trans with (S2:=F.state).
      eapply labenv_sim_app; eauto.
      Focus 2.
      eapply labenv_sim_app; eauto.
      intros; simpl in *; dcr; repeat subst; repeat get_functional.
      split; intros; eauto with len. cases; split; eauto. congruence.
      intros; simpl in *; dcr. destruct x; simpl in *.
      repeat subst; repeat get_functional.
      split; intros; eauto. eexists; split; eauto. split; eauto with len.
      split; eauto with len. congruence.
      cases; eauto. split; intros. congruence.
      eauto with len.
Qed.

(** * Contextual Equivalence *)

Inductive stmtCtx : Type :=
| ctxExp    (x : var) (e: exp) (C : stmtCtx) : stmtCtx
| ctxIfS     (e : op) (C : stmtCtx) (t : stmt) : stmtCtx
| ctxIfT     (e : op) (s : stmt) (C : stmtCtx) : stmtCtx
(* block f Z : rt = s in b  *)
| ctxLetS    (F1: list (params*stmt)) (Z:params) (C : stmtCtx) (F2: list (params*stmt)) (t : stmt) : stmtCtx
| ctxLetT    (F: list (params*stmt)) (C : stmtCtx) : stmtCtx
| ctxHole.

Fixpoint fill (ctx:stmtCtx) (s':stmt) : stmt :=
  match ctx with
    | ctxExp x e ctx => stmtLet x e (fill ctx s')
    | ctxIfS e ctx t => stmtIf e (fill ctx s') t
    | ctxIfT e s ctx => stmtIf e s (fill ctx s')
    | ctxLetS F1 Z ctx F2 t => stmtFun (F1 ++ (Z,fill ctx s')::F2) t
    | ctxLetT F ctx => stmtFun F (fill ctx s')
    | ctxHole => s'
  end.

Fixpoint fillC (ctx:stmtCtx) (s':stmtCtx) : stmtCtx :=
  match ctx with
    | ctxExp x e ctx => ctxExp x e (fillC ctx s')
    | ctxIfS e ctx t => ctxIfS e (fillC ctx s') t
    | ctxIfT e s ctx => ctxIfT e s (fillC ctx s')
    | ctxLetS F1 Z ctx F2 t => ctxLetS F1 Z (fillC ctx s') F2 t
    | ctxLetT F ctx => ctxLetT F (fillC ctx s')
    | ctxHole => s'
  end.

(** ** Program Equivalence is contextual *)

Lemma simeq_contextual p r s s' ctx
: (forall r, bisimeq r p s s')
  -> bisimeq r p (fill ctx s) (fill ctx s').
Proof.
  intros. general induction ctx; simpl; hnf; intros; eauto.
  - destruct e.
    + eapply (sim_let_op il_statetype_F); eauto.
      intros. left. eapply IHctx; eauto.
    + eapply (sim_let_call il_statetype_F); eauto.
      intros. left. eapply IHctx; eauto.
  - eapply (sim_cond il_statetype_F); eauto; intros; left.
    + eapply IHctx; eauto.
    + eapply bisimeq_refl; eauto.
  - eapply (sim_cond il_statetype_F); eauto; intros; left.
    + eapply bisimeq_refl; eauto.
    + eapply IHctx; eauto.
  - pone_step. left.
    eapply bisimeq_refl; eauto 20 with len.
    rewrite !map_app. intros.
    eapply labenv_sim_extension_ptw; simpl; eauto 20 with len.
    + intros; hnf; intros.
      { destruct (get_subst _ _ _ H5) as [? |[?|?]].
        - inv_get; simpl in *; dcr; subst.
          simpl; repeat split; eauto. inv_get.
          eapply bisimeq_refl; eauto 20 with len.
          rewrite !map_app. eauto.
        - simpl in *. dcr; subst. subst. invc H9.
          inv_get. simpl in *.
          eapply IHctx; eauto 20 with len.
          rewrite !map_app. intros; eauto.
        - simpl in *; dcr; subst.
          inv_get. simpl in *.
          eapply bisimeq_refl; eauto 20 with len.
          rewrite !map_app; eauto.
      }
    + hnf; intros; simpl in *; subst; inv_get; simpl.
      destruct (get_subst _ _ _ H4) as [? |[?|?]].
      * inv_get; simpl in *; dcr; subst; eauto.
      * dcr; subst. invc H5. inv_get; eauto with len.
      * simpl in *; dcr; subst. inv_get; eauto.
  - pone_step. left.
    eapply IHctx; eauto with len.
    rewrite !map_app. intros.
    eapply labenv_sim_extension_ptw; simpl; eauto 20 with len.
    + intros; hnf; simpl; intros; dcr; subst; inv_get. simpl in *.
      eapply bisimeq_refl; eauto 20 with len.
      rewrite !map_app; eauto.
    + hnf; simpl; intros; subst; inv_get; simpl; eauto.
  - eapply H; eauto.
Qed.

Lemma fun_congrunence p F F' t t' (LEN:length F = length F')
  : (forall r, bisimeq r p t t')
    -> (forall n Z s Z' s', get F n (Z, s) -> get F' n (Z', s') -> Z = Z' /\ forall r, bisimeq r p s s')
    -> forall r, bisimeq r p (stmtFun F t) (stmtFun F' t').
Proof.
  intros.
  hnf; intros.
  eapply sim_fun_ptw; eauto using labenv_sim_refl.
    + intros. left. eapply H; eauto with len.
      intros. rewrite !map_app. eauto.
    + intros. hnf; intros. inv_get. simpl in *; subst; dcr; subst.
      exploit H0; eauto; dcr; subst.
      eapply H11; eauto with len. rewrite !map_app; eauto with len.
    + hnf; intros. simpl in *; subst. exploit H0; eauto; dcr; subst.
      inv_get; eauto.
    + eauto with len.
Qed.

Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
  rewrite IHC; eauto.
Qed.

Definition lessDef (E E':onv val)
  := forall x , E' x = None -> E x = None.

Lemma ctx_constr_E (E':onv val) G G'
  : exists C, forall E, lessDef E E' ->
              exists EC, forall (L:list F.block) s,
                  star2 step (L, E, fill C s) nil (L, EC, s)
                  /\ agree_on eq G E' EC
                  /\ agree_on eq (G'\G) EC E.
Proof.
  revert G'.
  pattern G. eapply set_induction.
  - intros. eexists ctxHole. intros. eexists E. split.
    + eapply star2_refl.
    + eapply empty_is_empty_1 in H. rewrite H.
      split.
      * hnf; intros; cset_tac; intuition.
      * eapply agree_on_refl; eauto.
  - intros. eapply Add_Equal in H1.
    case_eq (E' x); intros.
    + edestruct H as [C' ?]; eauto using defined_on_incl with cset.
      eexists (fillC C' (ctxExp x (Operation (Con v)) ctxHole)).
      intros. specialize (H3 E). destruct H3 as[EC' ?]; eauto.
      eexists (EC'[x<-E' x]). intros. rewrite fill_fillC.
      split.
      * simpl.
        eapply (@star2_trans _ _ _ _ _ nil nil).
        -- eapply H3.
        -- rewrite H2. eapply star2_silent.
           single_step; simpl; eauto.
           eapply star2_refl.
      * split.
        -- hnf; intros. lud; eauto.
           ++ rewrite e. reflexivity.
           ++ eapply H3; eauto. rewrite H1 in H5. cset_tac.
        -- eapply agree_on_update_dead. rewrite H1. cset_tac; intuition.
           eapply agree_on_incl; eauto. eapply H3; eauto.
           rewrite H1. cset_tac.
    + edestruct (H ({x; G'})) as [C' ?]; eauto using defined_on_incl with cset.
      eexists C'.
      intros. specialize (H3 E H4).
      destruct H3 as[EC' ?]; eauto.
      eexists (EC').
      intros. edestruct H3; dcr; split; eauto.
      split.
      * rewrite H1.
        hnf; intros.
        cset_tac'. rewrite H2, H8. rewrite H4; eauto.
        cset_tac.
      * eapply agree_on_incl; eauto. rewrite H1. clear. cset_tac.
Qed.

(*
Lemma ctx_constr t r (L:list F.block) (E:onv val) L'
  : exists C LC, forall s, star2 step (L, fun _ => None, fill C s) nil ((LC++L)%list, fun _ => None, s)
                    /\ labenv_sim t (sim r) SR (block_Z ⊝ LC) LC L'.
Proof.
  intros. general induction L'.
  + eexists ctxHole, nil; simpl.
    split; eauto using star2_refl.
  + destruct a.
    edestruct (ctx_constr_E block_E (freeVars block_s) ∅) as [CE].
    edestruct (IHL' t r L E) as [CR [LC' ]].
    specialize (H (fun _ => None)). destruct H as [CEE ?]. hnf; intros; eauto.
    specialize (H0 ). destruct H0 as [CEE2 ?].
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
 *)

(*



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
