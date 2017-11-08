Require Import Util MapDefined LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp Envs IL Sawtooth SimF BisimEq MoreCtxEq.

Set Implicit Arguments.
Unset Printing Records.

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

Lemma simeq_contextual p s s' ctx
: bisimeq bot3 p s s'
  -> bisimeq bot3 p (fill ctx s) (fill ctx s').
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
          inv_get.
          eapply bisimeq_refl; eauto 20 with len.
          rewrite !map_app. eauto.
        - simpl in *. dcr; subst. subst. invc H9.
          inv_get. simpl in *.
          eapply bisimeq_bot; eauto with len.
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
Qed.

Lemma fun_congrunence p F F' t t' (LEN:length F = length F')
  : bisimeq bot3 p t t'
    -> (forall n Z s Z' s', get F n (Z, s) -> get F' n (Z', s') -> Z = Z' /\ bisimeq bot3 p s s')
    -> bisimeq bot3 p (stmtFun F t) (stmtFun F' t').
Proof.
  intros SIMt SIMF.
  hnf; intros ? ? ? LAB Len.
  eapply sim_fun_ptw; eauto using labenv_sim_refl.
  - intros. left.
    eapply bisimeq_bot; eauto with len.
    rewrite !map_app in *; eauto.
  - intros; hnf; intros.
    hnf in H0; dcr; subst.
    hnf in H4; dcr; subst. inv_get.
    simpl in *. edestruct SIMF; eauto; subst.
    eapply bisimeq_bot; eauto with len.
    rewrite !map_app in *; eauto.
  -  hnf; intros. simpl in *; subst. inv_get.
     edestruct SIMF; dcr; eauto; subst.
     eauto.
  - eauto with len.
Qed.

Lemma fill_fillC C C' s
  :  fill (fillC C C') s = fill C (fill C' s).
Proof.
  general induction C; simpl; f_equal; eauto.
  rewrite IHC; eauto.
Qed.

Definition lessDef (E E':onv val)
  := forall x, E' x = None -> E x = None.

Lemma ctx_constr_E (E':onv val) G G'
  : exists C, forall E, lessDef E E' ->
              exists EC, agree_on eq G E' EC
                    /\ agree_on eq (G'\G) EC E
                    /\ forall (L:list F.block) s,
                        star2 step (L, E, fill C s) nil (L, EC, s).
Proof.
  revert G'.
  pattern G. eapply set_induction.
  - intros. eexists ctxHole. intros. eexists E. split.
    + eapply empty_is_empty_1 in H. rewrite H. eapply agree_on_empty; eauto.
    + split.
      * hnf; intros; cset_tac; intuition.
      * intros. eapply star2_refl.
  - intros. eapply Add_Equal in H1.
    case_eq (E' x); intros.
    + edestruct H as [C' ?]; eauto using defined_on_incl with cset.
      eexists (fillC C' (ctxExp x (Operation (Con v)) ctxHole)).
      intros. specialize (H3 E). destruct H3 as [EC' [AGR1 [AGR2 ECH]]]; eauto.
      eexists (EC'[x<-E' x]).
      split;[|split].
      * hnf; intros. lud; eauto.
        -- rewrite e. reflexivity.
        -- eapply AGR1; eauto. rewrite H1 in *. cset_tac.
      * eapply agree_on_update_dead. rewrite H1. cset_tac.
        eapply agree_on_incl; eauto.
        rewrite H1. cset_tac.
      * intros. rewrite fill_fillC.
        simpl.
        eapply (@star2_trans _ _ _ _ _ nil nil).
        -- eapply ECH; eauto.
        -- rewrite H2. eapply star2_silent.
           single_step; simpl; eauto.
           eapply star2_refl.
    + edestruct (H ({x; G'})) as [C' ?]; eauto using defined_on_incl with cset.
      eexists C'.
      intros. specialize (H3 E H4).
      destruct H3 as [EC' [AGR1 [AGR2 ECH]]]; eauto.
      eexists EC'.
      split;[|split].
      * rewrite H1. clear - AGR1 AGR2 H0 H2 H4.
        hnf; intros.
        cset_tac'. rewrite AGR2.
        exploit H4; eauto. congruence.
        cset_tac.
      * eapply agree_on_incl; eauto. rewrite H1. clear. cset_tac.
      * intros. eauto.
Qed.


Lemma ctx_constr t L' (STL':sawtooth L')
  : exists C LC, labenv_sim t (sim bot3) SR (@length _ ⊝ block_Z ⊝ LC) LC L'
            /\ forall L s, star2 step (L, fun _ => None, fill C s) nil ((LC++L)%list, fun _ => None, s).
Proof.
  intros. induction STL'.
  - eexists ctxHole, nil; simpl.
    split; eauto using star2_refl.
  - destruct IHSTL' as [IHCR [IHLC [IHH1 IHH2]]]; eauto.
    assert (CTXT:
        exists (C : stmtCtx) (LC : 〔F.block〕),
          labenv_sim t (sim bot3) SR (length (A:=positive) ⊝ block_Z ⊝ (LC++IHLC))
                     (LC++IHLC) (L++L') /\
          (forall L s,
              star2 step (L, fun _ : positive => ⎣⎦, fill C s) nil (LC ++ L, fun _ : positive => ⎣⎦, s))).
    {
      admit.
    }
    destruct CTXT as [TCT [TLC [TSIM TRED]]].
    eexists (fillC IHCR (fillC TCT ctxHole)).
    eexists (TLC ++ IHLC).
    split.
    + rewrite !map_app.
      eapply labenv_sim_extension_ptw.
    + intros.
      rewrite !fill_fillC.
      eapply star2_trans_silent; eauto.
      eapply star2_trans_silent; eauto.
      rewrite app_assoc. eapply star2_refl.

    revert H. generalize 0. intros.
    induction H.
    + eapply IHSTL'; eauto.
    + simpl. subst. destruct b; simpl in *.
      edestruct (ctx_constr_E block_E (freeVars block_s) ∅) as [CE CCH].
      destruct IHSTL' as [CR [LC' IHH]]; eauto.
      specialize (CCH (fun _ => None)). destruct CCH as [CCH1 CCH2].
      * hnf; intros; eauto.
      * destruct IHtooth as [IHTC [IHTLC IHT]].
        eexists (fillC CR (fillC CE (ctxLetT ((block_Z, block_s)::nil) ctxHole))).
      eexists (F.blockI CCH1 block_Z block_s block_n ::LC').
      intros s.
      split.
      * rewrite !fill_fillC.
        eapply star2_trans_silent. eapply IHH.
        eapply star2_trans_silent. eapply CCH2.
        simpl.
        eapply star2_silent. econstructor.
        simpl. unfold F.mkBlock. simpl.
      *


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
