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


Fixpoint fix_vars (E:onv val) (xl: list var) : stmtCtx :=
  match xl with
  | x::xl =>
    match E x with
    | Some v => ctxExp x (Operation (Con v)) (fix_vars E xl)
    | None => fix_vars E xl
    end
  | nil => ctxHole
  end.

Lemma fix_vars_correct G L E E' s xl (LD:lessDef E E') (ND:NoDupA eq xl)
  : exists E'', star2 F.step (L, E, fill (fix_vars E' xl) s) nil (L, E'', s)
           /\ agree_on eq (of_list xl) E' E''
           /\ agree_on eq (G \ of_list xl) E E''.
Proof.
  general induction xl; simpl in * |- *; eauto 20 using star2_refl, agree_on_refl, agree_on_empty.
  - cases; simpl; eauto.
    + edestruct (IHxl {a; G}); dcr; swap 1 3.
      eexists x; split.
      * eapply star2_silent; eauto. econstructor. reflexivity.
      * split.
        -- hnf; intros. cset_tac'. rewrite <- H3; lud; try cset_tac.
           inv ND. cset_tac.
        -- hnf; intros. cset_tac'.
           rewrite <- H3; lud; eauto. cset_tac.
      * eauto.
      * hnf; intros. lud; eauto. congruence.
    + edestruct (IHxl {a; G}); swap 1 3; dcr.
      eexists x; split; [|split]; eauto.
      * hnf; intros. cset_tac'. exploit LD; eauto. rewrite <- H3; eauto. congruence.
        inv ND; cset_tac.
      * eapply agree_on_incl; eauto.
        cset_tac.
      * eauto.
      * eauto.
Qed.

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
  : exists C LC, labenv_sim t (sim bot3) SR (@length _ ⊝ block_Z ⊝ L') LC L'
            /\ forall L s, star2 step (L, fun _ => None, fill C s) nil ((LC++L)%list, fun _ => None, s).
Proof.
  intros. induction STL'.
  - eexists ctxHole, nil; simpl.
    split; eauto using star2_refl.
  - destruct IHSTL' as [IHCR [IHLC [IHH1 IHH2]]]; eauto.
    assert (CTXT:
              exists F,
                labenv_sim t (sim bot3) SR (length (A:=positive) ⊝ block_Z ⊝ (L ++ L'))
                           (mapi (F.mkBlock (fun _ => ⎣⎦)) F ++ IHLC) (L ++ L')).
    {
      clear IHCR IHH2. unfold mapi.
      revert H; generalize 0; intros.
      induction H.
      - eexists nil; simpl; eauto with len.
      - subst. destruct b; simpl in *.
        destruct IHtooth as [F IHRED].
        edestruct (ctx_constr_E block_E (freeVars block_s \ of_list block_Z) ∅) as [CE CCH].
        specialize (CCH (fun _ => None)). destruct CCH as [CCH1 [AGR1 [AGR2 CCH2]]].
        + hnf; intros; eauto.
        + eexists ((block_Z, fill CE block_s) :: F).
          destruct IHRED; dcr.
          hnf; intros. simpl.
          split. {
            len_simpl. omega.
          }
          split. {
            admit.
          }
          split. {
            admit.
          }
          split. {
            hnf; intros.
            hnf in H1. destruct f, f'. simpl in *; subst.
            destruct 0; inv_get.
            admit.
            inv_get. destruct x1.
            eapply (H3 (LabI n)); eauto. simpl in *.
            admit.
          }
          admit.
    }
    destruct CTXT as [F TSIM].
    eexists (fillC IHCR (ctxLetT F ctxHole)).
    eexists (mapi (F.mkBlock (fun _ : positive => ⎣⎦)) F ++ IHLC).
    split.
    + eauto.
    + intros.
      rewrite !fill_fillC.
      eapply star2_trans_silent; eauto. simpl.
      eapply star2_silent. single_step.
      rewrite app_assoc. eapply star2_refl.
Admitted.

Definition ctxeq1 t s s' := forall C, bisimeq bot3 t (fill C s) (fill C s').

Lemma ctxeq_simeq1 t s s'
  : ctxeq1 t s s' <-> bisimeq bot3 t s s'.
Proof.
  split; intros; eauto.
  - eapply (H ctxHole).
  - hnf; intros.
    eapply simeq_contextual. eauto.
Qed.

Definition ctxeq2 t s s' := forall C, sim bot3 t (nil:F.labenv, fun _ : positive => ⎣⎦, fill C s) (nil:F.labenv, fun _ : positive => ⎣⎦, fill C s').

Local Notation EMP := (fun _ : positive => ⎣⎦).

Require Import LivenessCorrect.

Lemma ctxeq_simeq2 t s s'
  : ctxeq2 t s s' <-> bisimeq bot3 t s s'.
Proof.
  split; intros.
  - hnf; intros L1 L2 E SIM Len.
    edestruct (ctx_constr_E E (freeVars s ∪ freeVars s') ∅) as [CE CCH].
    specialize (CCH EMP (ltac:(hnf; intros; eauto))).
    destruct CCH as [EC [AGR1 [AGR2 RED]]].
    edestruct (ctx_constr Bisim) as [C1 [L1' [LC1 ?]]].
    instantiate (1:=L2). admit.
    exploit (H (fillC C1 CE)).
    rewrite !fill_fillC in *.
    eapply sim_reduction_closed in H1; swap 1 3; eauto.
    eapply sim_reduction_closed in H1; swap 1 3; eauto.
    rewrite app_nil_r in *.
    assert (LC2:labenv_sim t (sim bot3) SR (length (A:=positive) ⊝ block_Z ⊝ L2) L1' L2). {
      destruct t; eauto.
      destruct LC1; dcr.
      repeat (split; eauto). hnf; intros.
      eapply bisim_sim; eauto.
    }
    eapply sim_trans with (S2:=F.state); swap 1 2.
    + eapply (bisimeq_refl _ _ LC2).
    + eapply sim_trans with (S2:=F.state); swap 1 2. {
        instantiate (1:=(L1', EC, s')).
        eapply SimLockStep.sim_bisim.
        eapply freeVarSimF_sim.
        econstructor. eapply PIR2_get; intros; inv_get; try reflexivity.
        destruct x; econstructor; reflexivity.
        symmetry. eapply agree_on_incl; eauto.
      }
      eapply sim_trans with (S2:=F.state); swap 1 2; eauto.
      eapply sim_trans with (S2:=F.state). {
        instantiate (1:=(L1, EC, s)).
        eapply SimLockStep.sim_bisim.
        eapply freeVarSimF_sim.
        econstructor. eapply PIR2_get; intros; inv_get; try reflexivity.
        destruct x; econstructor; reflexivity.
        eapply agree_on_incl; eauto.
      }
      eapply sim_trans with (S2:=F.state). {
        eapply (bisimeq_refl _ _ SIM).
      }
      assert (sim bot3 Bisim (L2, EC, s) (L1', EC, s)). {
        eapply @bisim_sym.
        eapply (bisimeq_refl). eauto.
      }
      destruct t; eauto.
      eapply bisim_sim; eauto.
  - hnf; intros.
    eapply simeq_contextual with (ctx:=C) in H.
    exploit (H nil nil); simpl; eauto using labenv_sim_nil.
Qed.
