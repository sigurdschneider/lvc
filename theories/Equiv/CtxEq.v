Require Import Util MapDefined LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp Envs IL Sawtooth SimF BisimEq MoreCtxEq ILStateType.

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

Definition lessDef (G:set var) (E E':onv val)
  := forall x, x ∈ G -> E' x = None -> E x = None.


Fixpoint fix_vars (E:onv val) (xl: list var) : stmtCtx :=
  match xl with
  | x::xl =>
    match E x with
    | Some v => ctxExp x (Operation (Con v)) (fix_vars E xl)
    | None => fix_vars E xl
    end
  | nil => ctxHole
  end.



Lemma fix_vars_correct G E' xl E (LD:lessDef (of_list xl) E E') (ND:NoDupA eq xl)
  : exists E'', (forall L s, star2 F.step (L, E, fill (fix_vars E' xl) s) nil (L, E'', s))
           /\ agree_on eq (of_list xl) E' E''
           /\ agree_on eq (G \ of_list xl) E E''.
Proof.
  general induction xl; simpl in * |- *; eauto 20 using star2_refl, agree_on_refl, agree_on_empty.
  - cases; simpl; eauto.
    + edestruct (IHxl {a; G}); dcr; swap 1 3.
      eexists x; split.
      * intros. eapply star2_silent; eauto. econstructor. reflexivity.
      * split.
        -- hnf; intros. cset_tac'. rewrite <- H3; lud; try cset_tac.
           inv ND. cset_tac.
        -- hnf; intros. cset_tac'.
           rewrite <- H3; lud; eauto. cset_tac.
      * eauto.
      * hnf; intros. lud; eauto. congruence.
        exploit LD; eauto. cset_tac.
    + edestruct (IHxl {a; G}); swap 1 3; dcr.
      eexists x; split; [|split]; eauto.
      * hnf; intros. cset_tac'.
        rewrite <- H3; eauto.
        exploit LD; eauto. cset_tac.
        congruence.
        inv ND; cset_tac.
      * eapply agree_on_incl; eauto.
        cset_tac.
      * eauto.
      * hnf; intros; eapply LD; cset_tac.
Qed.

Local Notation EMP := (fun _ : positive => ⎣⎦).

Lemma tooth_smaller L
  : tooth 0 L
    -> smaller L.
Proof.
  intros; hnf; intros.
  change f with (0 + f).
  revert H. generalize 0.
  intros.
  general induction H0; invt tooth; try omega.
  eapply IHget in H4. omega.
Qed.

Lemma freeVarSimF_sim r t s E E'
      (AG:agree_on eq (IL.freeVars s) E E')
  : forall (L L' : 〔F.block〕),
      labenv_sim t (sim r) SR (length (A:=positive) ⊝ F.block_Z ⊝ L') L L'
      -> ❬L❭ = ❬L'❭
      -> sim r t (L : F.labenv, E, s) (L', E', s).
Proof.
  revert r E E' AG.
  sind s; destruct s; simpl in *; intros.
  - destruct e; simpl in *.
    + eapply (sim_let_op il_statetype_F); intros.
      * erewrite op_eval_agree; eauto.
        symmetry.
        eapply agree_on_incl; eauto.
      * left. eapply IH; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
    + eapply (sim_let_call il_statetype_F); intros.
      * exploit omap_op_eval_agree; eauto using agree_on_incl.
        symmetry.
        eapply agree_on_incl; eauto.
      * left. eapply IH; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
  - eapply (sim_cond il_statetype_F); eauto.
    + erewrite op_eval_agree; eauto.
      symmetry.
      eapply agree_on_incl; eauto.
    + intros.
      left. eapply IH; eauto using agree_on_incl with cset.
    + intros.
      left. eapply IH; eauto using agree_on_incl with cset.
  - destruct (get_dec L' l) as [[? ?]|?].
    + eapply labenv_sim_app; eauto using map_get_1.
      intros; simpl in *; dcr; split; intros.
      exploit omap_op_eval_agree; eauto using agree_on_incl.
      eexists; repeat split; eauto. congruence. congruence.
      destruct t; simpl. split; eauto; intros.
      exploit omap_op_eval_agree; eauto using agree_on_incl. congruence.
      eauto.
    + pno_step.
  - pno_step. simpl.
    erewrite op_eval_agree; symmetry; eauto using agree_on_incl with cset.
  - eapply sim_fun_ptw with (AL':=length (A:=positive) ⊝ F.block_Z ⊝ mapi (F.mkBlock E') F);
      try eapply H; eauto with len.
    + intros.
      left. eapply IH; eauto using agree_on_incl with cset.
      rewrite !map_app. eauto. eauto with len.
    + intros. hnf; intros. simpl in *. subst. inv_get; dcr; subst.
      eapply IH; eauto.
      eapply update_with_list_agree; eauto with len.
      eapply agree_on_incl; eauto.
      eapply incl_union_left.
      eapply incl_list_union; eauto using map_get_1.
      rewrite !map_app. eauto. eauto with len.
    + hnf; intros; simpl in *. subst. inv_get; eauto.
Qed.

Arguments of_list : simpl never.
Arguments to_list : simpl never.

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
      exists ((fun b => (F.block_Z b,
                 fill (fix_vars (F.block_E b)
                                (to_list (freeVars (F.block_s b) \ of_list (F.block_Z b))))
                      (F.block_s b))) ⊝ L).
      rewrite !map_app.
      eapply labenv_sim_extension_ptw'; eauto with len.
      - hnf; intros. simpl in *.
        hnf; intros. simpl in *. subst.
        dcr; subst; inv_get. simpl in *.
        edestruct fix_vars_correct; swap 1 3; dcr.
        eapply sim_expansion_closed; [| eapply H2 | eapply star2_refl].
        rewrite get_app_lt in H4. inv_get. simpl in *.
        orewrite (i - i = 0); simpl.
        exploit tooth_index; eauto. simpl in *.
        orewrite (i - i' = 0); simpl.
        rewrite <- !map_app in *.
        eapply freeVarSimF_sim; eauto.
        instantiate (1:=of_list Z') in H7.
        assert (freeVars s' ⊆ of_list Z'  ∪ (freeVars s' \ of_list Z')) by (clear; cset_tac).
        eapply agree_on_incl; eauto.
        eapply agree_on_union.
        etransitivity. symmetry. eapply agree_on_incl; eauto.
        rewrite of_list_3. clear; cset_tac.
        eapply update_with_list_agree; eauto with len.
        eapply agree_on_empty. clear; cset_tac.
        eapply agree_on_update_list_dead.
        rewrite of_list_3 in H6. symmetry. eauto.
        clear. cset_tac.
        len_simpl. destruct H0. len_simpl. eauto.
        eauto with len. eapply nodup_to_list_eq.
        hnf. intros. rewrite of_list_3 in H1.
        rewrite lookup_set_update_not_in_Z; eauto.
        cset_tac.
      - rewrite <- !map_app.
        hnf; intros; simpl in *.
        destruct f, f'; simpl in *; subst.
        inv_get. simpl in *. eauto.
      - rewrite <- app_nil_r.
        econstructor 2; eauto using @sawtooth.
        unfold mapi. revert H. generalize 0.
        intros.
        general induction H; simpl; eauto using @tooth.
      - rewrite <- app_nil_r.
        econstructor 2; eauto using @sawtooth.
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
Qed.

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


Lemma ctxeq_simeq2 t s s'
  : ctxeq2 t s s' <-> bisimeq bot3 t s s'.
Proof.
  split; intros.
  - hnf; intros L1 L2 E SIM Len.
    edestruct (@fix_vars_correct ∅ E (to_list (freeVars s ∪ freeVars s')) EMP) as [E'' CCH].
    hnf; intros; eauto. eapply nodup_to_list_eq.
    destruct CCH as [RED [AGR1 AGR2]].
    rewrite of_list_3 in AGR1.
    rewrite of_list_3 in AGR2.
    edestruct (ctx_constr Bisim) as [C1 [L1' [LC1 ?]]].
    instantiate (1:=L2). eapply SIM.
    set (CE:=(fix_vars E (to_list (freeVars s ∪ freeVars s')))).
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
        instantiate (1:=(L1', E'', s')).
        eapply freeVarSimF_sim.
        symmetry. eauto using agree_on_incl with cset.
        eapply labenv_sim_refl. eapply LC1. reflexivity.
      }
      eapply sim_trans with (S2:=F.state); swap 1 2; eauto.
      eapply sim_trans with (S2:=F.state). {
        instantiate (1:=(L1, E'', s)).
        eapply freeVarSimF_sim.
        eauto using agree_on_incl with cset.
        eapply labenv_sim_refl. eapply SIM. reflexivity.
      }
      eapply sim_trans with (S2:=F.state). {
        eapply (bisimeq_refl _ _ SIM).
      }
      assert (sim bot3 Bisim (L2, E'', s) (L1', E'', s)). {
        eapply @bisim_sym.
        eapply (bisimeq_refl). eauto.
      }
      destruct t; eauto.
      eapply bisim_sim; eauto.
  - hnf; intros.
    eapply simeq_contextual with (ctx:=C) in H.
    exploit (H nil nil); simpl; eauto using labenv_sim_nil.
Qed.
