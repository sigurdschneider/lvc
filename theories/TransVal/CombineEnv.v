Require Import List Arith.
Require Import IL Annotation AutoIndTac Exp MoreExp RenamedApart Fresh Util.
Require Import SetOperations Sim Var.
Require Import SMT NoFun.
Require Import Guards ILFtoSMT GuardProps ComputeProps.

(** Definitons **)
Definition combineEnv D (E1:onv val) E2 :=
  fun x => if [x ∈ D] then E1 x else E2 x.

(** Lemmata **)

Lemma combineEnv_agree D E E'
  : agree_on eq D (combineEnv D E E') E.
Proof.
  hnf; intros. unfold combineEnv. cases; eauto; isabsurd.
Qed.

Lemma combineEnv_agree_meet D D' Es Et
  : agree_on eq (D' ∩ D) Es Et
    -> agree_on eq D' (combineEnv D Es Et) Et.
Proof.
 intros.
 - hnf. cset_tac. unfold combineEnv. cases; eauto.
   rewrite H; eauto. cset_tac; intuition.
Qed.

Lemma combineEnv_agree_minus D D' Es Et
  : agree_on eq (D' \ D) Es Et
    -> agree_on eq D' (combineEnv D Es Et) Es.
Proof.
 intros.
 - hnf. cset_tac. unfold combineEnv. cases; eauto.
   rewrite H; eauto. cset_tac; intuition.
Qed.

Lemma combineEnv_models F s D Es Et
  : freeVars s ⊆  D
    -> (models F (to_total Es) s  <-> models F (to_total (combineEnv D Es Et)) s).
Proof.
  intros. eapply models_agree. eapply (agree_on_incl (lv:=D)); eauto; symmetry.
  eapply agree_on_total.
  eapply combineEnv_agree.
Qed.

Lemma combineEnv_omap_exp_eval_left el D Es Et
  : list_union (List.map Exp.freeVars el) ⊆ D
    -> omap (exp_eval (combineEnv D Es Et)) el = omap (exp_eval Es) el.
Proof.
  intros.
  erewrite omap_exp_eval_agree; [reflexivity | | reflexivity].
  symmetry. eapply agree_on_incl; eauto using combineEnv_agree.
Qed.

Lemma combineEnv_omap_exp_eval_right el D Es Et
  : agree_on eq (list_union (List.map Exp.freeVars el) ∩ D) Es Et
    -> omap (exp_eval (combineEnv D Es Et)) el = omap (exp_eval Et) el.
Proof.
  intros.
  erewrite omap_exp_eval_agree; [reflexivity | | reflexivity].
  symmetry. eapply combineEnv_agree_meet; eauto.
Qed.

Lemma renamedApart_contained L E s t Es D
: Terminates (L, E, s) (L, Es, t)
  -> noFun s
  -> renamedApart s D
  -> IL.freeVars t ⊆ fst (getAnn D) ∪ snd (getAnn D).

Proof.
  intros term_s nf_s ssa_s.
  general induction term_s; invt noFun; invt renamedApart; try invt F.step; simpl; eauto with cset.
  - exploit IHterm_s as IH; try reflexivity; eauto.
    rewrite IH. pe_rewrite. rewrite H9. clear_all; cset_tac.
  - exploit IHterm_s as IH; try reflexivity; eauto.
    rewrite IH. pe_rewrite. rewrite <- H8. clear_all; cset_tac.
  - exploit IHterm_s as IH; try reflexivity; eauto.
    rewrite IH. pe_rewrite. rewrite <- H8. clear_all; cset_tac.
  - exfalso; eapply H0; eauto.
Qed.

Lemma agree_on_ssa_combine:
  forall D D' L E s t Es Et es et,
    renamedApart s D
    -> renamedApart t D'
    -> fst (getAnn D) [=] fst (getAnn D')
    -> disj (snd (getAnn D)) (snd (getAnn D'))
    -> noFun s
    -> noFun t
    -> Terminates (L, E, s) (L, Es, stmtReturn es)
    -> Terminates (L, E, t) (L, Et, stmtReturn et)
    -> (agree_on eq (Exp.freeVars et) Et (combineEnv (fst(getAnn D) ∪ snd(getAnn D)) Es Et)
        /\ agree_on eq (Exp.freeVars es) Es (combineEnv (fst(getAnn D) ∪ snd(getAnn D)) Es Et)).

Proof.
  intros D D' L E s t Es Et es et.
  intros ssa_s ssa_t agree_fv disj_dv nf_s nf_t sterm tterm.
  split.
  - edestruct (ssa_move_return D' L E t Et et nf_t ssa_t tterm)
      as [D'' [ ssaRet [fstSubset sndSubset]]].
    exploit term_ssa_eval_agree; try eapply sterm; eauto.
    exploit term_ssa_eval_agree; try eapply tterm; eauto.
    exploit (renamedApart_contained L E t (stmtReturn et) Et D') as fv_dv; eauto.
    simpl in *. symmetry.
    eapply agree_on_incl; [ eapply combineEnv_agree_meet | reflexivity ].
    rewrite fv_dv. rewrite <- agree_fv.
    rewrite <- agree_fv in H0. rewrite H in H0; clear H.
    hnf; intros; cset_tac.
  - edestruct (ssa_move_return D L E s Es es nf_s ssa_s sterm)
      as [D'' [ssaRet [fstSubset sndSubset]]]; eauto.
    inv ssaRet. symmetry.
    eapply agree_on_incl; [eapply combineEnv_agree_minus | reflexivity ].
    exploit (renamedApart_contained L E s (stmtReturn es) Es D) as fv_dv; eauto.
    simpl in *.
    rewrite fv_dv. hnf; intros; cset_tac.
Qed.