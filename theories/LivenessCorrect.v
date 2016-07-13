Require Import AllInRel List Map Env Exp MoreExp Rename SetOperations.
Require Import IL Annotation AutoIndTac Liveness InRel4.
Require Import Sim SimTactics.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

(** ** For functional programs, only free variables are significant *)

Inductive approxF :  F.block -> F.block -> Prop :=
 | approxFI E E' Z s n
    : agree_on eq (IL.freeVars s \ of_list Z) E E'
    ->  approxF (F.blockI E Z s n) (F.blockI E' Z s n).

Unset Printing Records.

Lemma mkBlocks_approxF s0 E E' s i
: agree_on eq (list_union
                 (List.map
                    (fun f : params * stmt =>
                       IL.freeVars (snd f) \ of_list (fst f)) s) ∪ IL.freeVars s0) E E'
  -> PIR2 approxF (mapi_impl (F.mkBlock E) i s) (mapi_impl (F.mkBlock E') i s).
Proof.
  intros.
  general induction s; eauto using PIR2. simpl.
  - econstructor. econstructor.
    eapply agree_on_incl; eauto.
    rewrite <- get_list_union_map; eauto using get.
    eapply IHs.
    eapply agree_on_incl; eauto. simpl.
    norm_lunion. clear_all; cset_tac.
Qed.


Inductive freeVarSimF : F.state -> F.state -> Prop :=
  freeVarSimFI (E E':onv val) L L' s
  (LA: PIR2 approxF L L')
  (AG:agree_on eq (IL.freeVars s) E E')
  : freeVarSimF (L, E, s) (L', E', s).

Lemma freeVarSimF_sim σ1 σ2
  : freeVarSimF σ1 σ2 -> sim Bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  destruct H; destruct s; simpl; simpl in *.
  - case_eq (exp_eval E e); intros.
    + exploit exp_eval_agree; eauto. eauto using agree_on_incl with cset.
      one_step.
      eapply freeVarSimF_sim. econstructor; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl with cset.
    + exploit exp_eval_agree; eauto using agree_on_incl with cset.
      no_step.
  - case_eq (exp_eval E e); intros.
    exploit exp_eval_agree; eauto using agree_on_incl.
    case_eq (val2bool v); intros.
    + one_step; eauto using agree_on_incl, freeVarSimF.
    + one_step; eauto using agree_on_incl, freeVarSimF.
    + exploit exp_eval_agree; eauto using agree_on_incl.
      no_step.
  - destruct (get_dec L (counted l)) as [[[Eb Zb sb]]|].
    PIR2_inv.
    decide (length Zb = length Y).
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_agree; eauto.
      one_step.
      simpl. eapply freeVarSimF_sim. econstructor; eauto.
      eapply PIR2_drop; eauto.
      eapply update_with_list_agree; eauto with len.
    + exploit omap_exp_eval_agree; eauto.
      no_step; get_functional; subst.
    + no_step; get_functional; subst; simpl in *; congruence.
    + no_step; eauto.
      edestruct PIR2_nth_2; eauto; dcr; eauto.
  - no_step. simpl. erewrite exp_eval_agree; eauto. symmetry; eauto.
  - case_eq (omap (exp_eval E) Y); intros.
    exploit omap_exp_eval_agree; eauto using agree_on_incl.
    extern_step.
    + exploit omap_exp_eval_agree; eauto using agree_on_incl.
    + exploit omap_exp_eval_agree.
      * symmetry. eauto using agree_on_incl.
      * eauto.
      * eapply freeVarSimF_sim. econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl with cset.
    + exploit omap_exp_eval_agree; eauto. symmetry; eauto using agree_on_incl with cset.
    + exploit omap_exp_eval_agree.
      * symmetry. eauto using agree_on_incl.
      * eauto.
      * eapply freeVarSimF_sim. econstructor; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl with cset.
    + no_step.
      symmetry in AG.
      exploit omap_exp_eval_agree; eauto using agree_on_incl.
      congruence.
  - one_step.
    eapply freeVarSimF_sim; econstructor; eauto using agree_on_incl.
    eapply PIR2_app; eauto. eapply mkBlocks_approxF; eauto.
Qed.

(** ** Live variables contain all variables significant to an IL/I program *)

Inductive approxI
  : list params -> list params -> list params -> list (set var) -> list I.block -> list I.block ->
    params -> params -> params -> set var -> I.block -> I.block -> Prop :=
  approxII ZL Lv Z s lv n L L'
  : live_sound Imperative ZL Lv s lv
    ->  approxI ZL ZL ZL Lv L L' Z Z Z (getAnn lv) (I.blockI Z s n) (I.blockI Z s n).

Lemma liveSimI_sim ZL Lv (E E':onv val) L s lv
  (LS:live_sound Imperative ZL Lv s lv)
  (LA:inRel approxI ZL ZL ZL Lv L L)
  (AG:agree_on eq (getAnn lv) E E')
  : sim Bisim (L, E, s) (L, E', s).
Proof.
  revert_all. cofix; intros.
  inv LS; simpl; simpl in *.
  - case_eq (exp_eval E e); intros.
    + one_step; eauto using exp_eval_live_agree.
      eapply liveSimI_sim; eauto.
      eapply agree_on_update_same; eauto using agree_on_incl.
    + no_step; eauto.
  - case_eq (exp_eval E e); intros.
    case_eq (val2bool v); intros.
    one_step; eauto using exp_eval_live_agree.
    eapply liveSimI_sim; eauto using agree_on_incl.
    one_step; eauto using exp_eval_live_agree.
    eapply liveSimI_sim; eauto using agree_on_incl.
    no_step; eauto.
  - inRel_invs. inv H8; simpl in *.
    case_eq (omap (exp_eval E) Y); intros.
    + exploit omap_exp_eval_live_agree; try eassumption.
      one_step; simpl; try congruence.
      eapply liveSimI_sim; eauto.
      eapply update_with_list_agree; eauto using agree_on_incl with len.
    + exploit omap_exp_eval_live_agree; try eassumption.
      no_step.
  - no_step. simpl. eapply exp_eval_live; eauto.
  - case_eq (omap (exp_eval E) Y); intros;
    exploit omap_exp_eval_live_agree; try eassumption.
    + extern_step.
      * exploit omap_exp_eval_live_agree; eauto.
      * eapply liveSimI_sim; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
      * symmetry in AG. exploit omap_exp_eval_live_agree; eauto.
      * eapply liveSimI_sim; eauto.
        eapply agree_on_update_same; eauto using agree_on_incl.
    + no_step.
  - one_step.
    eapply liveSimI_sim; eauto using agree_on_incl.
    + econstructor; eauto using agree_on_incl.
      eapply mutual_approx; eauto using mkBlock_I_i, mkBlock_F_i with len.
      intros; inv_get. econstructor; eauto.
Qed.
