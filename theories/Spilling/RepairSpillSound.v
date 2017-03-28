Require Import RepairSpill RegLive.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL.
Require Import Take TakeSet.

Set Implicit Arguments.

(** * Soundness of repair_spill *)


Lemma repair_spill_sound k ZL Λ R M s rlv lv sl (*ra*)
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> annotation s sl
    -> annotation s rlv
(*    -> renamedApart s ra
    -> R ∪ M [=] fst (getAnn ra)*)
    -> getAnn lv ⊆ R ∪ M
    -> spill_sound k ZL Λ (R,M) s (repair_spill k ZL Λ R M s rlv lv sl)
.
Proof.
  intros lvSnd anno_sl anno_rlv lv_RM (*rena RM_ra*).
  general induction lvSnd; invc anno_sl; invc anno_rlv; (*invc rena;*) cbn.
  - destruct a,p. rename s0 into Sp. rename s1 into L. rename a0 into Rlv.
    set (L' := set_take_prefer k (L ∩ (Sp ∩ R ∪ M)) (Exp.freeVars e \ R)) in *.
    set (K' := set_take_least_avoid (cardinal (R ∪ L') - k) (R \ (Exp.freeVars e ∪ L')) Rlv) in *.
    set (Kx' := set_take_least_avoid (cardinal {x; R \ K' ∪ L'} - k) R Rlv) in *.
    set (Sp':= (getAnn al ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))) in *.
    assert (Sp ∩ R ⊆ Sp') as Spincl.
    { subst Sp'. clear; cset_tac. }
    econstructor; eauto.
    + subst Sp'. apply incl_minus_incl_union in H0. rewrite H0.
      subst Kx'. rewrite set_take_least_avoid_incl. subst K'. rewrite set_take_least_avoid_incl.
      clear; cset_tac.
    + subst L'. rewrite set_take_prefer_incl. rewrite Spincl.
      cbn in *. apply Exp.freeVars_live in H. rewrite H. clear - lv_RM. cset_tac.
    + eapply IHlvSnd; eauto. apply incl_minus_incl_union in H0.
      setoid_rewrite <-inter_subset_equal with (s':=getAnn al) at 1; eauto.
      setoid_rewrite H0 at 1. subst Sp'.
      clear - lv_RM. cbn in *. rewrite lv_RM. rewrite union_meet_distr_r.
      apply union_incl_split; [cset_tac|].
      rewrite union_meet_distr_r. apply union_incl_split; [|cset_tac].
      setoid_rewrite set_decomp with (t:=(K' ∪ Kx')) at 1.
      apply union_incl_split; [|cset_tac]. setoid_rewrite <-incl_right at 2.
      setoid_rewrite set_decomp with (t:=M) at 1; cset_tac.
    + eapply Exp.freeVars_live in H. rewrite H. subst L'. 
      cset_tac.
      subst Kx'. rewrite set_take_least_avoid_incl. subst K'. rewrite set_take_least_avoid_incl.
      cbn in *. subst Sp'. setoid_rewrite set_take_least_avoid_incl at 1.
      subst L'. setoid_rewrite set_take_prefer_incl at 1.
  
  
                