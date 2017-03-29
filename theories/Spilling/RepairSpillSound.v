Require Import RepairSpill RegLive ExpVarsBounded.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL.
Require Import Take TakeSet.

Set Implicit Arguments.

(** * Soundness of repair_spill *)


Lemma set_union_disjunctify (X:Type) `{OrderedType X} (s t : ⦃X⦄) :
  s ∪ t [=] (s \ t) ∪ (s ∩ t) ∪ (t \ s)
.
Proof.
  cset_tac.
Qed.

Lemma cardinal_union_split (X:Type) `{OrderedType X} (s t : ⦃X⦄) :
  cardinal (s ∪ t) = cardinal (s \ t) + cardinal (s ∩ t) + cardinal (t \ s)
.
Proof.
  rewrite <-union_cardinal; [|cset_tac]. setoid_rewrite union_comm at 2. rewrite <-set_decomp.
  rewrite <-union_cardinal; [|cset_tac]. apply Equal_cardinal. cset_tac.
Qed.


Lemma repair_spill_sound k ZL Λ R M s rlv lv sl (*ra*)
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> annotation s sl
    -> annotation s rlv
(*    -> renamedApart s ra
    -> R ∪ M [=] fst (getAnn ra)*)
    -> getAnn lv ⊆ R ∪ M
    -> exp_vars_bounded k s
    -> spill_sound k ZL Λ (R,M) s (repair_spill k ZL Λ R M s rlv lv sl)
.
Proof.
  intros lvSnd anno_sl anno_rlv lv_RM expB (*rena RM_ra*).
  general induction lvSnd; invc anno_sl; invc anno_rlv; invc expB; (*invc rena;*) cbn.
  - destruct a,p. rename s0 into Sp. rename s1 into L. rename a0 into Rlv.
    set (L' := set_take_prefer (k - cardinal (Exp.freeVars e ∩ R \ L))
                               (L ∩ (Sp ∩ R ∪ M)) (Exp.freeVars e \ R)) in *.
    set (K' := set_take_least_avoid ((cardinal R + cardinal L') - k)
                                    ((R \ Exp.freeVars e) ∪ (R ∩ L')) Rlv) in *.
    set (Kx' := set_take_least_avoid (cardinal {x; R \ K' ∪ L'} - k) (R \ K' ∪ L') Rlv) in *.
    set (Sp':= (getAnn al ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))) in *.
    assert (Sp ∩ R ⊆ Sp') as Spincl.
    { subst Sp'. clear; cset_tac. }
    econstructor; eauto.
    + subst Sp'. apply incl_minus_incl_union in H0. rewrite H0.
      subst Kx'. rewrite set_take_least_avoid_incl. subst K'.
      setoid_rewrite set_take_least_avoid_incl at 1.
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
    + subst L'. cbn in *. 
      subst K'. rewrite set_take_least_avoid_incl. rewrite <-set_take_prefer_card_incl.
      * rewrite <-minus_union. clear; cset_tac.
      * apply Nat.le_add_le_sub_l. rewrite <-union_cardinal; [|clear;cset_tac].
        rewrite <-set_decomp. eauto.
    + assert (K' ⊆ R) as KReq.
      { subst K'. rewrite set_take_least_avoid_incl. clear; cset_tac. }
      assert (disj (R \ K') L') as RKLdisj.
      { subst K' L'.
      setoid_rewrite set_decomp with (t:=R) at 5. rewrite <-union_assoc.
      rewrite union_cardinal; [|clear;cset_tac].
      setoid_rewrite cardinal_difference'.
      setoid_rewrite set_take_least_avoid_size at 2; eauto.  
      rewrite cardinal_union_split.
      assert (forall s t u : ⦃var⦄, s \ t ∩ u [=] (s ∩ u) \ t) as seteq by (clear;intros;cset_tac).
      rewrite seteq. setoid_rewrite cardinal_difference' at 2.

      
                                                                     
                                                                     
      subst K'. rewrite minus_union, minus_minus.
      rewrite meet_in_left. rewrite union_cardinal_inter. subst L'.
      apply <-Nat.le_sub_le_add_r. setoid_rewrite set_take_prefer_size at 1.
      assert (cardinal R <= k) as cheat by admit.
      rewrite cheat.
      enough ((k - cardinal (Exp.freeVars e ∩ R))
                             <= cardinal
                                 (R ∩ set_take_prefer (k - cardinal (Exp.freeVars e ∩ R))
                                    (L ∩ (Sp ∩ R ∪ M)) (Exp.freeVars e \ R))) by omega.
      rewrite Nat.le_sub_le_add_r.
      rewrite <-set_take_prefer_card_incl.
      * 
      setoid_rewrite set_take_prefer_incl at 2.
      cset_tac.
      subst Kx'. rewrite set_take_least_avoid_incl. subst K'. rewrite set_take_least_avoid_incl.
      cbn in *. subst Sp'. setoid_rewrite set_take_least_avoid_incl at 1.
      subst L'. setoid_rewrite set_take_prefer_incl at 1.
  
  
                