Require Import RepairSpill RegLive ExpVarsBounded.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL.
Require Import Take TakeSet PickLK SetUtil.

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
    set (L' := pick_load k R M Sp L (Exp.freeVars e)) in *.
    set (K' := pick_kill k R L' (Exp.freeVars e) Rlv) in *.
    set (Kx' := pick_killx k x (R \ K' ∪ L') Rlv) in *.
    set (Sp':= (getAnn al ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))) in *.
    assert (Sp ∩ R ⊆ Sp') as Spincl.
    { subst Sp'. clear; cset_tac. }
    econstructor; eauto; cbn in *.
    + subst Sp'. subst K'. rewrite pick_kill_incl. setoid_rewrite meet_in_left at 2.
      subst Kx'. rewrite pick_killx_incl.
      setoid_rewrite minus_incl at 2 3. subst L'. rewrite pick_load_incl.
      apply Exp.freeVars_live in H. rewrite H. rewrite lv_RM. clear; cset_tac.
    + subst L'. rewrite pick_load_incl. rewrite <-Spincl.
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
    + subst K'. rewrite pick_kill_incl.
      setoid_rewrite union_comm at 2. rewrite <-minus_union, minus_minus.
      rewrite incl_minus_union; [|clear;cset_tac].
      subst L'. rewrite <-incl_pick_load. clear; cset_tac.
    + assert (K' ⊆ R) as KReq.
      { subst K'. rewrite pick_kill_incl. clear; cset_tac. }
      assert (disj (R \ K') L') as RKLdisj.
      { subst K'. rewrite <-incl_pick_kill. clear. cset_tac. }
      rewrite union_cardinal; [|clear - RKLdisj;intros;intro N;cset_tac].
      rewrite cardinal_difference'; eauto.
      rewrite <-Nat.add_sub_swap; [|rewrite subset_cardinal; eauto].
      apply Nat.le_sub_le_add_r.
      subst K'. rewrite <-pick_kill_card; [omega|].
      subst L'. rewrite pick_load_card; eauto.
      assert (forall n1 n2 n3 : nat, n1 <= n3 -> n3 <= n2 -> n1 + (n2 - n3) <= n2) as nateq.
      { clear. intros. omega. }
      apply nateq; eauto.
      * apply subset_cardinal;eauto. rewrite <-incl_pick_load; eauto.
        admit. (*rewrite <-incl_pick_load. clear; cset_tac.*)
      * rewrite subset_cardinal; eauto. clear; cset_tac.
    + 
  - 
  
                