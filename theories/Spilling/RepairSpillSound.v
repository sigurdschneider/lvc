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
    set (K' := pick_kill k R L' (Exp.freeVars e) (getAnn sa0)) in *.
    set (Kx' := pick_killx k (R \ K' ∪ L') (getAnn sa0)) in *.
    set (Sp':= (getAnn al ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))) in *.
    assert (Sp ∩ R ⊆ Sp') as Spincl.
    { subst Sp'. clear; cset_tac. }
    assert (K' ⊆ R) as KReq.
    { subst K'. rewrite pick_kill_incl. clear; cset_tac. }
    assert (disj (R \ K') L') as RKLdisj.
    { subst K'. rewrite <-incl_pick_kill. clear. cset_tac. }
    assert (cardinal (R \ K' ∪ L') <= k) as card_RKL.
    {
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
        clear;cset_tac.
      * rewrite subset_cardinal; eauto. clear; cset_tac.
    }
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
    + decide (x ∈ (R \ K' ∪ L') \ Kx').
      * rewrite add_cardinal_1; eauto. rewrite cardinal_difference'; [| apply pick_killx_incl].
        apply Nat.le_sub_le_add_r. rewrite card_RKL. omega.
      * rewrite add_cardinal_2; eauto. rewrite cardinal_difference'; [| apply pick_killx_incl].
        rewrite minus_Sn_m. Focus 2. apply subset_cardinal. subst Kx'. apply pick_killx_incl.
        apply Nat.le_sub_le_add_r. subst Kx'. rewrite <-pick_killx_card.
        -- omega.
        -- setoid_rewrite union_comm at 2. rewrite <-set_decomp. omega.
  - destruct a. destruct p as (Sp, L). cbn in *. rename sa0 into rlv1. rename ta0 into rlv2.
    set (L' := pick_load k R M Sp L (Op.freeVars e)) in *.
    set (K' := pick_kill k R L' (Op.freeVars e) (getAnn rlv1 ∪ getAnn rlv2)) in *.
    set (Sp':= ((getAnn al1 ∪ getAnn al2) ∩ K' \ M) ∪ (Sp ∩ R)) in *.
    assert (Sp ∩ R ⊆ Sp') as Spincl.
    { subst Sp'. clear; cset_tac. }
    assert (K' ⊆ R) as KReq.
    { subst K'. rewrite pick_kill_incl. clear; cset_tac. }
    assert (disj (R \ K') L') as RKLdisj.
    { subst K'. rewrite <-incl_pick_kill. clear. cset_tac. }
    econstructor; eauto; cbn in *.
    + subst Sp'. subst K'. rewrite pick_kill_incl. setoid_rewrite meet_in_left at 2.
      setoid_rewrite minus_incl at 2 3.
      rewrite H0, H1. rewrite lv_RM. clear; cset_tac.
    + subst L'. rewrite pick_load_incl. rewrite <-Spincl.
      cbn in *. apply Op.freeVars_live in H. rewrite H. clear - lv_RM. cset_tac.
    + instantiate (1:=K'). subst K'. rewrite pick_kill_incl.
      setoid_rewrite union_comm at 2. rewrite <-minus_union, minus_minus.
      rewrite incl_minus_union; [|clear;cset_tac].
      subst L'. rewrite <-incl_pick_load. clear; cset_tac.
    + rewrite union_cardinal; [|clear - RKLdisj;intros;intro N;cset_tac].
      rewrite cardinal_difference'; eauto.
      rewrite <-Nat.add_sub_swap; [|rewrite subset_cardinal; eauto].
      apply Nat.le_sub_le_add_r.
      subst K'. rewrite <-pick_kill_card; [omega|].
      subst L'. rewrite pick_load_card; eauto.
      assert (forall n1 n2 n3 : nat, n1 <= n3 -> n3 <= n2 -> n1 + (n2 - n3) <= n2) as nateq.
      { clear. intros. omega. }
      apply nateq; eauto.
      * apply subset_cardinal;eauto. rewrite <-incl_pick_load; eauto.
        clear;cset_tac.
      * rewrite subset_cardinal; eauto. clear; cset_tac.
    + eapply IHlvSnd1; eauto.
      setoid_rewrite <-inter_subset_equal with (s':=getAnn al1) at 1; eauto.
      setoid_rewrite H0 at 1. subst Sp'.
      clear - lv_RM. cbn in *. rewrite lv_RM. rewrite union_meet_distr_r.
      apply union_incl_split; [cset_tac|].
      clear; cset_tac.
    + eapply IHlvSnd2; eauto.
      setoid_rewrite <-inter_subset_equal with (s':=getAnn al2) at 1; eauto.
      setoid_rewrite H1 at 1. subst Sp'.
      clear - lv_RM. cbn in *. rewrite lv_RM. rewrite union_meet_distr_r.
      apply union_incl_split; [cset_tac|].
      clear; cset_tac.
  - repeat let_pair_case_eq; subst. inv_get. simpl in *.
    eapply Op.freeVars_live_list in H3.
    destruct x as [Rf Mf]. unfold merge in H1; simpl in *.
    destruct (get_dec (snd a) 0) as [[[R' M'] ?]|].
    + repeat erewrite get_nth; eauto using get; simpl.
      econstructor; eauto.
      * rewrite pick_kill_incl.
        rewrite H3 at 1. rewrite lv_RM in *.
        revert H1. clear_all. cset_tac.
      * rewrite pick_load_incl at 1.
        rewrite lv_RM in *. revert H1.
        clear_all; cset_tac.
      * admit.
      * admit.
      * admit.
      * admit.
      * rewrite lv_RM in *.
        rewrite pick_kill_incl at 1.
        (*rewrite H3 at 1.*)
        eapply union_incl_split.
        -- admit.
        -- rewrite <- incl_pick_kill.
           rewrite <- incl_pick_load.
           revert H1.
           clear_all.
           admit.
    + repeat rewrite (not_get_nth_default _ f); eauto. simpl.
      repeat erewrite get_nth; eauto using get; simpl.
      econstructor; eauto.
      * rewrite pick_kill_incl.
        rewrite H3 at 1. rewrite lv_RM in *.
        revert H1. clear_all. cset_tac.
      * rewrite pick_load_incl at 1.
        rewrite lv_RM in *. revert H1.
        clear_all; cset_tac.
      * instantiate (1:=pick_kill k R
                                  (pick_load k R M (fst (fst a)) (snd (fst a)) (Rf \ of_list Z))
                                  (Rf \ of_list Z) (list_union (Op.freeVars ⊝ Y) \ {})).
        admit.
      * rewrite pick_kill_incl.
        rewrite pick_load_incl at 1.
        rewrite <- incl_pick_load.
        rewrite lv_RM in *.
        revert H1.
        destruct a as [[Sp L] c]. simpl in *.
        admit.
      * clear_all; cset_tac.
      * rewrite <- incl_pick_kill at 2.
        rewrite pick_kill_incl.
        rewrite pick_load_incl at 1.
        rewrite <- incl_pick_load.
        rewrite lv_RM in *.
        revert H3. clear_all.
        admit.
      * rewrite lv_RM in *.
        rewrite pick_kill_incl at 1.
        (*rewrite H3 at 1.*)
        eapply union_incl_split.
        -- clear_all. cset_tac.
        -- rewrite <- incl_pick_kill.
           rewrite <- incl_pick_load.
           revert H1.
           clear_all. cset_tac.
  - destruct a. destruct p as [Sp L]. cbn in *.
    set (L' := pick_load k R M Sp L (Op.freeVars e)) in *.
    econstructor; eauto.
    + cset_tac.
    + subst L'. rewrite pick_load_incl.
      apply Op.freeVars_live in H. rewrite H. clear - lv_RM. cset_tac.
    + instantiate (1:=(R \ Op.freeVars e) ∪ (R ∩ L')). rewrite <-minus_union.
      rewrite incl_minus_union; [|clear;cset_tac]. rewrite minus_minus.
      subst L'. setoid_rewrite <-incl_pick_load. clear; cset_tac'.
    + rewrite <-minus_union.
      rewrite union_cardinal; [|clear;intros;intro N;cset_tac].
      subst L'. rewrite pick_load_card; eauto. rewrite <-incl_pick_load.
      rewrite minus_minus.
      assert (forall n1 n2 n3 n4 : nat, n1 <= n3 -> n3 <= n2 -> n1 + (n2 - n3) <= n2) as nateq.
        { clear. intros. omega. }
        apply nateq; eauto.
        -- apply subset_cardinal;eauto. clear; cset_tac.
        -- rewrite subset_cardinal;eauto. clear; cset_tac.
  - admit.