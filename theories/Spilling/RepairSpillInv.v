Require Import RepairSpill RLiveMin RLiveSound SpillMaxKill.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL Take TakeSet OneOrEmpty AllInRel PickLK.

Set Implicit Arguments.

(** * Invariance on correct spillings *)

Lemma spill_max_kill_ext k ZL Λ R R' M M' s rlv sl :
  R [=] R'
  -> M [=] M'
  -> spill_max_kill k ZL Λ (R , M ) s rlv sl
  -> spill_max_kill k ZL Λ (R', M') s rlv sl
.
Proof.
  intros Req Meq spillKill.
  general induction spillKill.
  - econstructor; eauto; [| |eapply IHspillKill| | |];
      try rewrite <-Req; try rewrite <-Meq; eauto; eauto.
  - econstructor; eauto; try rewrite <-Req; try rewrite <-Meq; eauto.
  - econstructor; eauto; [| | | |eapply IHspillKill1|eapply IHspillKill2];
      try rewrite <-Req; try rewrite <-Meq; eauto; eauto.
  - econstructor; eauto; try rewrite <-Req; try rewrite <-Meq; eauto.
  - econstructor; eauto; [| | |eapply IHspillKill]; try rewrite <-Req; try rewrite <-Meq; eauto; eauto.
Qed.
    
(*


Inductive live_min (k:nat)
  : list params -> list (⦃var⦄ * ⦃var⦄) -> ⦃var⦄ -> stmt -> spilling -> ann ⦃var⦄ -> Prop :=
| RMinLet ZL Λ x e s an sl Rlv rlv G
  : live_min k ZL Λ (singleton x) s sl rlv
    -> (forall R M, spill_max_kill k ZL Λ (R,M) (stmtLet x e s) (ann1 Rlv rlv) (ann1 (Sp,L,rm) sl)
             -> getAnn lv ⊆ R \ K ∪ M ∪ Sp)
    -> live_min k ZL Λ G (stmtLet x e s) (ann1 (Sp,L,rm) sl) (ann1 Rlv rlv) (ann1 LV lv)
.

| RMinIf ZL Λ e s1 s2 an sl1 sl2 Rlv rlv1 rlv2 G
  : live_min k ZL Λ ∅ s1 sl1 rlv1
    -> live_min k ZL Λ ∅ s2 sl2 rlv2
    -> is_live_min k ZL Λ (stmtIf e s1 s2) (ann2 an sl1 sl2) (Rlv \ G)
    -> live_min k ZL Λ G (stmtIf e s1 s2) (ann2 an sl1 sl2) (ann2 Rlv rlv1 rlv2)
| RMinReturn ZL Λ e an Rlv G
  : is_live_min k ZL Λ (stmtReturn e) (ann0 an) (Rlv \ G)
    -> live_min k ZL Λ G (stmtReturn e) (ann0 an) (ann0 Rlv)
| RMinApp ZL Λ f Y an Rlv G
  : is_live_min k ZL Λ (stmtApp f Y) (ann0 an) (Rlv \ G)
    -> live_min k ZL Λ G (stmtApp f Y) (ann0 an) (ann0 Rlv)
| RSpillFun ZL Λ G F t spl rms sl_F sl_t Rlv rlv_F rlv_t
  : (forall n Zs sl_s rlv_s rm,
        get F n Zs
        -> get sl_F n sl_s
        -> get rlv_F n rlv_s
        -> get rms n rm
        -> live_min k (fst ⊝ F ++ ZL) (rms ++ Λ) (of_list (fst Zs) ∩ fst rm) (snd Zs) sl_s rlv_s)
    -> live_min k (fst ⊝ F ++ ZL) (rms ++ Λ) ∅ t sl_t rlv_t
    -> is_live_min k ZL Λ (stmtFun F t) (annF (spl, rms) sl_F sl_t) (Rlv \ G)
    -> live_min k ZL Λ G (stmtFun F t) (annF (spl, rms) sl_F sl_t) (annF Rlv rlv_F rlv_t)
.

 *)
      
Lemma repair_spill_inv k ZL Λ s lv sl R M G ra rlv
  : renamedApart s ra
    -> rlive_min k ZL Λ G s sl rlv
    -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
    -> R ∪ M ⊆ fst (getAnn ra)
    -> getAnn rlv ⊆ R
    -> live_sound Imperative ZL (merge ⊝ Λ) s lv
(*    -> live_min k ZL Λ G s sl rlv*)
    -> spill_sound k ZL Λ (R,M) s sl
    -> sl === repair_spill k ZL Λ R M s rlv lv sl
.
Proof.
  intros rena rliveMin rliveSnd rm_ra sub_R liveSnd (*liveMin*) spillSnd. 
  eapply spill_sound_spill_max_kill with (R':=R) (M:=M) in spillSnd; eauto.
  general induction rliveSnd; invc liveSnd; invc spillSnd; invc rliveMin; invc rena.
  (*; invc liveMin. *)
  - cbn in sub_R.
    assert (Sp ∩ R [=] Sp) as Speq by (apply inter_subset_equal; eauto).
    assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H20; rewrite Speq, H20; eauto).
    set (L' := pick_load k R M Sp L (Exp.freeVars e)).
    set (K' := pick_kill k R L' (Exp.freeVars e) (getAnn al)).
    set (Kx':= pick_killx k (R \ K' ∪ L') (getAnn al)).
    set (Sp':= (getAnn al0 ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))).
    assert (L [=] L') as Leq'.
    {
      symmetry. subst L'. eapply pick_load_eq; eauto.
      - clear - H22. cset_tac.
      - clear - H22 H24. rewrite H22, union_assoc, union_idem. eauto.
    }
    assert (K0 [=] K') as Keq.
    { subst K' K0. symmetry. rewrite Leq'. apply pick_kill_eq. rewrite <-Leq'. eauto. }
    assert (Kx [=] Kx') as Kxeq.
    {
      symmetry. subst Kx Kx'. rewrite Keq, Leq'. apply pick_killx_eq. rewrite <-Keq, <-Leq'.
      decide (cardinal (R \ K0 ∪ L) = k).
      - clear - H24 H25 e0 H7 rm_ra H20 H19.
        assert (x ∉ R \ K0 ∪ L) as x_nin.
        { cbn in rm_ra. rewrite H20, H19, rm_ra. clear - rm_ra H7. cset_tac. }
        rewrite add_cardinal_2 in H25; [| clear - x_nin; cset_tac]. rewrite e0.
        rewrite cardinal_difference' in H25; [|clear;intros; intro N; cset_tac].
        rewrite e0 in H25. omega.
      - omega.
    }
    assert (Sp [=] Sp') as Speq'.
    {
      subst Sp'. rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq. subst K0.
      admit.
      (* we need MINIMAL liveness!! *)
    }
    econstructor; [econstructor| ]; eauto; [econstructor | ]; eauto.
    subst K' Kx' L' Sp'.
    eapply IHrliveSnd; eauto;
      set (L' := pick_load k R M Sp L (Exp.freeVars e)) in *;
    set (K' := pick_kill k R L' (Exp.freeVars e) (getAnn al)) in *;
    set (Kx':= pick_killx k (R \ K' ∪ L') (getAnn al)) in *;
    set (Sp':= (getAnn al0 ∩ (K' ∪ Kx') \ M ∪ (Sp ∩ R))) in *.
    + rewrite <-Kxeq, <-Keq, <-Leq'. subst K0 Kx. rewrite minus_minus. rewrite <-minus_union.
      rewrite minus_minus. apply Exp.freeVars_live in H9. rewrite H9.
      rewrite minus_incl, meet_comm, meet_in_left. admit.
    + rewrite <-Kxeq, <-Keq, <-Leq'. subst K0 Kx. rewrite minus_minus. rewrite <-minus_union.
      rewrite minus_minus. setoid_rewrite <-sub_R at 1. clear - H1. cset_tac.
    + eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto]. rewrite Keq, Kxeq, Leq'. eauto.
  - cbn in sub_R.
    assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H19. eauto. } 
    assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H23; rewrite Speq, H23; eauto).
    set (L' := pick_load k R M Sp L (Op.freeVars e)).
    set (K' := pick_kill k R L' (Op.freeVars e) (getAnn al1 ∪ getAnn al2)).
    set (Sp':= (getAnn al0 ∪ getAnn al3 ∩ K' \ M ∪ (Sp ∩ R))).
    assert (L [=] L') as Leq'.
    {
      symmetry. subst L'. eapply pick_load_eq; eauto.
      - clear - H24; cset_tac.
      - rewrite H24, union_assoc, union_idem. eauto.
    }
    assert (K [=] K') as Keq.
    {
      symmetry. subst K K'. rewrite pick_kill_eq.
      - rewrite Leq'. clear; cset_tac.
      - rewrite <-Leq'. rewrite <-union_assoc. eauto.
    }
    assert (Sp [=] Sp') as Speq'.
    {
      subst Sp'. rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq. subst K.
      admit.
      (* we need MINIMAL liveness!! *)
    } 
    econstructor; [econstructor| |]; eauto; [econstructor | |]; eauto;
      subst L' K' Sp';
      set (L' := pick_load k R M Sp L (Op.freeVars e)) in *;
      set (K' := pick_kill k R L' (Op.freeVars e) (getAnn al1 ∪ getAnn al2)) in *;
      set (Sp':= (getAnn al0 ∪ getAnn al3 ∩ K' \ M ∪ (Sp ∩ R))) in *.
    + eapply IHrliveSnd1; eauto.
      * admit.
      * rewrite <-Keq, <-Leq'. rewrite <-sub_R. subst K. clear - H1; cset_tac.
      * eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto].
        rewrite <-Keq, <-Leq'. eauto.
    + eapply IHrliveSnd2; eauto.
      * admit.
      * rewrite <-Keq, <-Leq'. rewrite <-sub_R. subst K. clear - H2; cset_tac.
      * eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto].
        rewrite <-Keq, <-Leq'. eauto.
  - admit.
  - cbn in sub_R.
    assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H; eauto. }
    econstructor; econstructor; [econstructor|]; eauto.
    assert ((L ∩ (Sp ∩ R ∪ M)) [=] L) as Leq.
    { apply inter_subset_equal in H11. rewrite Speq. eauto. }
    rewrite pick_load_eq; eauto.
    + clear - H12. cset_tac.
    + rewrite subset_cardinal; eauto. clear - H12; cset_tac.
  - admit.
