Require Import RepairSpill RLiveMin RLiveSound LiveMin SpillMaxKill.
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
Lemma stretch_rms_inv k ZL Λ R M F t Rlv rlv_F rlv_t Sp L rms sl_F sl_t :
  spill_max_kill k ZL Λ (R,M) (stmtFun F t) (annF Rlv rlv_F rlv_t) (annF (Sp,L,rms) sl_F sl_t)
  -> rms === stretch_rms k F rms lvF
.
Proof.
*)
   
      
Lemma repair_spill_inv k ZL Λ s lv sl R M G ra rlv
  : renamedApart s ra
    -> rlive_min k ZL Λ G s sl rlv
    -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
    -> R ∪ M ⊆ fst (getAnn ra)
    -> getAnn rlv ⊆ R
    -> live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> live_min k ZL Λ G s sl lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> (forall Rf Mf n, get Λ n (Rf,Mf) -> cardinal Rf <= k)
    -> ann_R (fun x (y : ⦃var⦄ * ⦃var⦄) => (list_union (merge ⊝ snd x)) ⊆ fst y) sl ra
    -> sl === repair_spill k ZL Λ R M s rlv lv sl
.
Proof.
  intros rena rliveMin rliveSnd rm_ra sub_R liveSnd liveMin spillSnd cardRf sl_ra.
(*  assert (spillSnd':=spillSnd).*)
  eapply spill_sound_spill_max_kill with (R':=R) (M:=M) in spillSnd; eauto.
  clear sl_ra.
  general induction rliveSnd; invc liveSnd; invc spillSnd; invc rliveMin; invc rena;
    invc liveMin. (*; invc spillSnd'. *)
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
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq.
      apply spill_max_kill_spill_sound in H21 as spillSnd.
      eapply live_min_incl_R in H26; eauto; [|clear;cset_tac]. rewrite H26.
      rewrite <-Kxeq. 
      assert (K0 ∪ Kx [=] (R ∪ L) ∩ (K0 ∪ Kx)) as seteq.
      { symmetry. rewrite meet_comm. apply inter_subset_equal. subst K0 Kx. clear; cset_tac. }
      rewrite seteq.
      assert (x ∉ (K0 ∪ Kx) \ L) as x_nin.
      { subst K0 Kx. clear - H2. cset_tac. }
      rewrite H20. rewrite H20 in x_nin. clear - x_nin. cset_tac.
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
      rewrite minus_incl, meet_comm, meet_in_left.
      invc H16. cbn in *. rewrite H14.
      apply union_incl_split.
      * apply incl_add_eq. split; [clear;cset_tac|]. apply incl_union_incl_minus in H1. rewrite H1.
        rewrite H20, sub_R, H19. clear - rm_ra. cset_tac.
      * rewrite <-Speq'. rewrite H19. clear - rm_ra. cset_tac.
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
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq.
      apply spill_max_kill_spill_sound in H26 as spillSnd1.
      apply spill_max_kill_spill_sound in H27 as spillSnd2.
      eapply live_min_incl_R in H31; eauto; [|clear;cset_tac]. rewrite H31.
      eapply live_min_incl_R in H37; eauto; [|clear;cset_tac]. rewrite H37.
      assert (K [=] R ∩ K) as seteq.
      { symmetry. rewrite meet_comm. apply inter_subset_equal. subst K. clear; cset_tac. }
      rewrite seteq.
      rewrite H23. clear. cset_tac.
    } 
    econstructor; [econstructor| |]; eauto; [econstructor | |]; eauto;
      subst L' K' Sp';
      set (L' := pick_load k R M Sp L (Op.freeVars e)) in *;
      set (K' := pick_kill k R L' (Op.freeVars e) (getAnn al1 ∪ getAnn al2)) in *;
      set (Sp':= (getAnn al0 ∪ getAnn al3 ∩ K' \ M ∪ (Sp ∩ R))) in *.
    + eapply IHrliveSnd1; eauto.
      * rewrite <-Speq', <-Leq', <-Keq. invc H18. cbn in *. rewrite H17, H23, H19.
        clear - rm_ra. cset_tac.
      * rewrite <-Keq, <-Leq'. rewrite <-sub_R. subst K. clear - H1; cset_tac.
      * eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto].
        rewrite <-Keq, <-Leq'. eauto.
    + eapply IHrliveSnd2; eauto.
      * rewrite <-Speq', <-Leq', <-Keq. invc H20. cbn in *. rewrite H17, H23, H19.
        clear - rm_ra. cset_tac.
      * rewrite <-Keq, <-Leq'. rewrite <-sub_R. subst K. clear - H2; cset_tac.
      * eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto].
        rewrite <-Keq, <-Leq'. eauto.
  - cbn in sub_R.
    assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H20. eauto. } 
     assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H21; rewrite Speq, H21; eauto).
    inv_get.
    set (L' := pick_load k R M Sp L (R_f \ of_list Z)).     
    set (K' := pick_kill k R L' (R_f \ of_list Z) (list_union (Op.freeVars ⊝ Y) \ M')).
    set (Sp':= ((list_union (Op.freeVars ⊝ Y) ∩ K') ∪ (M_f \ of_list Z)) \ M ∪ (Sp ∩ R)).
    assert (L [=] L') as Leq'.
    {
      symmetry. subst L'. eapply pick_load_eq; eauto.
      - clear - H25; cset_tac.
      - rewrite subset_cardinal; eauto. clear - H25; cset_tac.
    }
    assert (K [=] K') as Keq.
    {
      symmetry. subst K K'. rewrite pick_kill_eq.
      - rewrite Leq'. clear; cset_tac.
      - rewrite <-Leq'. rewrite subset_cardinal; eauto. clear; cset_tac.
    }
    assert (Sp [=] Sp') as Speq'.
    {
      subst Sp'. rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq.
      subst K. rewrite H26, H21, H28. clear; cset_tac.
    }
    assert (R_f = fst (nth (counted l) Λ ({}, {}))) as Rfeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    assert (M_f = snd (nth (counted l) Λ ({}, {}))) as Mfeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    assert (Z = nth (counted l) ZL nil) as Zeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    econstructor; rewrite <-Rfeq, <-Mfeq, <-Zeq; econstructor; eauto; [econstructor|];
      [| |econstructor]; eauto; [|reflexivity]; econstructor.
    + erewrite get_nth; eauto. instantiate (1:=(R',M')); eauto.
      econstructor.
    + subst Sp' K' L'. rewrite <-Speq', <-Keq, <-Leq'. erewrite get_nth; eauto.
      * instantiate (1:=(R',M')). unfold snd.
        assert (M' ∩ (Sp ∪ M) [=] M') as M'eq.
        { apply inter_subset_equal; eauto. }
        rewrite M'eq. symmetry. apply union_subset_equal. rewrite H27. clear; cset_tac.
      * econstructor.
  - cbn in sub_R.
    assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H; eauto. }
    econstructor; econstructor; [econstructor|]; eauto.
    assert ((L ∩ (Sp ∩ R ∪ M)) [=] L) as Leq.
    { apply inter_subset_equal in H11. rewrite Speq. eauto. }
    rewrite pick_load_eq; eauto.
    + clear - H12. cset_tac.
    + rewrite subset_cardinal; eauto. clear - H12; cset_tac.
  - assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H24. eauto. } 
     assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H25; rewrite Speq, H25; eauto).
    set (L' := pick_load k R M Sp L ∅).     
    set (K' := pick_kill k R L' ∅ (getAnn alb)).
    set (Sp':= ((getAnn alb0) ∩ K' \ M) ∪ (Sp ∩ R)).
    assert (L [=] L') as Leq'.
    {
      symmetry. subst L'. eapply pick_load_eq; eauto.
      - clear; cset_tac.
      - rewrite subset_cardinal; eauto. clear; cset_tac.
    }
    assert (K [=] K') as Keq.
    {
      symmetry. subst K K'. rewrite pick_kill_eq.
      - rewrite Leq'. clear; cset_tac.
      - rewrite <-Leq'. rewrite subset_cardinal; eauto. clear; cset_tac.
    }
    assert (Sp [=] Sp') as Speq'.
    {
      subst Sp'. rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq.
      apply spill_max_kill_spill_sound in H31; eauto.
      eapply live_min_incl_R in H42; eauto; [|clear;cset_tac].
      rewrite H42, H25. clear; cset_tac.
    }
    econstructor; eauto;
      subst L' Sp' K';
      set (L' := pick_load k R M Sp L ∅) in *;
      set (K' := pick_kill k R L' ∅ (getAnn alb)) in *;
      set (Sp':= ((getAnn alb0) ∩ K' \ M) ∪ (Sp ∩ R)) in *.
    + eauto with len.
    + intros. inv_get. admit.
    + admit.
Admitted.

