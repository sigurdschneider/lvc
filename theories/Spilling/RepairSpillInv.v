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

  



Lemma stretch_rms_inv  F rms k lvF :
  length F = length rms
  -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
  -> PIR2 Equal (merge ⊝ rms) lvF
  -> PIR2 _eq rms (stretch_rms k F rms lvF)
.
Proof.
  intros lenF card pir2.
  general induction rms; destruct F; isabsurd; destruct lvF; isabsurd.
  - unfold stretch_rms. eauto.
  - unfold stretch_rms. destruct a as [Rf Mf].
    assert (cardinal (Rf ∩ s) <= k).
    {
      rewrite subset_cardinal.
      - eapply card. econstructor.
      - cbn. clear; cset_tac.
    }
    cbn in pir2. invc pir2. unfold merge in pf. cbn in pf.
    econstructor; [econstructor|].
    + rewrite set_take_eq; eauto. clear - pf.
      symmetry. apply inter_subset_equal. cset_tac.
    + rewrite set_take_eq; eauto.
      clear - pf. rewrite <- pf. apply incl_eq; cset_tac.
      (* shouldn't cset_tac try this by itself? *)
    + apply IHrms; eauto. intros. inv_get. exploit card; eauto. instantiate (1:=S n).
      econstructor; eauto.
Qed.




Lemma PIR2_Equal_Subset (X:Type) `{OrderedType X} (L L' : list ⦃X⦄) :
  PIR2 Equal L L' -> PIR2 Subset L L'
.
Proof.
  intros pir2. eapply PIR2_get; eauto.
  - intros. apply incl_set_left. eapply get_PIR2; eauto.
  - eapply PIR2_length; eauto.
Qed.


   
   
Lemma repair_spill_inv k ZL Λ Λ' s lv sl R M G ra rlv VD
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
    -> spill_live VD sl lv
    -> PIR2 _eq Λ Λ'
(*    -> R ∪ M ⊆ getAnn lv*)
    -> sl === repair_spill k ZL Λ' R M s rlv lv sl
.
Proof.
  intros rena rliveMin rliveSnd rm_ra sub_R liveSnd liveMin spillSnd cardRf sl_ra spillLv Λeq.
(*  assert (spillSnd':=spillSnd).*)
  eapply spill_sound_spill_max_kill with (R':=R) (M:=M) in spillSnd; eauto.
  general induction rliveSnd; invc liveSnd; invc spillSnd; invc rliveMin; invc rena;
    invc liveMin; invc spillLv; invc sl_ra. (*; invc spillSnd'. *)
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
    + pe_rewrite. rewrite <-Keq, <-Kxeq, <-Speq', <-Leq'. rewrite H20,H19.
      clear - rm_ra. cset_tac.
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
      * rewrite <-Speq', <-Leq', <-Keq. invc H18. cbn in *. rewrite H21, H23, H19.
        clear - rm_ra. cset_tac.
      * rewrite <-Keq, <-Leq'. rewrite <-sub_R. subst K. clear - H1; cset_tac.
      * eapply spill_max_kill_ext; eauto; [|rewrite Speq';eauto].
        rewrite <-Keq, <-Leq'. eauto.
    + eapply IHrliveSnd2; eauto.
      * rewrite <-Speq', <-Leq', <-Keq. invc H20. cbn in *. rewrite H21, H23, H19.
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
    set (R_f':= fst (nth (counted l) Λ' (∅,∅))) in *.
    set (M_f':= snd (nth (counted l) Λ' (∅,∅))) in *.
    set (L' := pick_load k R M Sp L (R_f' \ of_list Z)).     
    set (K' := pick_kill k R L' (R_f' \ of_list Z) (list_union (Op.freeVars ⊝ Y) \ M')).
    set (Sp':= ((list_union (Op.freeVars ⊝ Y) ∩ K') ∪ (M_f' \ of_list Z)) \ M ∪ (Sp ∩ R)).
    assert (R_f = fst (nth (counted l) Λ ({}, {}))) as Rfeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    assert (M_f = snd (nth (counted l) Λ ({}, {}))) as Mfeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    assert (R_f' [=] R_f) as Rfeq'.
    {
      subst R_f R_f'.
      eapply PIR2_nth in Λeq as Λeq'; eauto.
      destruct Λeq' as [[Rf' Mf'] [get_rmf rmf_eq]]. invc rmf_eq. rewrite H6.
      erewrite get_nth; eauto; cbn; eauto.
    }
    assert (M_f' [=] M_f) as Mfeq'.
    {
      subst M_f M_f'.
      eapply PIR2_nth in Λeq as Λeq'; eauto.
      destruct Λeq' as [[Rf' Mf'] [get_rmf rmf_eq]]. invc rmf_eq. rewrite H15.
      erewrite get_nth; eauto; cbn; eauto.
    }
    assert (L [=] L') as Leq'.
    {
      symmetry. subst L'. eapply pick_load_eq; eauto; rewrite Rfeq'.
      - clear - H25; cset_tac.
      - rewrite subset_cardinal; eauto. clear - H25; cset_tac.
    }
    assert (K [=] K') as Keq.
    {
      symmetry. subst K K'. rewrite pick_kill_eq; rewrite Rfeq'.
      - rewrite Leq'. clear; cset_tac.
      - rewrite <-Leq'. rewrite subset_cardinal; eauto. clear; cset_tac.
    }
    assert (Sp [=] Sp') as Speq'.
    {
      subst Sp'. rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto. rewrite <-Keq.
      subst K. rewrite Mfeq'. rewrite H26, H21, H28. clear; cset_tac.
    }
    assert (Z = nth (counted l) ZL nil) as Zeq.
    { erewrite get_nth; eauto; cbn; eauto. }
    econstructor; rewrite <-Zeq; subst R_f' M_f';
      set (R_f':= fst (nth (counted l) Λ' (∅,∅))) in *;
      set (M_f':= snd (nth (counted l) Λ' (∅,∅))) in *;
      econstructor; eauto; [econstructor|];
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
  - rename als into rlvF. rename alb into rlv_t. rename als0 into lvF. rename alb0 into lv_t.
    assert (Sp ∩ R [=] Sp) as Speq.
    { apply inter_subset_equal. rewrite H24. eauto. } 
     assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H25; rewrite Speq, H25; eauto).
    set (L' := pick_load k R M Sp L ∅).     
    set (K' := pick_kill k R L' ∅ (getAnn rlv_t)).
    set (Sp':= ((getAnn lv_t) ∩ K' \ M) ∪ (Sp ∩ R)).
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
    assert (PIR2 _eq rms (stretch_rms k (fst ⊝ F) rms (getAnn ⊝ lvF))) as rms_eq.
    {
      eapply stretch_rms_inv; eauto.
      - eauto with len.
    }
    simpl.
    assert (PIR2 _eq rms (pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms))) as pir2_rlvF.
    {
      eapply PIR2_get; [|eauto with len].
      intros. inv_get. rewrite surjective_pairing at 1. econstructor; eauto. apply incl_eq.
      - exploit H17; eauto. exploit H30; eauto. destruct x as [xx xy].
        eapply spill_max_kill_spill_sound in H32; eauto.
        eapply rlive_min_incl_R in H6; eauto.
      - exploit H3; eauto.
    }
    econstructor; eauto;
      subst L' Sp' K';
      set (L' := pick_load k R M Sp L ∅) in *;
      set (K' := pick_kill k R L' ∅ (getAnn rlv_t)) in *;
      set (Sp':= ((getAnn lv_t) ∩ K' \ M) ∪ (Sp ∩ R)) in *.
    + reflexivity.
    + eauto with len.
    + intros. inv_get.
      exploit H36; eauto. exploit H17; eauto. exploit H30; eauto.
      eapply H2 with (Λ0:=pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms) ++ Λ); eauto.
      * eapply rlive_min_ext; eauto. eapply PIR2_app; eauto. 
      * rewrite map_app. rewrite fst_zip_pair. reflexivity. eauto with len.
      * edestruct H13; eauto. dcr. rewrite H48. rewrite <-H35. cbn.
        apply incl_union_right. eapply incl_list_union; eauto.
      * destruct x1 as [Rf Mf]. eapply spill_max_kill_spill_sound in H47. cbn.
        eapply rlive_min_incl_R in H47; eauto; cbn; eauto.
      * exploit H9; eauto. rewrite map_app. eapply live_sound_monotone.
        -- apply H48.
        -- apply PIR2_app; eauto. eapply PIR2_get; eauto; [|eauto with len].
           intros. inv_get. unfold merge. cbn.
           clear H22. exploit H17; eauto. exploit H30; eauto.
           destruct x6 as [Rf Mf]. eapply spill_max_kill_spill_sound in H55.
           rewrite rlive_min_incl_R with (R:=Rf); eauto; cbn; eauto.
           clear - H34 H49 H50. eapply get_PIR2; eauto.
           ++ apply PIR2_Equal_Subset; eauto.
           ++ eapply map_get_eq; eauto.
              
      * eapply live_min_ext; eauto. eapply PIR2_app; eauto. 
      * intros. decide (n0 >= length rms).
        -- eapply cardRf; eauto. eapply get_app_right_ge; [|eapply H48].
           assert (length rms = length (pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms))) by eauto with len.
           omega.
        -- eapply get_app_lt_1 in H48.
           ++ inv_get. exploit H17; eauto. exploit H30; eauto. destruct x6 as [x61 x62].
              eapply spill_max_kill_spill_sound in H51.
              eapply rlive_min_incl_R in H51; eauto; cbn; eauto.
              apply subset_cardinal in H51. rewrite H51.
              exploit H29; eauto.
           ++ assert (length rms = length (pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms))).
              { clear - H0 H28. eauto with len. }
              omega.
      * eapply PIR2_app; eauto.
        eapply PIR2_get. intros. inv_get.
        -- exploit H17; eauto. 
           eapply get_PIR2 in rms_eq; [|eauto|eauto]. destruct x' as [x'1 x'2].
           split; [| rewrite surjective_pairing in rms_eq at 1; invc rms_eq; eauto].
           apply incl_eq; destruct x2 as [x21 x22]. 
           ++ invc rms_eq. rewrite <-H59. exploit H3; eauto.
           ++ exploit H30; eauto.
              eapply spill_max_kill_spill_sound in H56.
              eapply rlive_min_incl_R in H56; eauto; cbn; eauto. rewrite H56.
              invc rms_eq. rewrite H60. reflexivity.
        -- rewrite stretch_rms_length; eauto with len.
      * destruct x1 as [x11 x12]. eapply spill_max_kill_ext'; eauto. eapply PIR2_app; eauto.
        eapply PIR2_sym; eauto.
    + eapply IHrliveSnd with (Λ0:=pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms) ++ Λ); eauto.
      * eapply rlive_min_ext; eauto. eapply PIR2_app; eauto. 
      * rewrite map_app. rewrite fst_zip_pair. reflexivity. eauto with len.
      * rewrite H25, H24. cbn in rm_ra. pe_rewrite. rewrite <-Speq', H24. clear - rm_ra. cset_tac.
      * rewrite <-Keq. clear - H4 sub_R. cbn in sub_R. subst K. cset_tac.
      * rewrite map_app. eapply live_sound_monotone.
        -- apply H7.
        -- apply PIR2_app; eauto. eapply PIR2_get; eauto; [|eauto with len].
           intros. inv_get. unfold merge. cbn.
           clear H22. exploit H17; eauto. exploit H30; eauto.
           destruct x1 as [Rf Mf]. eapply spill_max_kill_spill_sound in H32.
           rewrite rlive_min_incl_R with (R:=Rf);  eauto; cbn; eauto.
           clear - H6 H5 H34. eapply get_PIR2; eauto.
           ++ apply PIR2_Equal_Subset; eauto.
           ++ eapply map_get_eq; eauto.
      * eapply live_min_ext; eauto. eapply PIR2_app; eauto. 
      * intros. decide (n >= length rms).
        -- eapply cardRf; eauto. eapply get_app_right_ge; [|eapply H5].
           assert (length rms = length (pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms))) by eauto with len.
           omega.
        -- eapply get_app_lt_1 in H5.
           ++ inv_get. exploit H17; eauto. exploit H30; eauto. destruct x1 as [x61 x62].
              eapply spill_max_kill_spill_sound in H21.
              eapply rlive_min_incl_R in H21; eauto; cbn; eauto.
              apply subset_cardinal in H21. rewrite H21.
              exploit H29; eauto.
           ++ assert (length rms = length (pair ⊜ (getAnn ⊝ rlvF) (snd ⊝ rms))).
              { clear - H0 H28. eauto with len. }
              omega.
      * eapply PIR2_app; eauto.
        eapply PIR2_get. intros. inv_get.
        -- exploit H17; eauto. 
           eapply get_PIR2 in rms_eq; [|eauto|eauto]. destruct x' as [x'1 x'2].
           split; [| rewrite surjective_pairing in rms_eq at 1; invc rms_eq; eauto].
           apply incl_eq; destruct x as [x21 x22]. 
           ++ invc rms_eq. rewrite <-H50. exploit H3; eauto.
           ++ exploit H30; eauto.
              eapply spill_max_kill_spill_sound in H47.
              eapply rlive_min_incl_R in H47; eauto; cbn; eauto. rewrite H47.
              invc rms_eq. rewrite H51. reflexivity.
        -- rewrite stretch_rms_length; eauto with len.
      * eapply spill_max_kill_ext'; eauto. eapply PIR2_app; eauto.
        eapply PIR2_sym; eauto. eapply spill_max_kill_ext'; eauto.
        -- instantiate (1:=rms ++ Λ). eapply PIR2_app; eauto. apply PIR2_sym; eauto.
        -- eapply spill_max_kill_ext; [| |apply H31]; clear - Keq Speq'; cset_tac.
Qed.
