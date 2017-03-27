Require Import RepairSpill RegLive SpillMaxKill.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL Take TakeSet OneOrEmpty AllInRel.

Set Implicit Arguments.

(** * Invariance on correct spillings *)

(* assumptions missing *)
Lemma repair_spill_inv k ZL Λ s lv sl R M ra rlv
  : (*let rlv := reg_live ZL (fst ⊝ Λ) G s sl in*)
    renamedApart s ra
    -> rlive_min k ZL Λ (R,M) s sl rlv
    -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
    -> getAnn rlv ∪ M ⊆ fst (getAnn ra)
    -> getAnn rlv ⊆ R
    -> live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> sl === repair_spill k ZL Λ R M s rlv lv sl
.
Proof.
  intros rena rliveMin rliveSnd rlv_ra sub_R liveSnd spillSnd. 
  eapply spill_sound_spill_max_kill in spillSnd; eauto;
    [|reflexivity].
  clear rena rlv_ra.
  general induction sl; invc liveSnd; invc spillSnd; invc rlive.
  - admit. (* assert (H10' := H10). assert (H9' := H9).
    assert (set_take_prefer k (L ∩ (Sp ∩ R ∪ M))
                              ((fst (nth (counted l) Λ ({},{}))
                                    \ of_list (nth (counted l) ZL nil)) \ R) [=] L) as Leq.
    {
      admit. (*
      rewrite H9, H10. apply union_subset_equal;
            rewrite H16; clear; cset_tac).*)
    }
    econstructor; econstructor; symmetry;
      apply inter_subset_equal in H9; apply inter_subset_equal in H10. 
    + rewrite Leq. rewrite H9. apply union_subset_equal.
      erewrite !gect_nth; eauto. unfold fst,snd. rewrite H17.
      apply union_incl_split; [|clear;cset_tac].
      rewrite H18, H19. rewrite H10' at 1.
      assert (K [=] set_take (cardinal (R ∪ L) - k) (R \ R_f)) as Keq by admit.
      rewrite <-Keq.
      clear; cset_tac.
    + apply Leq. 
    + rewrite Leq. erewrite !get_nth; eauto. unfold snd, fst. econstructor; eauto.
      setoid_rewrite inter_subset_equal at 2; eauto. apply union_subset_equal.
      assert (K [=] set_take (cardinal (R ∪ L) - k) (R \ R_f)) as Keq by admit.
      rewrite <-Keq.
      rewrite H18. clear; cset_tac.
    + econstructor; eauto. *)
  - assert (Sp ∩ R [=] Sp) as Speq by (apply inter_subset_equal; rewrite H7, H3, sub_R; eauto).
    econstructor; econstructor; [econstructor|]; eauto.
    assert ((L ∩ (Sp ∩ R ∪ M)) [=] L) as Leq
        by (apply inter_subset_equal in H8; rewrite Speq, H8; eauto).
    rewrite set_take_prefer_eq; rewrite Leq; eauto.
    + clear - H10. rewrite subset_cardinal; eauto.
    + rewrite H9, H3, sub_R. clear; cset_tac.
  - assert (Rlv = getAnn rlv) as Rlv_eq.
    { clear - H8. destruct rlv; isabsurd. rewrite <-H8. cbn. reflexivity. }
    cbn in H13, H18, Kx, H16. rewrite <-Rlv_eq in *.
    assert (Sp ∩ R [=] Sp) as Speq by (apply inter_subset_equal; rewrite H13, sub_R; eauto).
    assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq
        by (apply inter_subset_equal in H14; rewrite Speq, H14; eauto).
    assert (L [=] (set_take_prefer k (L ∩ (Sp ∩ R ∪ M)) (Exp.freeVars e \ R))) as Leq'.
    {
      rewrite set_take_prefer_eq; rewrite Leq; eauto.
      * clear - H18. rewrite subset_cardinal; eauto.
      * rewrite H16, sub_R. clear; cset_tac.
    }
    econstructor; [econstructor|]; [econstructor| |]; eauto.
    + rewrite union_comm. setoid_rewrite Speq at 1. rewrite union_comm.
      symmetry. rewrite union_subset_equal; eauto.
      rewrite !set_take_least_avoid_eq.
      * rewrite <-Leq'. cbn. rewrite minus_union. rewrite union_subset_equal; [|clear;cset_tac].
        rewrite minus_union. eapply Exp.freeVars_live in H23.
        -- admit.
        -- admit.
      * admit.
      * admit. 
    + rewrite set_take_prefer_eq; rewrite Leq; eauto.
      * clear - H18. rewrite subset_cardinal; eauto.
      * rewrite H16, H8, sub_R. clear; cset_tac.
    + 
  - assert (H12' := H12); assert (H13' := H13).
    assert (Sp ∩ R [=] Sp) as Speq'
        by (apply inter_subset_equal; eauto).
    assert (L ∩ (Sp ∩ R ∪ M) [=] L) as Leq'
        by (rewrite Speq'; apply inter_subset_equal; rewrite  H13; eauto).
    assert (set_take_prefer k (L ∩ (Sp ∩ R ∪ M)) (Exp.freeVars e \ R) [=] L) as Leq.
    {
      apply inter_subset_equal in H12; apply inter_subset_equal in H13.
      rewrite set_take_prefer_eq; eauto; rewrite Leq'.
      - rewrite subset_cardinal; [apply H17|]; eauto.
      - rewrite H15; clear; cset_tac.
    }
    econstructor; [econstructor|]; eauto; [econstructor|]; eauto.
    + exploit IHsl as IH'; eauto. 
    + admit.
    + econstructor; symmetry;
      apply inter_subset_equal in H12; apply inter_subset_equal in H13.
    + admit.
    + apply Leq.
  - 
      