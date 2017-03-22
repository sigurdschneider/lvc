Require Import RepairSpill RegLive.
Require Import SpillSound Annotation Liveness.Liveness.
Require Import List Map IL Take TakeSet OneOrEmpty.

Set Implicit Arguments.

(** * Invariance on correct spillings *)

(* assumptions missing *)
Lemma repair_spill_inv k ZL Λ s lv sl R M G
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> sl === repair_spill k ZL Λ R M s lv (reg_live ZL (fst ⊝ Λ) G s sl) sl
.
Proof.
  intros liveSnd spillSnd.
  general induction sl; invc liveSnd; invc spillSnd; econstructor.
  - assert (H10' := H10). assert (H9' := H9).
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
      erewrite !get_nth; eauto. unfold fst,snd. rewrite H17.
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
    + econstructor; eauto.
  - assert (H6' := H6).
    econstructor; econstructor; apply inter_subset_equal in H6;
      eauto.
    assert ((L ∩ (Sp ∩ R ∪ M)) [=] L) as Leq.
    {
      apply inter_subset_equal in H7. rewrite H6, H7. eauto.
    }
    rewrite set_take_prefer_eq; eauto.
    + rewrite Leq. rewrite subset_cardinal; eauto.
    + rewrite H8, Leq. clear; cset_tac.
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
    econstructor; econstructor; symmetry;
      apply inter_subset_equal in H12; apply inter_subset_equal in H13.
    + admit.
    + apply Leq.
      