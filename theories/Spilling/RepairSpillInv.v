Require Import RepairSpill RegLive.
Require Import SpillSound Annotation Liveness.Liveness.
Require Import List Map IL Take TakeSet OneOrEmpty.

Set Implicit Arguments.

(** * Invariance on correct spillings *)

(* assumptions missing *)
Lemma repair_spill_inv k ZL Λ s lv sl R M G
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> sl === repair_spill k ZL Λ R M s lv (reg_live (fst ⊝ Λ) ZL G s sl) sl
.
Proof.
  intros liveSnd spillSnd.
  general induction sl; invc liveSnd; invc spillSnd; econstructor.
  - econstructor; econstructor; symmetry;
      apply inter_subset_equal in H9; apply inter_subset_equal in H10;
    assert (set_take_prefer k (L ∩ (Sp ∩ R ∪ M))
                              ((fst (nth (counted l) Λ ({},{}))
                                    \ of_list (nth (counted l) ZL nil)) \ R) [=] L) as Leq.
    {
      admit. (*
      rewrite H9, H10. apply union_subset_equal;
            rewrite H16; clear; cset_tac).*)
    }
    + rewrite H9 at 2. apply union_subset_equal. rewrite set_take_incl at 1. rewrite Leq.
      erewrite !get_nth; eauto. unfold fst,snd. rewrite H17.
      apply union_incl_split; [|clear;cset_tac].
      apply meet_incl. 
      rewrite H17. clear; cset_tac.
    + erewrite !get_nth; eauto. unfold fst. apply Leq.
    + erewrite !get_nth; eauto. unfold snd, fst. econstructor; eauto.
      apply union_subset_equal. rewrite Leq.
      rewrite meet_comm; apply meet_incl. rewrite H18.
      enough (R \ K ∪ L [<=] R \ set_take (cardinal (R ∪ L) -k) (R \ R_f) ∪ L) as H'.
      rewrite H'. clear. cset_tac. admit. (*
      unfold set_take; rewrite take_set_incl. rewrite minus_minus.
      rewrite meet_comm. apply meet_incl. rewrite Leq. rewrite H18, H9, H10. rewrite minus_minus.
      assert (forall s t u : ⦃var⦄, s \ (s \ t)
      apply incl_eq.
      * admit.
      * rewrite H17. apply union_incl_split.
        -- clear; cset_tac.
        -- rewrite H9 at 2. rewrite H10. unfold set_take. rewrite take_set_incl.
           rewrite H18. rewrite H16.*)

    + econstructor; eauto.      
  - econstructor; econstructor; symmetry; apply inter_subset_equal in H6;
      eauto.
    assert (Op.freeVars e \ R ∪ (L ∩ (Sp ∩ R ∪ M)) [=] L) as Hypo.
    {
      apply inter_subset_equal in H7. rewrite H6, H7. apply union_subset_equal.
      clear - H8. cset_tac.
    }
    rewrite set_take_prefer_eq; eauto.
    rewrite Hypo. rewrite subset_cardinal with (s':=R \ K ∪ L); eauto; clear; cset_tac.
  - econstructor; econstructor; symmetry;
      apply inter_subset_equal in H12; apply inter_subset_equal in H13.
    + rewrite H12 at 6. apply union_subset_equal. admit. 
    + rewrite H12, H13. apply union_subset_equal. clear - H15; cset_tac.