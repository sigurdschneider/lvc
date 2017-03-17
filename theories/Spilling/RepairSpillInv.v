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
      apply inter_subset_equal in H9; apply inter_subset_equal in H10.
    + rewrite H9; erewrite !get_nth; eauto. unfold snd. apply union_subset_equal.
      rewrite H17. clear; cset_tac.
    + erewrite !get_nth; eauto. rewrite H9, H10. unfold fst. apply union_subset_equal.
      rewrite H16. clear; cset_tac.
    + erewrite !get_nth; eauto. unfold snd, fst. econstructor; eauto.
      apply union_subset_equal. rewrite H17. unfold set_take; rewrite take_set_incl. admit. (*
      rewrite meet_comm. apply meet_incl. rewrite H18. cset_tac. rewrite H16.
      apply incl_eq.
      * admit.
      * rewrite H17. apply union_incl_split.
        -- clear; cset_tac.
        -- rewrite H9 at 2. rewrite H10. unfold set_take. rewrite take_set_incl.
           rewrite H18. rewrite H16.*)

    + econstructor; eauto.      
  - econstructor; econstructor; symmetry; apply inter_subset_equal in H6;
      eauto.
    apply inter_subset_equal in H7. rewrite H6, H7. apply union_subset_equal.
    clear - H8. cset_tac.
  - econstructor; econstructor; symmetry;
      apply inter_subset_equal in H12; apply inter_subset_equal in H13.
    + rewrite H12 at 6. apply union_subset_equal. admit. 
    + rewrite H12, H13. apply union_subset_equal. clear - H15; cset_tac.