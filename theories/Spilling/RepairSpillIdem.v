Require Import RepairSpill RLiveMin RLiveSound LiveMin SpillMaxKill.
Require Import SpillSound Annotation Liveness.Liveness RenamedApart.
Require Import List Map IL Take TakeSet OneOrEmpty AllInRel PickLK.
Require Import RepairSpillInv RegLive.

Set Implicit Arguments.

(** * Idempotence of repair_spill with reg_live *)


Corollary repair_spill_idem k ZL Λ Λ' s lv sl R M G ra VD
  : let rlv := reg_live ZL (fst ⊝ Λ) G s sl in
    renamedApart s ra
    -> R ∪ M ⊆ fst (getAnn ra)
    -> getAnn rlv ⊆ R
    -> live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> live_min k ZL Λ G s sl lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> (forall Rf Mf n, get Λ n (Rf,Mf) -> cardinal Rf <= k)
    -> ann_R (fun x (y : ⦃var⦄ * ⦃var⦄) => (list_union (merge ⊝ snd x)) ⊆ fst y) sl ra
    -> spill_live VD sl lv
    -> PIR2 _eq Λ Λ'
    -> sl === repair_spill k ZL Λ' R M s rlv lv sl
.
Proof.
  intros rlv rena RM_sub inclR lvSnd lvMin spillSnd rmf_card sl_ra spilli Λeq.
  eapply repair_spill_inv; eauto.
  - eapply reg_live_rlive_min; eauto.
    eapply reg_live_anno; eauto.
  - eapply reg_live_sound; eauto.
Qed.

   

  


