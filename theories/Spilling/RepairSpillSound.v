Require Import RepairSpill RegLive.
Require Import SpillSound Annotation Liveness.Liveness.
Require Import List Map IL.

Set Implicit Arguments.

(** * Soundness of repair_spill *)

(* assumptions missing*)
(* rlv does NOT have to be the correct reg liveness! (maybe it should have the right structure) *)
Lemma repair_spill_sound k ZL Λ R M s rlv lv sl
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> spill_sound k ZL Λ (R,M) s (repair_spill k ZL Λ R M s rlv lv sl)
.
  
                