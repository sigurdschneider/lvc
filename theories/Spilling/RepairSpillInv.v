Require Import RepairSpill.
Require Import SpillSound Annotation Liveness.Liveness.
Require Import List Map IL.

Set Implicit Arguments.

(** * Invariance on correct spillings *)

(* assumptions missing *)
Lemma repair_spill_inv
  : live_sound Imperative ZL (merge ⊝ Λ) s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> sl === repair_spill k ZL Λ R M s lv sl
.