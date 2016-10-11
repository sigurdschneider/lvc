Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm SpillUtil ReconstrLive.

Set Implicit Arguments.


(** Lemma 1: if a register-live set al has size k, and the statement it is precedented by
    "let x := ... in"
    then x ∈ al \/ there is a spill before let and a load afterwards **)

(** Lemma 2: analogous to Lemma 1 with
    "fun f (x1 ... xj) := ... in" (j <= k) instead of "let x := ... in"
    and j spills/loads **)

(** Lemma 3: in the sitaution of Lemma 1 every load has to result in a variable which is
    live in the statement **)