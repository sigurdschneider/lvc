Require Import Nat CSet Var MapInjectivity.

Set Implicit Arguments.

Definition slot n x := x + n.

Inductive Slot (VD:set var) :=
  {
    Slot_slot :> var -> var;
    Slot_Disj : disj VD (SetConstructs.map Slot_slot VD);
    Slot_Inj : injective_on VD Slot_slot
  }.

Hint Immediate Slot_Disj Slot_Inj.
