Require Import List.
Require Export IL.Events.

Set Implicit Arguments.

Definition reducible2 :=
  fun (X Y : Type) (R : X->Y->X->Prop) (x : X) => exists y x', R x y x'.

Definition normal2 :=
  fun (X Y : Type) (R : X->Y->X->Prop) (x : X) => ~ reducible2 R x.

Definition reddec2 :=
  fun (X Y : Type) (R : X->Y->X->Prop) => forall x : X, reducible2 R x \/ normal2 R x.

Definition internally_deterministic {X : Type} (R : X -> event -> X -> Prop)
  := forall x y x1 x2, R x EvtTau x1 -> R x y x2 -> x1 = x2 /\ y = EvtTau.

Definition externally_determined {X : Type} (R : X -> event -> X -> Prop)
  := forall x e x1 x2, R x e x1 -> R x e x2 -> x1 = x2.

Class StateType S := {
  step : S -> event -> S -> Prop;
  result : S -> option val;
  step_dec : reddec2 step;
  step_internally_deterministic : internally_deterministic step;
  step_externally_determined : externally_determined step
}.

Arguments step : simpl never.

Definition stateType S (ST:StateType S) := S.

Coercion stateType : StateType >-> Sortclass.

Smpl Create single_step [progress].

Ltac single_step := smpl single_step.