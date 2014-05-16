Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Util.
Require Export Infra.Option EqDec AutoIndTac Tactics.

Set Implicit Arguments.

Definition functional2 :=
fun (X Y : Type) (R : X -> Y -> X -> Prop)
=> forall x (y:Y) x1 x2, R x y x1 -> R x y x2 -> x1 = x2.

Definition reducible2 :=
fun (X Y : Type) (R : X->Y->X->Prop) (x : X) => exists y x', R x y x'.

Definition normal2 :=
fun (X Y : Type) (R : X->Y->X->Prop) (x : X) => ~ reducible2 R x.

Definition reddec :=
fun (X Y : Type) (R : X->Y->X->Prop) => forall x : X, reducible2 R x \/ normal2 R x.



(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
