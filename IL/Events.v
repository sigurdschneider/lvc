Require Import List.
Require Export Util Relations Val Exp AutoIndTac.

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

Definition external := nat.

Inductive extern :=
  ExternI {
      extern_fnc : external;
      extern_args : list val;
      extern_res  : val
    }.

Inductive event :=
  | EvtExtern (call:extern)
(*  | EvtTerminate   (res:val) *)
  | EvtTau.

Definition internally_deterministic {X : Type} (R : X -> event -> X -> Prop)
:= forall x y x1 x2, R x EvtTau x1 -> R x y x2 -> x1 = x2 /\ y = EvtTau.

Definition filter_tau (o:event) (L:list event) : list event :=
  match o with
      | EvtTau => L
      | e => e :: L
  end.

Inductive plus2 (X : Type) (R : X -> event -> X -> Prop)
: X -> list event -> X -> Prop :=
  plus2O  x y x' el
  : R x y x'
    -> el = (filter_tau y nil)
    -> plus2 R x el x'
| plus2S x y x' yl z el
  : R x y x'
    -> el = (filter_tau y yl)
    -> plus2 R x' yl z
    -> plus2 R x el z.


Inductive star2 (X : Type) (R : X -> event -> X -> Prop) : X -> list event -> X -> Prop :=
    star2_refl : forall x : X, star2 R x nil x
  | S_star2 : forall y x x' yl z, R x y x' -> star2 R x' yl z -> star2 R x (filter_tau y yl) z.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
