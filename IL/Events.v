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

Lemma filter_tau_nil evt B
 : (filter_tau evt nil ++ B)%list = filter_tau evt B.
Proof.
  destruct evt; simpl; eauto.
Qed.

Lemma filter_tau_app evt A B
 :  (filter_tau evt A ++ B)%list = filter_tau evt (A ++ B).
Proof.
  destruct evt; eauto.
Qed.

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


Lemma star2_plus2_plus2
     : forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> plus2 R y B z -> plus2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto using plus2.
  - econstructor 2; eauto. rewrite filter_tau_app; eauto.
Qed.

Lemma star2_trans
 :  forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> star2 R y B z -> star2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto.
  rewrite filter_tau_app.
  eapply S_star2; eauto.
Qed.

Lemma plus2_destr_nil
: forall (X : Type) R  (x z : X),
    plus2 R x nil z -> exists y : X, R x EvtTau y /\ star2 R y nil z.
Proof.
  intros. remember nil. induction H; subst.
  - destruct y; isabsurd. eexists; split; eauto using star2_refl.
  - destruct y; isabsurd. edestruct IHplus2; eauto; dcr.
    destruct yl; isabsurd.
    eexists; split; eauto.
    rewrite H0. econstructor 2; eauto.
Qed.

Lemma star2_plus2
: forall (X : Type) (R: X -> event -> X -> Prop) (x y z : X),
    R x EvtTau y -> star2 R y nil z -> plus2 R x nil z.
Proof.
  intros. general induction H0; eauto using plus2.
  - destruct y,yl; isabsurd.
    exploit IHstar2; eauto.
    econstructor 2; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
