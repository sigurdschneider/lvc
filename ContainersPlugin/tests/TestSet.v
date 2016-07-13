Time Require Import Sets.
Open Scope set_scope.
(* Require Import SetInterface SetListInstance. *)

(* Parameter a b : set nat. *)
(* Transparent compare. *)
(* Goal a =?= b = Gt. *)
(*   unfold compare. *)
(*   unfold _cmp. *)
(*   simpl. *)
(*   unfold SetList.set_compare. *)
(*   unfold SetList.SetList.set_compare. *)
(*   unfold OrderedTypeEx.list_compare. *)
(*   unfold compare, _cmp; simpl. *)
(*   Require Import ZArith. *)
(*   Print Pcompare. *)

(* Typeclasses eauto := debug. *)
Check set nat.
Check {1; {}}.

(** Testing notations and set declarations *)
Section Test.
  Fixpoint fill (s : set nat) (n : nat) :=
    match n with
      | O => s
      | S n0 => fill {n0; s} n0
    end.
(*   Time Eval vm_compute in {}. *)
  Time Eval vm_compute in 6 \in {fill {90} 7 ~ 6}.
  Time Eval vm_compute in elements {fill {90} 7 ~ 6}.
  Require Import SetConstructs.

  Time Eval vm_compute in (cardinal (powerset (fill {12} 3))).
  Time Eval vm_compute in (elements (cart_prod
    {1; {2; {3; {}}}} {true; {false; {}}})).
  Time Eval vm_compute in (elements (diag_prod {fill {90} 7 ~ 6})).

(*   Typeclasses eauto := debug. *)
(*   Check set (set (bool + (set (list nat)))). *)
(*   Check (fill {} 8) \ {}. *)
(*   Check (fill {8} 2). *)
(*   Check ((fill {} 8) \ {}). *)
(*   Typeclasses eauto :=. *)
End Test.

Require Import SetFacts.
(** Testing sets specifications *)
Fixpoint fill_ (s : set nat) (n : nat) :=
  match n with
    | O => s
    | S n0 => fill_ {n0; s} n0
  end.
Definition fill2 n := fill_ {} n.

Lemma fill__iff :
  forall n s k, k \In (fill_ s n) <-> (k < n \/ k \In s).
Proof.
  induction n; intros s k; split; simpl; intro H.
  right; assumption.
  destruct H; auto; apply False_rec; Omega.omega.
  simpl in H; rewrite IHn in H; rewrite add_iff in H.
  decompose [or] H.
  left; auto.
  left; rewrite H1; auto.
  right; auto.
  simpl; rewrite IHn; destruct H.
  inversion H; subst.
  right; apply add_1; reflexivity.
  left; Omega.omega.
  right; apply add_2; auto.
Qed.
Theorem fill2_iff : forall n k, k \In fill2 n <-> k < n.
Proof.
  intros; unfold fill2; rewrite fill__iff; intuition.
  contradiction (empty_1 H0).
Qed.
Print Assumptions fill2_iff.

(* fail si pas recursif terminal *)
(* Fixpoint setn (A : Type) `{OT : OrderedType A} (n : nat) : Type := *)
(*   match n with *)
(*     | O => A *)
(*     | S n0 => set (setn A n0) *)
(*   end. *)
Fixpoint setn_aux
  (Acc : Type) `{Acc_OT : OrderedType Acc} (n : nat) : Type :=
  match n with
    | O => Acc
    | S n0 => setn_aux (set Acc) n0
  end.
Definition setn (A : Type) `{OrderedType A} (n : nat) : Type :=
  setn_aux A n.

Time Check ({} : setn nat 5). (* 25s *)
Definition e2 : setn nat 2 := { {} }.
Definition e3 : setn nat 3 := { e2 }.
Definition e4 : setn nat 4 := { e3 }.
Time Definition e5 : setn nat 5 := { e4 }. (* 35s *)

(* Recursif non terminal avec PRogram *)
Program Fixpoint setn_aux' (A : Type) `{OT : OrderedType A} (n : nat) :
  {S : Type & OrderedType S} :=
  match n with
    | O => existT _ A _
    | S n0 =>
      let (T, _) := @setn_aux' A OT n0 in
      existT _ (@set T _ _) _
  end.
Solve Obligations using eauto with typeclass_instances.
(*
Next Obligation.
  exact (@SOT_as_OT (set T) _ _ _).
Defined.
*)
Definition setn' (A : Type) `{OrderedType A} (n : nat) : Type :=
  projT1 (setn_aux' A n).

Check ({} : setn' nat 5). (* 1sec *)
Definition e2' : setn' nat 2 := { {} }.
Definition e3' : setn' nat 3 := { e2' }.
Definition e4' : setn' nat 4 := { e3' }.
Definition e5' : setn' nat 5 := { e4' }.

(* Les deux types d'ensemble sont interchangeables !! *)
Definition e3'' : setn nat 3 := {e2'}.
Definition e3''' : setn' nat 3 := {e2}.
