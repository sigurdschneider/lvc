Require Import String List Get.

Set Implicit Arguments.

Inductive status A :=
  | Success : A -> status A
  | Error : string -> status A.

Arguments Success [A] _.
Arguments Error [A] _%string.

Definition bind (A B : Type) (f : status A) (g : A -> status B) : status B :=
  match f with
    | Success a => g a
    | Error e   => Error e
  end.

Notation "'sdo' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200).

Definition option2status {A} : option A -> string -> status A.
intros [a|]. constructor 1. eapply a.
intros s. eapply (Error s).
Defined.


Lemma option2status_inv {A} o s (v:A)
      : option2status o s = Success v
      -> o = Some v.
Proof.
  destruct o; simpl; inversion 1; eauto.
Qed.

Arguments option2status [A] _ _%string.


Lemma bind_inversion (A B : Type) (f : status A) (g : A -> status B) (y : B) :
  bind f g = Success y -> exists x, f = Success x /\ g x = Success y.
Proof.
  destruct f. firstorder. discriminate.
Qed.

Lemma bind_inversion' (A B : Type) (f : status A) (g : A -> status B) (y : B) :
  bind f g = Success y -> { x : A | f = Success x /\ g x = Success y }.
Proof.
  destruct f. firstorder. discriminate.
Qed.

(** * Reasoning over monadic computations *)

(** The [monadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
    By definition of the bind operation, both computations [a] and
    [b] must succeed for their composition to succeed.  The tactic
    therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
*)

Ltac monadS_inv1 H :=
  match type of H with
  | (Success _ = Success _) =>
      inversion H; clear H; try subst
  | (Error _  = Success _) =>
      discriminate
  | (bind ?F ?G = Success ?X) =>
      let x   := fresh "x"  in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
        destruct (bind_inversion' F G H) as [x [EQ1 EQ2]];
        clear H;
        try (monadS_inv1 EQ2))))
  end.

Ltac monadS_inv H :=
  match type of H with
  | (Success _ = Success _) => monadS_inv1 H
  | (Error _  = Success _) => monadS_inv1 H
  | (bind ?F ?G = Success ?X) => monadS_inv1 H
  | (@eq _ (@bind _ _ _ _ _ ?G) (?X)) =>
    let X := fresh in remember G as X; simpl in H; subst X; monadS_inv1 H
  end.


Section ParametricOptionMapIndex.
  Variables X Y : Type.
  Hypothesis f : nat -> X -> status Y : Type.

  Fixpoint smapi_impl (n:nat) (L:list X) : status (list Y) :=
    match L with
      | x::L =>
        sdo v <- f n x;
          sdo vl <- smapi_impl (S n) L;
          Success (v::vl)
      | _ => Success nil
    end.

  Definition smapi := smapi_impl 0.

End ParametricOptionMapIndex.

Section ParametricZip.
  Variables X Y Z : Type.
  Hypothesis f : X -> Y -> status Z : Type.

  Fixpoint szip (L:list X) (L':list Y) : status (list Z) :=
    match L, L' with
      | x::L, y::L' =>
        sdo z <- f x y;
          sdo ZL <- szip L L';
          Success (z::ZL)
      | _, _ => Success nil
    end.

End ParametricZip.

Section ParametricStatusMap.
  Variables X Y : Type.
  Hypothesis f : X -> status Y : Type.

  Fixpoint smap (L:list X) : status (list Y) :=
    match L with
      | x::L =>
        sdo v <- f x;
          sdo vl <- smap L;
          Success (v::vl)
      | _ => Success nil
    end.

  Lemma smap_spec L L'
  : smap L = Success L'
    -> forall n x, get L n x -> exists y, f x = Success y /\ get L' n y.
  Proof.
    intros. general induction L; simpl in * |- *; isabsurd.
    - monadS_inv H.  inv H0; eauto using get.
      edestruct IHL; eauto. dcr; eauto using get.
  Qed.

  Lemma smap_length L L'
  : smap L = Success L'
    -> length L' = length L.
  Proof.
    intros. general induction L; simpl in *; try monadS_inv H; simpl; eauto.
  Qed.

End ParametricStatusMap.

Lemma smap_agree_2 X X' Y (f: X -> status Y) (g: X' -> status Y) L L'
: (forall n x y, get L n x -> get L' n y -> f x = g y)
  -> length L = length L'
  -> smap f L = smap g L'.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl; eauto.
  erewrite <- H; eauto using get. erewrite IHlength_eq; eauto using get.
Qed.

Lemma szip_length_ass X Y Z (f:X->Y-> status Z) A B C k
  : szip f A B = Success C
    -> length A = length B
    -> length A = k
    -> length C = k.
Proof.
  intros EQ LEN1 LEN2; subst. length_equify.
  general induction LEN1; simpl in *; eauto.
  monadS_inv EQ; simpl; eauto.
Qed.

Hint Resolve szip_length_ass : len.

Lemma szip_get X Y Z (f:X->Y-> status Z) A B C n a b c
  : szip f A B = Success C
    -> get A n a
    -> get B n b
    -> get C n c
    -> f a b = Success c.
Proof.
  intros EQ GetA GetB GetC.
  general induction GetA; inv GetB; inv GetC; simpl in *;
    monadS_inv EQ; eauto.
Qed.

Inductive status_eq {A} (eqA : relation A) : status A -> status A -> Prop :=
| status_eq_Error s : status_eq eqA (Error s) (Error s)
| status_eq_Some : forall a a', eqA a a' -> status_eq eqA (Success a) (Success a').

Program Instance success_Equivalence A eqA `(Equivalence A eqA) :
  Equivalence (status_eq eqA).
Next Obligation. (* reflexivity *)
  inductive_refl.
Qed.
Next Obligation. (* symmetry *)
  inductive_sym.
Qed.
Next Obligation. (* transitivity *)
  inductive_trans.
Qed.
