Require Import List Coq.Classes.Equivalence Containers.OrderedTypeEx.

(** Cast option in the framework of Monad. The code in this file is taken from CompCert. *)

Notation "⎣ x ⎦" := (Some x) (at level 0, x at level 200).
Notation "⎣⎦" := (None) (at level 0).

Set Implicit Arguments.

Definition bind (A B : Type) (g : A -> option B) (x : option A) : option B :=
  match x with
    | Some a => g a
    | None   => None
  end.

Extraction Inline bind.

Notation "'mdo' X <- A ; B" := (bind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200).

Lemma bind_inversion_Some (A B : Type) (f : option A) (g : A -> option B) (y : B) :
  bind g f = Some y -> { x : A | f = Some x /\ g x = Some y }.
Proof.
  destruct f. firstorder. discriminate.
Qed.

Lemma bind_inversion_None {A B : Type} (f : option A) (g : A -> option B) :
  bind g f = None -> f = None \/ exists x, f = Some x /\ g x = None.
Proof.
  destruct f; firstorder.
Qed.

Lemma bind_inversion_Some_equiv (A B : Type) `{Equivalence B}
      (f : option A) (g : A -> option B) (y : B) :
  bind g f === Some y -> { x : A | f = Some x /\ g x === Some y }.
Proof.
  intros.
  destruct f; simpl in *. firstorder.
  intros; exfalso. inversion H0.
Qed.

Lemma bind_inversion_None_equiv {A B : Type} `{Equivalence B} (f : option A) (g : A -> option B) :
  bind g f === None -> f = None \/ exists x, f = Some x /\ g x = None.
Proof.
  destruct f; firstorder.
  inversion H0; subst; eauto.
Qed.

Lemma option_eq_inv X R (x:X) x'
  : @option_eq _ R (Some x) (Some x') -> R x x'.
Proof.
  inversion 1; eauto.
Qed.

Ltac monad_simpl :=
  match goal with
    | [ H: ?F = _ |- context [bind ?F ?G = _] ] => rewrite H; simpl
  end.

Ltac monad_inv H :=
  match type of H with
  | (Some _ = Some _) =>
    inversion H; clear H; try subst
  | (None   = Some _) =>
    inversion H
  | (Some _ = None) =>
    inversion H
  | (Some _ === Some _) =>
    eapply option_eq_inv in H; try subst
  | (None === Some _) =>
    exfalso; inversion H
  | (Some _ === None) =>
    exfalso; inversion H
  | (bind ?F ?G = Some ?X) =>
    let x   := fresh "x"  in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (bind_inversion_Some G F H) as [x [EQ1 EQ2]];
    clear H;
    try (monad_inv EQ2)
  | (bind ?F ?G = None) =>
    let x   := fresh "x"  in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (bind_inversion_None G F H) as [|[x [EQ1 EQ2]]];
    clear H;
    try (monad_inv EQ2)
  | (bind ?F ?G === Some ?X) =>
    let x   := fresh "x"  in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (bind_inversion_Some_equiv G F H) as [x [EQ1 EQ2]];
    clear H;
    try (monad_inv EQ2)
  | (bind ?F ?G === None) =>
    let x   := fresh "x"  in
    let EQ1 := fresh "EQ" in
    let EQ2 := fresh "EQ" in
    destruct (bind_inversion_None_equiv G F H) as [|[x [EQ1 EQ2]]];
    clear H;
    try (monad_inv EQ2)
  end.

Inductive option_R_Some (A B : Type) (eqA : A -> B -> Prop)
: option A -> option B -> Prop :=
| Option_R_Some a b : eqA a b -> option_R_Some eqA ⎣a⎦ ⎣b⎦.


Lemma option_R_Some_refl A R `{Reflexive A R} : forall x, option_R_Some R ⎣x⎦ ⎣x⎦.
intros; eauto using option_R_Some.
Qed.

Instance option_R_Some_sym A R `{Symmetric A R} : Symmetric (option_R_Some R).
hnf; intros ? [] []; eauto using option_R_Some.
Qed.

Instance option_R_trans A R `{Transitive A R} : Transitive (option_R_Some R).
hnf; intros. inversion H0; subst; inversion H1; subst; econstructor; eauto.
Qed.
