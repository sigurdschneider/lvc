Require Import Util Option AllInRel Get Setoid.
Require Export paco3.
Require Import Coq.Logic.FunctionalExtensionality ClassicalFacts.

Axiom propositional_extensionality : prop_extensionality.

Notation "p =3= q" :=
  (forall x0 x1 x2, p x0 x1 x2 <-> (q x0 x1 x2:Prop))
    (at level 50, no associativity).

Definition R3Eq A B C (R R' : A -> B -> C -> Prop) :=
  R =3= R'.

Lemma pred3_extensionality A B C (R R' : A -> B -> C -> Prop)
  : R =3= R' -> R = R'.
Proof.
  intros.
  do 3 (eapply functional_extensionality; intros).
  eapply propositional_extensionality. eauto.
Qed.

Set Implicit Arguments.

Section Tower3.
  Variables A B C : Type.
  Variable f : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop).

  Definition inf3 I (F: I -> A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall i:I, F i a b c.

  Inductive T3 : (A -> B -> C -> Prop) -> Prop :=
  | T3_step R : T3 R -> T3 (f R)
  | T3_lim I (F : I -> A -> B -> C -> Prop)
    : (forall i, T3 (F i)) -> T3 (inf3 F).

  Definition companion3 (R : A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall S, T3 S -> R <3= S -> S a b c.

  Notation "'㚘'" := companion3 (at level 0).

  Lemma T_companion3 x : T3 (companion3 x).
    repeat (eapply T3_lim; intros).
    eauto.
  Qed.

  Lemma companion3_monotone : monotone3 companion3.
    hnf; intros. hnf; intros.
    eapply IN; eauto.
  Qed.

  Lemma companion3_inc R : R <3= companion3 R.
    intros; hnf; eauto.
  Qed.

  Lemma companion3_idem x : companion3 (companion3 x) = companion3 x.
    eapply pred3_extensionality. split.
    - intros H; eapply H; eauto using T_companion3.
    - eapply companion3_inc.
  Qed.

  Lemma companion3_img x : T3 x -> companion3 x = x.
    intros; eapply pred3_extensionality.
    split; intros; eauto using companion3_inc.
    eapply H0; eauto.
  Qed.

  Definition inf3_closed (P: (A -> B -> C -> Prop) -> Prop) :=
    forall I (F : I -> A -> B -> C -> Prop),
      (forall i, P (F i)) -> P (inf3 F).


  Theorem tower_ind3 P
    : inf3_closed P ->
      (forall x, P (companion3 x) -> P (f (companion3 x))) ->
      forall x, P (companion3 x).
  Proof.
    intros.
    do 3 (eapply H; intros).
    clear x i1.
    induction i0; eauto.
    rewrite <- (companion3_img i0).
    eapply H0. rewrite companion3_img; eauto.
  Qed.

  Lemma companion3_fold R
    : monotone3 f -> f (companion3 R) <3= companion3 R.
  Proof.
    intro.
    eapply tower_ind3.
    - hnf; intros. hnf; intros. eauto.
    - intros. eapply H; eauto.
  Qed.

  Lemma companion3_unfold
    : companion3 bot3 <3= f (companion3 bot3).
  Proof.
    intros. eapply PR; intros.
    - econstructor 1. eapply T_companion3.
    - isabsurd.
  Qed.

  Section UptoLemma3.
    Variable g : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop).
    Hypothesis gP : monotone3 g.

    Lemma upto3 :
      (forall x, g (companion3 x) <3= companion3 x -> g (f (companion3 x)) <3= f (companion3 x)) ->
      (forall x, g (companion3 x) <3= companion3 x).
    Proof.
      intros H1 H2.
      eapply tower_ind3.
      - intros; hnf; intros; eauto.
        hnf; eauto.
      - intros; eauto.
    Qed.

    Lemma upto_below3 :
      (forall x, g (companion3 x) <3= companion3 x) -> g <4= companion3.
    Proof.
      intros H1 r; intros.
      eapply H1. eapply gP; eauto.
      eapply companion3_inc.
    Qed.

    Lemma upto_char3 :
      monotone3 f ->
      g <4= companion3 ->
      forall x, g (companion3 x) <3= companion3 x -> g (f (companion3 x)) <3= f (companion3 x).
    Proof.
      intros gM H1 r H2; intros.
      eapply H1; eauto.
      econstructor 1. eapply T_companion3.
    Qed.
  End UptoLemma3.
End Tower3.
