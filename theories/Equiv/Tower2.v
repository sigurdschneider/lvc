Require Import Util Option AllInRel Get Setoid.
Require Export paco2.
Require Import Coq.Logic.FunctionalExtensionality ClassicalFacts.

Axiom propositional_extensionality : prop_extensionality.

Notation "p =2= q" :=
  (forall x0 x1, p x0 x1 <-> (q x0 x1:Prop))
    (at level 50, no associativity).


Lemma pred2_extensionality A B (R R' : A -> B -> Prop)
  : R =2= R' -> R = R'.
Proof.
  intros.
  do 2 (eapply functional_extensionality; intros).
  eapply propositional_extensionality. eauto.
Qed.

Set Implicit Arguments.

Section Tower2.
  Variables A B : Type.
  Variable f : (A -> B -> Prop) -> (A -> B -> Prop).

  Definition inf2 I (F: I -> A -> B -> Prop) : A -> B -> Prop :=
    fun a b => forall i:I, F i a b.

  Inductive T2 : (A -> B -> Prop) -> Prop :=
  | T2_step R : T2 R -> T2 (f R)
  | T2_lim I (F : I -> A -> B -> Prop)
    : (forall i, T2 (F i)) -> T2 (inf2 F).

  Definition companion2 (R : A -> B -> Prop) : A -> B -> Prop :=
    fun a b => forall S, T2 S -> R <2= S -> S a b.

  Notation "'㚘'" := companion2 (at level 0).

  Lemma T_companion2 x : T2 (companion2 x).
    repeat (eapply T2_lim; intros).
    eauto.
  Qed.

  Lemma companion2_monotone : monotone2 companion2.
    hnf; intros. hnf; intros.
    eapply IN; eauto.
  Qed.

  Lemma companion2_inc R : R <2= companion2 R.
    intros; hnf; eauto.
  Qed.

  Lemma companion2_idem x : companion2 (companion2 x) = companion2 x.
    eapply pred2_extensionality; split.
    - intros H; eapply H; eauto using T_companion2.
    - eapply companion2_inc.
  Qed.


  Lemma companion2_img x : T2 x -> companion2 x = x.
    intros. eapply pred2_extensionality.
    split; intros; eauto using companion2_inc.
    - eapply H0; eauto.
  Qed.

  Definition inf2_closed (P: (A -> B -> Prop) -> Prop) :=
    forall I (F : I -> A -> B -> Prop),
      (forall i, P (F i)) -> P (inf2 F).


  Theorem tower_ind2 P
    : inf2_closed P ->
      (forall x, P (companion2 x) -> P (f (companion2 x))) ->
      forall x, P (companion2 x).
  Proof.
    intros.
    do 3 (eapply H; intros).
    clear x i1.
    induction i0; eauto.
    rewrite <- (companion2_img i0).
    eapply H0. rewrite companion2_img; eauto.
  Qed.

  Lemma companion2_fold R
    : monotone2 f -> f (companion2 R) <2= companion2 R.
  Proof.
    intro.
    eapply tower_ind2.
    - hnf; intros. hnf; intros. eauto.
    - intros. eapply H; eauto.
  Qed.

  Lemma companion2_unfold
    : companion2 bot2 <2= f (companion2 bot2).
  Proof.
    intros. eapply PR; intros.
    - econstructor 1. eapply T_companion2.
    - isabsurd.
  Qed.

  Section UptoLemma2.
    Variable g : (A -> B -> Prop) -> (A -> B -> Prop).
    Hypothesis gP : monotone2 g.

    Lemma upto2 :
      (forall x, g (companion2 x) <2= companion2 x -> g (f (companion2 x)) <2= f (companion2 x)) ->
      (forall x, g (companion2 x) <2= companion2 x).
    Proof.
      intros H1 H2.
      eapply tower_ind2.
      - intros; hnf; intros; eauto.
        hnf; eauto.
      - intros; eauto.
    Qed.

    Lemma upto_below2 :
      (forall x, g (companion2 x) <2= companion2 x) -> g <3= companion2.
    Proof.
      intros H1 r; intros.
      eapply H1. eapply gP; eauto.
      eapply companion2_inc.
    Qed.

    Lemma upto_char2 :
      monotone2 f ->
      g <3= companion2 ->
      forall x, g (companion2 x) <2= companion2 x -> g (f (companion2 x)) <2= f (companion2 x).
    Proof.
      intros gM H1 r H2; intros.
      eapply H1; eauto.
      econstructor 1. eapply T_companion2.
    Qed.
  End UptoLemma2.
End Tower2.