Require Import Util Option AllInRel Get Setoid.
Require Export paco3 SmallStepRelations StateType Sim.
Require Import Coq.Logic.FunctionalExtensionality ClassicalFacts.

Axiom propositional_extensionality : prop_extensionality.

Notation "p =3= q" :=
  (forall x0 x1 x2, p x0 x1 x2 <-> (q x0 x1 x2:Prop))
    (at level 50, no associativity).


Lemma pred3_extensionality A B C (R R' : A -> B -> C -> Prop)
  : R =3= R' -> R = R'.
Proof.
  intros.
  do 3 (eapply functional_extensionality; intros).
  eapply propositional_extensionality. eauto.
Qed.

Set Implicit Arguments.

Section Tower.
  Variables A B C : Type.
  Variable f : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop).

  Definition inf I (F: I -> A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall i:I, F i a b c.

  Inductive T : (A -> B -> C -> Prop) -> Prop :=
  | T_step R : T R -> T (f R)
  | T_lim I (F : I -> A -> B -> C -> Prop)
    : (forall i, T (F i)) -> T (inf F).

  Definition companion (R : A -> B -> C -> Prop) : A -> B -> C -> Prop :=
    fun a b c => forall S, T S -> R <3= S -> S a b c.

  Lemma T_companion x : T (companion x).
    repeat (eapply T_lim; intros).
    eauto.
  Qed.

  Lemma compantion_monotone : monotone3 companion.
    hnf; intros. hnf; intros.
    eapply IN; eauto.
  Qed.

  Lemma companion_inc R : R <3= companion R.
    intros; hnf; eauto.
  Qed.

  Lemma companion_idem x : companion (companion x) = companion x.
    eapply pred3_extensionality; split.
    - intros H; eapply H; eauto using T_companion.
    - eapply companion_inc.
  Qed.


  Lemma companion_img x : T x -> companion x = x.
    intros. eapply pred3_extensionality.
    split; intros; eauto using companion_inc.
    - eapply H0; eauto.
  Qed.

  Definition inf_closed (P: (A -> B -> C -> Prop) -> Prop) :=
    forall I (F : I -> A -> B -> C -> Prop),
      (forall i, P (F i)) -> P (inf F).


  Theorem tower_ind P
    : inf_closed P ->
      (forall x, P (companion x) -> P (f (companion x))) ->
      forall x, P (companion x).
  Proof.
    intros.
    do 3 (eapply H; intros).
    clear x i1.
    induction i0; eauto.
    rewrite <- (companion_img i0).
    eapply H0. rewrite companion_img; eauto.
  Qed.

  Lemma compantion_fold R
    : monotone3 f -> f (companion R) <3= companion R.
  Proof.
    intro.
    eapply tower_ind.
    - hnf; intros. hnf; intros. eauto.
    - intros. eapply H; eauto.
  Qed.

  Lemma companion_unfold
    : companion bot3 <3= f (companion bot3).
  Proof.
    intros. eapply PR; intros.
    - econstructor 1. eapply T_companion.
    - isabsurd.
  Qed.

End Tower.

Definition simc {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  := companion (@sim_gen S _ S' _) r t σ1 σ2.

Theorem sim_simc {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  : simc bot3 t σ1 σ2 -> sim r t σ1 σ2.
Proof.
  intros. revert t σ1 σ2 H1.
  pcofix CIH; intros.
  pfold. eapply companion_unfold in H2.
  eapply sim_gen_mon; eauto.
Qed.


Theorem simc_sim {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  : sim bot3 t σ1 σ2 -> simc r t σ1 σ2.
Proof.
  intros. revert t σ1 σ2 H1.
  unfold simc.
  eapply tower_ind; intros.
  - hnf; intros; hnf; intros. eauto.
  - punfold H2.
    eapply sim_gen_mon; eauto; intros.
    destruct PR; isabsurd.
    eapply H1. eauto.
Qed.

Lemma simc_trans {S} `{StateType S} {S'} `{StateType S'} r t
       (σ1:S) (σ2:S) (σ3:S')
  : simc bot3 t σ1 σ2
    -> simc r t σ2 σ3
    -> simc r t σ1 σ3.
Proof.
Admitted.
