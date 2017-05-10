Require Import CSet Le CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice CMapTerminating.

Require Import Plus Util AllInRel CSet OptionR.
Require Import Val Var Env IL Annotation Infra.Lattice DecSolve.
Require Import CMap WithTop.
Require Import MapNotations ListUpdateAt.
Require Import Terminating OptionR.

Set Implicit Arguments.

Open Scope map_scope.

Definition Dom D := Map [var, D].

Definition domupd D (d:Dom D) x (o:option D) : Dom D :=
  match o with
  | Some xv => (d [- x <- xv -])
  | None => remove x d
  end.

Fixpoint domjoin_list D `{JoinSemiLattice D} (m:Dom D) (A:list var) (B:list (option D)) :=
  match A, B with
  | x::A, y::B =>
    domupd (domjoin_list m A B) x (join (find x m) y)
  | _, _ => m
  end.

Definition domenv D (d:Dom D) (x:var) : option D :=
  find x d.

Lemma poLe_option_None X `{PartialOrder X} (x:option X)
  :  ⎣⎦ ⊑ x.
Proof.
  econstructor.
Qed.

Hint Resolve poLe_option_None.

Lemma domupd_le D `{PartialOrder D} (a b: Dom D) v v' x
  : leMap a b
    -> poLe v v'
    -> leMap (domupd a x v) (domupd b x v').
Proof.
  unfold leMap, domupd; intros.
  inv H1.
  - repeat cases; clear_trivial_eqs; mlud; eauto.
  - mlud; eauto.
Qed.

Lemma domjoin_list_le D `{JoinSemiLattice D} (a b: Dom D) Z Y Y'
  : leMap a b
    -> poLe Y Y'
    -> leMap (domjoin_list a Z Y)
            (domjoin_list b Z Y').
Proof.
  general induction Z; simpl domjoin_list; eauto.
  inv H2; eauto.
  - eapply domupd_le.
    + eapply IHZ; eauto.
    + eapply ojoin_poLe; eauto.
Qed.

Lemma domupd_eq D `{PartialOrder D} (a b: Dom D) v v' x
  : eqMap a b
    -> poEq v v'
    -> eqMap (domupd a x v) (domupd b x v').
Proof.
  unfold eqMap, domupd; intros.
  inv H1.
  - eapply eqMap_remove; eauto.
  - repeat cases; clear_trivial_eqs. mlud; eauto.
    econstructor. eauto.
Qed.

Lemma domjoin_list_eq  D `{JoinSemiLattice D} (a b: Dom D) Z Y Y'
  : eqMap a b
    -> poEq Y Y'
    -> eqMap (domjoin_list a Z Y)
            (domjoin_list b Z Y').
Proof.
  general induction Z; simpl domjoin_list; eauto.
  inv H2; eauto.
  - eapply domupd_eq
    + eapply IHZ; eauto.
    + eapply ojoin_poEq; eauto.
Qed.

Lemma domjoin_ne D `{JoinSemiLattice D} (m:Dom D) x y a
  : x =/= y
    -> find x (domupd m y a) = find x m.
Proof.
  unfold domupd; cases; intros; mlud; eauto.
Qed.

Lemma domjoin_list_ne D `{JoinSemiLattice D} (m:Dom D) x Z Y
  : ~ InA eq x Z
    -> find x (domjoin_list m Z Y) === find x m.
Proof.
  intros NI.
  general induction Z; destruct Y; simpl; eauto.
  erewrite domjoin_ne; eauto. eapply IHZ; eauto.
  intro; eapply NI; econstructor. eapply H1.
Qed.

Lemma domjoin_list_exp  D `{JoinSemiLattice D} (m:Dom D) Z Y
  : leMap m (domjoin_list m Z Y).
Proof.
  general induction Z; destruct Y; simpl domjoin_list; eauto;
    try reflexivity.
  unfold ojoin; repeat cases; simpl domupd; eauto.
  - hnf; intros. mlud.
    + rewrite <- e, <- Heq.
      econstructor.
      eapply join_poLe.
    + eapply IHZ.
  - hnf; intros; mlud.
    rewrite Heq, e; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
  - hnf; intros; mlud.
    rewrite <- e, <- Heq; eauto.
    eapply IHZ.
Qed.
