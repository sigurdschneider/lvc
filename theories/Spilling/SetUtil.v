Require Import List Map AllInRel.
Require Import IL AutoIndTac.


Set Implicit Arguments.

(** * SetUtil *)


Lemma add_incl (X : Type) `{OrderedType X} (x : X) (s t : ⦃X⦄)
  : {x; s} ⊆ t -> x ∈ t /\ s ⊆ t.
Proof.
  intros.
  hnf; intros;
    split; rewrite <- H0;
      cset_tac.
Qed.

Lemma of_list_empty (X : Type) `{OrderedType X} (L : list X)
  : of_list L [=] ∅ <-> L = nil.
Proof.
  destruct L; simpl; eauto.
  - split; eauto.
  - split; intros; isabsurd.
    exfalso.
    cset_tac.
Qed.

Lemma in_singleton (X : Type) `{OrderedType X} (x : X) (s : ⦃X⦄)
  : singleton x ⊆ s -> x ∈ s.
Proof.
  intros.
  hnf in H0; eauto.
Qed.

Lemma union_incl_split2 (X : Type) `{OrderedType X} (s t u : ⦃X⦄)
  : s ∪ t ⊆ u -> s ⊆ u /\ t ⊆ u.
Proof.
  intros uni.
  split;
    rewrite <- uni;
    cset_tac.
Qed.

Lemma incl_minus_union (X:Type) `{OrderedType X} (s t u : ⦃X⦄)
  : t ⊆ u -> s \ t ∪ u [=] s ∪ u.
Proof.
  intros; cset_tac.
Qed.

Lemma cap_special_in X `{OrderedType X} G
  : forall x D, x ∈ D -> {x; G} ∩ D [=] {x; G ∩ D}.
Proof.
  cset_tac.
Qed.

Lemma cap_special_notin X `{OrderedType X} G
  : forall x D, x ∉ D -> {x; G} ∩ D [=] G ∩ D.
Proof.
  cset_tac.
Qed.
