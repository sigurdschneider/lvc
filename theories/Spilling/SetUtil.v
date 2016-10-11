Require Import List Map AllInRel.
Require Import IL AutoIndTac.


Set Implicit Arguments.




Lemma add_incl
      (X : Type)
      `{OrderedType X}
      (x : X)
      (s t : ⦃X⦄)
  :
    {x; s} ⊆ t
    -> x ∈ t /\ s ⊆ t
.
Proof.
  intros.
  hnf; intros;
    split; rewrite <- H0;
      cset_tac.
Qed.




Lemma of_list_empty
      (X : Type)
      `{OrderedType X}
      (L : list X)
  :
    of_list L [=] ∅ <-> L = nil
.
Proof.
  destruct L; simpl; eauto.
  - split; eauto.
  - split; intros; isabsurd.
    exfalso.
    cset_tac.
Qed.



Definition union_fs
           (X : Type)
           `{OrderedType X}
           (a : ⦃X⦄ * ⦃X⦄)
  : ⦃X⦄
  :=
    fst a ∪ snd a
.


Lemma in_singleton
      (X : Type)
      `{OrderedType X}
      (x : X)
      (s : ⦃X⦄)
  :
    singleton x ⊆ s -> x ∈ s
.
Proof.
  intros.
  hnf in H0; eauto.
Qed.




Lemma union_incl_split2
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    s ∪ t ⊆ u -> s ⊆ u /\ t ⊆ u
.
Proof.
  intros uni.
  split;
    rewrite <- uni;
    cset_tac.
Qed.




Lemma of_list_list_union
      (X : Type)
      `{OrderedType X}
      (s : ⦃X⦄)
      (L : list ⦃X⦄)
  :
    s ∈ of_list L -> s ⊆ list_union L
.
Proof.
  intro s_in.
  apply of_list_1 in s_in.
  induction s_in;
    simpl in *; eauto.
  - rewrite H0.
    apply list_union_start.
    cset_tac.
  - rewrite list_union_start_swap, IHs_in.
    cset_tac.
Qed.
