Require Import CSet Var VarsUpTo.

Set Implicit Arguments.

Section FreshList.
  Variable V : Type.
  Context `{OrderedType V}.
  Variable fresh : set V -> V.

  Fixpoint fresh_list (G:set V) (n:nat) : list V :=
    match n with
      | 0 => nil
      | (S n) => let y := fresh G in y::fresh_list {y;G} n
    end.

  Lemma fresh_list_length (G:set V) n
  : length (fresh_list G n) = n.
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G, fresh G ∉ G.

  Definition fresh_set (G:set V) L : set V :=
    of_list (fresh_list G L).

  Lemma fresh_list_spec : forall (G:set V) n, disj (of_list (fresh_list G n)) G.
  Proof.
    intros. general induction n; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + rewrite <- H2 in H1. eauto.
      + specialize (H0 ({fresh G; G})).
        eapply H0; eauto.
        cset_tac.
  Qed.

  Lemma fresh_set_spec
  : forall (G:set V) L, disj (fresh_set G L) G.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_nodup (G: set V) n
    : NoDupA eq (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_spec.
    eapply InA_eq_of_list; eauto.
    cset_tac.
  Qed.

  Lemma fresh_list_ext n G G'
    : (forall G G', G [=] G' -> fresh G = fresh G')
      -> G [=] G'
      -> fresh_list G n = fresh_list G' n.
  Proof.
    intros EXT EQ. general induction n; simpl.
    - reflexivity.
    - f_equal. eauto.
      eapply IHn; eauto.
      erewrite EXT, EQ; eauto; reflexivity.
  Qed.

End FreshList.

Hint Resolve fresh_list_length : len.
