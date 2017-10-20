Require Import CSet Take.

Set Implicit Arguments.

Record StableFresh V `{OrderedType V} :=
  {
    stable_fresh :> set V -> V -> V;
    stable_fresh_spec : forall G x, stable_fresh G x ∉ G;
    stable_fresh_ext : forall G G', G [=] G' -> forall x, stable_fresh G x = stable_fresh G' x
  }.

Arguments StableFresh V {H}.

Hint Resolve stable_fresh_spec stable_fresh_ext.

Section FreshListStable.
  Variable V : Type.
  Context `{OrderedType V}.
  Variable fresh : StableFresh V.

  Fixpoint fresh_list_stable (G:set V) (xl:list V) : list V * set V :=
    match xl with
      | nil => (nil, G)
      | x::xl => let y := fresh G x in
                let (Y,G') := fresh_list_stable {y;G} xl in
                (y::Y,G')
    end.

  Lemma fresh_list_stable_length (G:set V) xl
  : length (fst (fresh_list_stable G xl)) = length xl.
  Proof.
    general induction xl; simpl; repeat let_pair_case_eq; subst; simpl; eauto.
  Qed.

  Lemma fresh_list_stable_spec
    : forall (G:set V) L, disj (of_list (fst (fresh_list_stable G L))) G.
  Proof.
    intros. general induction L; simpl;
              repeat let_pair_case_eq; subst; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + rewrite <- H2 in H1. eapply stable_fresh_spec in H1; eauto.
      + eapply IHL; eauto; cset_tac.
  Qed.

  Lemma fresh_list_stable_nodup (G: set V) L
    : NoDupA _eq (fst (fresh_list_stable G L)).
  Proof.
    general induction L; simpl; repeat let_pair_case_eq; subst; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_stable_spec.
    eapply InA_in. eapply H0.
    cset_tac; eauto.
  Qed.

  Lemma fresh_list_stable_G G L
    : snd (fresh_list_stable G L) [=] of_list (fst (fresh_list_stable G L)) ∪ G.
  Proof.
    general induction L; simpl; repeat let_pair_case_eq; subst; simpl;
      eauto with cset.
    rewrite IHL. cset_tac.
  Qed.

End FreshListStable.

Lemma fresh_list_stable_ext V `{OrderedType V} n G G' (f:StableFresh V)
  : (forall x G G', G [=] G' -> f G x = f G' x)
    -> G [=] G'
    -> fst (fresh_list_stable f G n) = fst (fresh_list_stable f G' n).
Proof.
  intros EXT EQ. general induction n; simpl.
  - reflexivity.
  - repeat let_pair_case_eq; subst; simpl; eauto.
    f_equal; eauto.
    eapply IHn; eauto.
    erewrite EXT, EQ; eauto; reflexivity.
Qed.

Lemma fresh_list_stable_get V `{OrderedType V}
      (fresh : StableFresh V) (G: set V) L x n
  : get (fst (fresh_list_stable fresh G L)) n x
    -> exists y, get L n y /\
           x = fresh (of_list (take n (fst (fresh_list_stable fresh G L))) ∪ G) y.
Proof.
  intros Get. general induction L; simpl in *.
  - isabsurd.
  - revert Get. let_pair_case_eq; simpl_pair_eqs; subst. intros Get.
    inv Get.
    + simpl. erewrite stable_fresh_ext; eauto.
      eexists; split; eauto with get. clear; cset_tac.
    + edestruct IHL; eauto; dcr; subst.
      eexists; split; eauto using get.
      simpl. eapply stable_fresh_ext. clear; cset_tac.
Qed.

Lemma fresh_list_stable_In V `{OrderedType V}
      (fresh : StableFresh V) (G: set V) L x
  : x ∈ of_list (fst (fresh_list_stable fresh G L))
    -> exists y G', y ∈ of_list L /\
              fresh G' y === x /\ G ⊆ G'.
Proof.
  intros Get.
  eapply of_list_get_first in Get; eauto; dcr.
  eapply fresh_list_stable_get in H0; dcr; subst.
  eauto 20 using get_in_of_list.
Qed.

Hint Resolve fresh_list_stable_length : len.
