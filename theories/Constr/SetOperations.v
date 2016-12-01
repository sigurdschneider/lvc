Require Export Setoid Coq.Classes.Morphisms.
Require Export EqDec Get CSet Take Map AllInRel.

Lemma transpose_union X `{OrderedType X}
      : transpose Equal union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma transpose_union_eq X `{OrderedType X}
      : transpose _eq union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma transpose_union_subset X `{OrderedType X}
      : transpose Subset union.
Proof.
  repeat (hnf; intros). cset_tac; intuition.
Qed.

Lemma fold_union_incl X `{OrderedType.OrderedType X} s u (x:X) y
  : x ∈ y
    -> y ∈ s
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - exfalso. eapply H0; eauto.
  - rewrite fold_2; [
    | eapply Equal_ST
    | eapply union_m
    | eapply transpose_union
    | eapply H1
    | eapply H2 ].
    eapply Add_Equal in H2. rewrite H2 in H4. clear H2.
    cset_tac'. rewrite H2 in n. exfalso; eauto.
Qed.

Lemma fold_union_incl_start X `{OrderedType.OrderedType X} s u (x:X)
  : x ∈ u
    -> x ∈ fold union s u.
Proof.
  revert_except s.
  pattern s. eapply set_induction; intros.
  - rewrite fold_1; eauto using Equal_ST.
  - rewrite fold_2; [
    | eapply Equal_ST
    | eapply union_m
    | eapply transpose_union
    | eapply H1
    | eapply H2 ].
    cset_tac.
Qed.

Instance fold_union_Proper X `{OrderedType X}
  : Proper (_eq ==> _eq ==> _eq) (fold union).
Proof.
  unfold Proper, respectful.
  intros. revert_except x. pattern x.
  eapply set_induction; intros.
  - repeat rewrite fold_1; eauto.
    rewrite <- H1; eauto.
  - rewrite fold_2; [
    | eapply Equal_ST
    | eapply union_m
    | eapply transpose_union
    | eapply H1
    | eapply H2 ].
    eapply Add_Equal in H2.
    rewrite H3 in H2.
    eapply Add_Equal in H2.
    symmetry.
    rewrite fold_2; [
    | eapply Equal_ST
    | eapply union_m
    | eapply transpose_union
    | eapply H1
    | eapply H2 ].
    rewrite H0; try reflexivity. eauto.
Qed.

Lemma fold_union_app X `{OrderedType X} Gamma Γ'
: fold union (Gamma ∪ Γ') {}[=]
  fold union Gamma {} ∪ fold union Γ' {}.
Proof.
  revert Γ'. pattern Gamma. eapply set_induction.
  - intros. eapply empty_is_empty_1 in H0.
    rewrite H0. rewrite empty_neutral_union.
    rewrite fold_empty.
    rewrite empty_neutral_union. reflexivity.
  - intros.
    eapply Add_Equal in H2. rewrite H2.
    assert ({x; s} ∪ Γ' [=] (s ∪ {x; Γ'})).
    clear_all; cset_tac; intuition.
    rewrite H3. rewrite H0.
    decide (x ∈ Γ').
    rewrite (@add_fold ⦃X⦄ _ _ _ _ Equal Equal_ST union);
      [| eapply union_m | eapply transpose_union | eauto ].
    rewrite (@fold_add ⦃X⦄ _ _ _ _ Equal Equal_ST union _); [| eapply transpose_union | ]; eauto.
    symmetry.
    rewrite union_comm. rewrite <- union_assoc.
    rewrite <- (union_comm _ x).
    rewrite (incl_union_absorption _ x). rewrite union_comm. reflexivity.
    hnf; intros. eapply fold_union_incl; eauto.
    rewrite (@fold_add ⦃X⦄ _ _ _ _ Equal Equal_ST union _); [| eapply transpose_union | ]; eauto.
    rewrite (@fold_add ⦃X⦄ _ _ _ _ Equal Equal_ST union _); [| eapply transpose_union | ]; eauto.
    symmetry. rewrite (union_comm _ x). rewrite union_assoc. reflexivity.
Qed.



Lemma fold_single {X} `{OrderedType X} Y `{Equivalence Y} (f:X->Y->Y)
      `{Proper _ (_eq ==> R ==> R) f} (x:X) (s:Y)
      : transpose R f
        -> R (fold f {{x}} s) (f x s).
Proof.
  hnf; intros.
  rewrite fold_2; eauto. simpl. rewrite fold_empty. reflexivity.
Qed.


Lemma incl_fold_union X `{OrderedType X} s t x
  :  x \In fold union s t
     -> (exists s', s' ∈ s /\ x ∈ s') \/ x ∈ t.
Proof.
  revert_except s. pattern s. eapply set_induction; intros.
  - assert (fold union s0 t [=] t) by
        (rewrite fold_1; eauto using Equal_ST; reflexivity).
    rewrite H2 in H1; eauto.
  - eapply Add_Equal in H2. rewrite H2 in H3.
    decide (x ∈ s0).
    + rewrite fold_add in H3; eauto using union_m, transpose_union_subset.
    + rewrite fold_add with (eqA:=Equal) in H3; eauto using union_m, transpose_union, Equal_ST.
      cset_tac'.
      * eapply H0 in H6; cset_tac.
Qed.

Instance fold_union_morphism X `{OrderedType X}
: Proper (Subset ==> Subset ==> Subset) (fold union).
Proof.
  unfold Proper, respectful; intros.
  hnf; intros.
  eapply incl_fold_union in H2. destruct H2.
  - destruct H2; dcr.
    eapply fold_union_incl; eauto.
  - eapply fold_union_incl_start; eauto.
Qed.

Lemma lookup_set_list_union
      X `{OrderedType X } Y `{OrderedType Y} (ϱ:X->Y) `{Proper _ (_eq ==> _eq) ϱ} l s s'
: lookup_set ϱ s[=]s' ->
  lookup_set ϱ (fold_left union l s)
             [=]  fold_left union (List.map (lookup_set ϱ) l) s'.
Proof.
  general induction l; simpl; eauto.
  eapply IHl; eauto. rewrite lookup_set_union; eauto.
  rewrite H2. reflexivity.
Qed.

Lemma list_union_take_incl X `{OrderedType X} (L:list (set X)) n
  : list_union (take n L) ⊆ list_union L.
Proof.
  eapply list_union_incl; intros; inv_get; eauto with cset.
  eapply incl_list_union; eauto.
Qed.
