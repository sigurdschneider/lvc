Require Import Util CSet InfinitePartition MapAgreement.

Definition sep (p:inf_partition) (G:set nat) (ϱ:nat -> nat) :=
  (forall x, x ∈ G -> part_1 p x -> part_1 p (ϱ x))
  /\ (forall x, x ∈ G -> part_2 p x -> part_2 p (ϱ x)).

Instance sep_morphism_impl
  : Proper (eq ==> Equal ==> eq ==> impl) sep.
Proof.
  unfold Proper, respectful, impl. intros ? p ? x ? EQ ? ϱ ? SEP; subst.
  destruct SEP; split; intros.
  - eapply H; eauto. rewrite EQ; eauto.
  - eapply H0; eauto. rewrite EQ; eauto.
Qed.

Instance sep_morphism_iff
  : Proper (eq ==> Equal ==> eq ==> iff) sep.
Proof.
  unfold Proper, respectful; intros; subst.
  split; rewrite H0; eauto.
Qed.

Instance sep_morphism_Subset_impl
  : Proper (eq ==> Subset ==> eq ==> flip impl) sep.
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H2; split; intros; eauto.
Qed.

Instance sep_morphism_Subset_impl'
  : Proper (eq ==> flip Subset ==> eq ==> impl) sep.
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H2; split; intros; eauto.
Qed.

Lemma sep_incl p lv lv' ϱ
  : sep p lv ϱ
    -> lv' ⊆ lv
    -> sep p lv' ϱ.
Proof.
  intros A B. rewrite B; eauto.
Qed.

Lemma sep_agree p D ϱ ϱ'
  : agree_on eq D ϱ ϱ'
    -> sep p D ϱ
    -> sep p D ϱ'.
Proof.
  intros AGR [GT LE]; split; intros.
  - rewrite <- AGR; eauto.
  - rewrite <- AGR; eauto.
Qed.


Hint Resolve sep_incl sep_agree.

Lemma sep_filter_map_comm p (ϱ:nat -> nat) lv
  : sep p lv ϱ
    -> map ϱ (filter (part_1 p) lv) [=] filter (part_1 p) (map ϱ lv).
Proof.
  intros [GT LE]. cset_tac'.
  - eexists x; cset_tac'.
    pose proof (part_dich p x).
    pose proof (part_disj p (ϱ x)).
    cset_tac.
Qed.

Definition part_bounded (p:inf_subset) (k:nat) : ⦃nat⦄ -> Prop
  := fun a => cardinal (filter p a) <= k.

Instance part_bounded_impl p k
  : Proper (flip Subset ==> impl) (part_bounded p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; intros.
  rewrite H. eauto.
Qed.

Instance part_bounded_iff p k
  : Proper (Equal ==> iff) (part_bounded p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; split;
  rewrite H; eauto.
Qed.

Lemma part_bounded_sep p ϱ k lv
  (BND:part_bounded (part_1 p) k lv)
  (SEP:sep p lv ϱ)
  : part_bounded (part_1 p) k (lookup_set ϱ lv).
Proof.
  unfold part_bounded in *.
  unfold lookup_set. rewrite <- sep_filter_map_comm; eauto.
  rewrite cardinal_map; eauto.
Qed.

Lemma sep_update_part p ϱ lv x G
      (SEP:sep p (lv \ singleton x) ϱ)
  : sep p lv (ϱ [x <- least_fresh_part p G x]).
Proof.
  unfold sep in SEP; dcr.
  hnf; split; intros; lud.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
Qed.
