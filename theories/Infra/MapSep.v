Require Import Util CSet InfiniteSubset InfinitePartition MapAgreement
        MapUpdate StableFresh.


Definition sep X `{OrderedType X} (p:inf_partition X) (G:set X) (ϱ:X -> X) :=
  (forall x, x ∈ G -> part_1 p x -> part_1 p (ϱ x))
  /\ (forall x, x ∈ G -> part_2 p x -> part_2 p (ϱ x)).

Instance sep_morphism_impl X `{OrderedType X}
  : Proper (eq ==> Equal ==> eq ==> impl) (sep X).
Proof.
  unfold Proper, respectful, impl. intros ? p ? x ? EQ ? ϱ ? SEP; subst.
  destruct SEP; split; intros.
  - eapply H0; eauto. rewrite EQ; eauto.
  - eapply H1; eauto. rewrite EQ; eauto.
Qed.

Instance sep_morphism_iff X `{OrderedType X}
  : Proper (eq ==> Equal ==> eq ==> iff) (sep X).
Proof.
  unfold Proper, respectful; intros; subst.
  split; rewrite H1; eauto.
Qed.

Instance sep_morphism_Subset_impl X `{OrderedType X}
  : Proper (eq ==> Subset ==> eq ==> flip impl) (sep X).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H3; split; intros; eauto.
Qed.

Instance sep_morphism_Subset_impl' X `{OrderedType X}
  : Proper (eq ==> flip Subset ==> eq ==> impl) (sep X).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst.
  destruct H3; split; intros; eauto.
Qed.

Lemma sep_incl X `{OrderedType X} p lv lv' ϱ
  : sep X p lv ϱ
    -> lv' ⊆ lv
    -> sep X p lv' ϱ.
Proof.
  intros A B. rewrite B; eauto.
Qed.

Lemma sep_agree X `{OrderedType X} p D ϱ ϱ'
  : agree_on eq D ϱ ϱ'
    -> sep X p D ϱ
    -> sep X p D ϱ'.
Proof.
  intros AGR [GT LE]; split; intros.
  - rewrite <- AGR; eauto.
  - rewrite <- AGR; eauto.
Qed.


Hint Resolve sep_incl sep_agree.

Lemma sep_filter_map_comm X `{OrderedType X} p (ϱ:X -> X)
      `{Proper _ (_eq ==> _eq) ϱ} lv
  : sep X p lv ϱ
    -> map ϱ (filter (part_1 p) lv) [=] filter (part_1 p) (map ϱ lv).
Proof.
  intros [GT LE].
  assert (Proper (_eq ==> eq) (part_1 p)) by eapply (part_1 p).
  cset_tac'.
  - eexists x; cset_tac'.
    pose proof (part_dich p x).
    pose proof (part_disj p (ϱ x)).
    rewrite H3 in H4.
    cset_tac.
Qed.

Definition part_bounded X `{OrderedType X} (p:inf_subset X) (k:nat) : ⦃X⦄ -> Prop
  := fun a => cardinal (filter p a) <= k.

Instance filter_params
  : Params filter 1.

Instance part_bounded_impl X `{OrderedType X} p k
  : Proper (flip Subset ==> impl) (part_bounded X p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; intros.
  rewrite H0. eauto.
Qed.

Instance part_bounded_iff X `{OrderedType X} p k
  : Proper (Equal ==> iff) (part_bounded X p k).
Proof.
  unfold Proper, respectful, impl, flip, part_bounded; split;
  rewrite H0; eauto.
Qed.

Lemma part_bounded_sep X `{OrderedType X} p ϱ
      `{Proper _ (_eq ==> _eq) ϱ} k lv
  (BND:part_bounded X (part_1 p) k lv)
  (SEP:sep X p lv ϱ)
  : part_bounded X (part_1 p) k (lookup_set ϱ lv).
Proof.
  unfold part_bounded in *.
  unfold lookup_set. rewrite <- sep_filter_map_comm; eauto.
  rewrite cardinal_map; eauto.
Qed.

Lemma sep_update_list X `{OrderedType X} p ϱ (Z:list X) (lv:set X) G
      (SEP:sep X p (lv \ of_list Z) ϱ) (incl:of_list Z [<=] lv)
  : sep X p lv
        (ϱ [Z <-- fst (fresh_list_stable (stable_fresh_part p) G Z)]).
Proof.
  hnf; split; intros; decide (x ∈ of_list Z).
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H5. cset_tac'.
    exploit (@fresh_list_stable_get X _); try eapply H3; eauto; dcr.
    subst. get_functional. eapply least_fresh_part_1; eauto.
    rewrite <- H7. eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
  - edestruct update_with_list_lookup_in_list; try eapply i; dcr.
    Focus 2.
    rewrite H5. cset_tac'.
    exploit (@fresh_list_stable_get X _); try eapply H3; eauto; dcr.
    dcr. subst. get_functional. eapply least_fresh_part_2; eauto.
    rewrite <- H7. eauto.
    eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply SEP; cset_tac.
Qed.
