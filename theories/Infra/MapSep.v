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
