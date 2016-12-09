Require Import Util CSet AnnP.

Definition bounded_below
           (c : nat)
           (k : nat)
  : ⦃nat⦄ -> Prop
  :=
    fun a => cardinal (filter (fun x => B[x <= c]) a) <= k.


Instance bounded_in_equal_morph
  : Proper (eq ==> eq ==> Equal ==> iff) bounded_below.
Proof.
  unfold Proper, respectful, bounded_below; intros; subst.
  rewrite H1. reflexivity.
Qed.

Instance bounded_in_subset_morph
  : Proper (eq ==> eq ==> Equal ==> impl) bounded_below.
Proof.
  unfold Proper, respectful, bounded_below, impl, flip; intros; subst.
  rewrite <- H1. rewrite <- H2. reflexivity.
Qed.


Instance bounded_in_equal_ptw
  : Proper (eq ==> eq ==> pointwise_relation _ iff) bounded_below.
Proof.
  unfold Proper, respectful, pointwise_relation; intros; subst.
  reflexivity.
Qed.

Instance bounded_in_impl_ptw'
  : Proper (eq ==> eq ==> pointwise_relation _ impl) bounded_below.
Proof.
  unfold Proper, respectful, pointwise_relation, impl, flip; intros; subst.
  eauto.
Qed.
