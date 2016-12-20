Require Import Nat Util Get.

Notation "'list_max' L" := (fold_left max L 0) (at level 50).

Lemma list_max_swap L x
: max (list_max L) x = fold_left max L x.
Proof.
  general induction L; simpl; eauto.
  setoid_rewrite <- IHL; eauto.
  setoid_rewrite Max.max_comm at 4.
  rewrite Max.max_assoc; eauto.
Qed.

Lemma list_max_get L n x
: get L n x
  -> x <= list_max L.
Proof.
  intros. general induction L; eauto; invt get; simpl.
  - rewrite <- list_max_swap. eapply Max.le_max_r.
  - rewrite <- list_max_swap. rewrite <- Max.le_max_l; eauto.
Qed.
