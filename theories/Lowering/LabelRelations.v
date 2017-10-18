Require Import Util Get Linear.

Definition not_contains_label C l :=
  forall n l', get C n (Llabel l') -> l' <> l.

Definition all_labels_smaller C l :=
  forall n l', get C n (Llabel l') -> (l' < l)%positive.

Definition all_labels_ge C l :=
  forall n l', get C n (Llabel l') -> (l <= l')%positive.

Lemma all_not_labels C l
  : all_labels_smaller C l
    ->  not_contains_label C l.
Proof.
  intros. hnf; intros. exploit H; eauto.
  intro. subst.
  eapply Pos.lt_irrefl. eauto.
Qed.

Lemma all_not_labels_ge C l
  : all_labels_ge C (Pos.succ l)
    -> not_contains_label C l.
Proof.
  intros. hnf; intros. exploit H; eauto.
  intro. subst.
  eapply Pos.le_succ_l in H1.
  eapply Pos.lt_irrefl. eauto.
Qed.

Hint Resolve all_not_labels.

Lemma not_contains_label_app1 C C' l
  : not_contains_label C l -> not_contains_label C' l -> not_contains_label (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_smaller_app1 C C' l
  : all_labels_smaller C l -> all_labels_smaller C' l -> all_labels_smaller (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_ge_app1 C C' l
  : all_labels_ge C l -> all_labels_ge C' l -> all_labels_ge (C ++ C') l.
Proof.
  intros; hnf; intros.
  eapply get_app_cases in H1 as [? |[? ?]]; eauto.
Qed.

Lemma all_labels_smaller_le C l l'
  : all_labels_smaller C l
    -> (l <= l')%positive
    -> all_labels_smaller C l'.
Proof.
  intros; hnf; intros.
  eapply H in H1. eapply Pos.lt_le_trans; eauto.
Qed.

Lemma all_labels_ge_le C l l'
  : all_labels_ge C l
    -> (l' <= l)%positive
    -> all_labels_ge C l'.
Proof.
  intros; hnf; intros.
  eapply H in H1. etransitivity; eauto.
Qed.
