Require Import CSet Util MoreList Take MoreInversion LengthEq.

Fixpoint range (n d:nat) :=
  match d with
  | 0 => nil
  | S d => n::range (S n) d
  end.

Lemma range_get k d n x
  : get (range k d) n x
    -> x = k + n.
Proof.
  intros. general induction d; simpl in *; isabsurd.
  inv H. omega. eapply IHd in H4. omega.
Qed.

Lemma get_range k d n x
  : x = k + n
    -> n < d
    -> get (range k d) n x.
Proof.
  intros. general induction d; simpl in *; isabsurd.
  destruct n.
  - orewrite (k + 0 = k). eauto using get.
  - econstructor. eapply IHd; eauto. omega. omega.
Qed.

Ltac range_get_simpl :=
  match goal with
  | [H : get (range ?k ?d) ?n ?x |- _ ] =>
    eapply range_get in H; try (is_var x; subst x)
  end.

Smpl Add range_get_simpl : inv_get.

Lemma range_len k n
  : ❬range k n❭ = n.
Proof.
  general induction n; simpl; eauto.
Qed.

Ltac range_len_simpl :=
  match goal with
  | [ H : context [ ❬range ?k ?d❭ ] |- _ ] => rewrite (@range_len k d) in H
  | [ |- context [ ❬range ?k ?d❭ ] ] => rewrite (@range_len k d)
  end.

Smpl Add range_len_simpl : len.

Lemma x_notin_range x k n
  : x ∉ of_list (range k n)
    -> x < k \/ k+n <= x.
Proof.
  general induction n; simpl in *.
  - decide (x < k); omega.
  - decide (x = k); subst;
      cset_tac'. eapply IHn in H1. destruct H1.
    omega. omega.
Qed.

Lemma x_in_range x k n
  : x >= k /\ k+n > x -> x ∈ of_list (range k n).
Proof.
  general induction n; simpl in *; dcr.
  - exfalso; omega.
  - decide (x = k); subst;
      cset_tac'. eapply IHn. omega.
Qed.

Lemma in_range_x x k n
  : x ∈ of_list (range k n) -> x >= k /\ k+n > x.
Proof.
  general induction n; simpl in *; dcr.
  - cset_tac.
  - decide (x = k); subst; try omega.
    cset_tac'; eapply IHn in H0; omega.
Qed.


Lemma take_range k n d
  : Take.take k (range n d) = range n (min k d).
Proof.
  general induction k; simpl; eauto.
  repeat cases; eauto.
  simpl in *. f_equal; eauto.
Qed.


Lemma range_nodup i d
  : NoDupA eq (range i d).
Proof.
  general induction d; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro. eapply InA_eq_of_list in H.
  eapply in_range_x in H. omega.
Qed.
