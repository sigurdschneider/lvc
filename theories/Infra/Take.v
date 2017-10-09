Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Export Infra.Option EqDec AutoIndTac Util Get Drop.

Set Implicit Arguments.

Fixpoint take n X (L:list X) :=
  match n, L with
    | S n, x::L => x::take n L
    | _, _ => nil
  end.

Lemma take_nil (X:Type) n
  : @take n X nil = nil.
Proof.
  destruct n; eauto.
Qed.

Lemma get_take_lt k X (L:list X) n x
: get (take k L) n x -> n < k.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  - inv H; eauto; try omega.
    + exploit IHk; eauto. omega.
Qed.

Lemma get_take_get k X (L:list X) n x
: get (take k L) n x -> get L n x.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  inv H; eauto using get.
Qed.

Lemma take_length_le X (L:list X) n
  : n <= length L -> length (take n L) = n.
Proof.
  intros. general induction L; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.


Lemma take_length_ge X (L:list X) n
  : n >= length L -> length (take n L) = length L.
Proof.
  intros. general induction L; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.

Lemma take_length X (L:list X) n
  : length (take n L) = min (length L) n.
Proof.
  decide (n < length L).
  - rewrite take_length_le; try omega.
    rewrite min_r; omega.
  - eapply not_lt in n0.
    rewrite min_l; try omega.
    eapply take_length_ge; eauto.
Qed.

Lemma take_get X (L:list X) n k x
  : get (take k L) n x -> get L n x /\ n < k.
Proof.
  intros.
  general induction H ; destruct k, L; simpl in *; inv Heql.
  - split; eauto using get; omega.
  - exploit IHget; eauto; dcr.
    split; eauto using get; omega.
Qed.

Lemma get_take X (L:list X) n k x
  : n < k
    -> get L n x
    -> get (take k L) n x.
Proof.
  intros LE GET.
  general induction GET; destruct k; simpl; eauto using get; try now (exfalso; omega).
  - econstructor.
    eapply IHGET. omega.
Qed.

 Lemma map_take X Y (f:X -> Y) (L:list X) n
  : f ⊝ take n L = take n (f ⊝ L).
Proof.
  general induction n; simpl; eauto.
  destruct L; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma take_app_le n X (L L':list X)
  : n <= length L
    -> take n (L ++ L') = take n L.
Proof.
  intros. general induction n; simpl; eauto.
  destruct L; isabsurd; simpl.
  rewrite IHn; eauto. simpl in *; omega.
Qed.

Lemma take_app_ge n X (L L':list X)
  : n >= length L
    -> take n (L ++ L') = L ++ take (n - length L) L'.
Proof.
  intros. general induction n; simpl; eauto.
  - destruct L; simpl in *; eauto. exfalso; omega.
  - destruct L; simpl in *; eauto.
    rewrite IHn; eauto. omega.
Qed.

Lemma take_eq_ge n X (L:list X)
  : n >= ❬L❭ -> take n L = L.
Proof.
  intros. general induction n; destruct L; simpl in *; eauto.
  - exfalso; omega.
  - rewrite IHn; eauto. omega.
Qed.


Lemma take_app_eq n X (L L':list X)
  : n = length L
    -> take n (L ++ L') = L.
Proof.
  intros. subst. general induction L; simpl; eauto.
  f_equal; eauto.
Qed.


Lemma drop_rev X (L:list X) k
  : drop k L = rev (take (❬L❭ - k) (rev L)).
Proof.
  general induction k.
  - simpl. rewrite take_eq_ge; eauto.
    rewrite rev_rev; eauto. rewrite rev_length; omega.
  - simpl. rewrite IHk.
    f_equal. destruct L. simpl; eauto.
    simpl.
    rewrite !take_app_le. reflexivity.
    rewrite rev_length. omega.
Qed.


Lemma take_take_lt X (L:list X) n m
  : n < m
    -> take n L = take n (take m L).
Proof.
  intros. general induction n; destruct L, m; simpl; eauto.
  - omega.
  - erewrite IHn; eauto. omega.
Qed.
Lemma take_take_app X (L:list X) n m
  : n < m
    -> take m L = take n L ++ take (m - n) (drop n L).
Proof.
  intros. general induction n; destruct L, m; simpl; eauto; try omega.
  - rewrite drop_nil, take_nil; eauto.
  - rewrite IHn; eauto. omega.
Qed.

Lemma take_one X (L:list X) x k
  : k > 0
    -> take k (x::L) = x :: take (k - 1) L.
Proof.
  intros; destruct k; simpl.
  - omega.
  - f_equal. f_equal. omega.
Qed.

Lemma take_InA A (R:A->A->Prop) L n x
  : InA R x (take n L)
    -> InA R x L.
Proof.
  general induction n; destruct L; simpl in *; isabsurd.
  invt InA; eauto using InA.
Qed.

Lemma nodup_take A (R:A->A->Prop) L n
  : NoDupA R L
    -> NoDupA R (take n L).
Proof.
  intros. general induction n; invt NoDupA; simpl; eauto using NoDupA.
  econstructor; eauto. intro. eapply take_InA in H2; eauto.
Qed.
