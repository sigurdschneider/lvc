Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Export Infra.Option EqDec AutoIndTac Util Get.

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

Lemma take_less_length X (L:list X) n
  : n <= length L -> length (take n L) = n.
Proof.
  intros. general induction L; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.


Lemma take_gr_length X (L:list X) n
  : n >= length L -> length (take n L) = length L.
Proof.
  intros. general induction L; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.

Lemma take_length X (L:list X) n
  : length (take n L) = min (length L) n.
Proof.
  decide (n < length L).
  - rewrite take_less_length; try omega.
    rewrite min_r; omega.
  - eapply not_lt in n0.
    rewrite min_l; try omega.
    eapply take_gr_length; eauto.
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
