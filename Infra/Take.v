Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Export Infra.Option EqDec AutoIndTac Util Get.

Set Implicit Arguments.

Fixpoint take n X (L:list X) :=
  match n, L with
    | S n, x::L => x::take n L
    | _, _ => nil
  end.

Lemma get_take_lt k X (L:list X) n x
: get (take k L) n x -> n < k.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  - inv H; eauto; try omega.
    + exploit IHk; eauto. omega.
Qed.

Lemma get_take k X (L:list X) n x
: get (take k L) n x -> get L n x.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  inv H; eauto using get.
Qed.
