Require Import Util Get Len MoreList.

Set Implicit Arguments.

Section NRange.
  Variable V:Type.
  Variable f : V -> V.

  Fixpoint range (n:V) (d:nat) :=
    match d with
    | 0 => nil
    | S d => n::range (f n) d
    end.

  Lemma range_get k d n x
    : get (range k d) n x
      -> x = iter n k f.
  Proof.
    intros. general induction d; simpl in *; isabsurd.
    invt get.
    - simpl. reflexivity.
    - eapply IHd in H4; eauto.
  Qed.

  Lemma get_range k d n x
    : x = iter n k f
      -> n < d
      -> get (range k d) n x.
  Proof.
    intros. general induction d; simpl in *; isabsurd.
    destruct n.
    - eauto using get.
    - econstructor. eapply IHd; eauto. omega.
  Qed.

  Lemma range_len k n
    : ❬range k n❭ = n.
  Proof.
    general induction n; simpl; eauto.
  Qed.

End NRange.

Ltac range_len_simpl :=
  match goal with
  | [ H : context [ ❬@range ?V ?f ?k ?d❭ ] |- _ ] =>
    rewrite (@range_len V f k d) in H
  | [ |- context [ ❬@range ?V ?f ?k ?d❭ ] ] =>
    rewrite (@range_len V f k d)
  end.

Smpl Add range_len_simpl : len.


Ltac range_get_simpl :=
  match goal with
  | [H : get (@range ?V ?f ?k ?d) ?n ?x |- _ ] =>
    eapply (@range_get V f k d) in H; try (is_var x; subst x)
  end.

Smpl Add range_get_simpl : inv_get.
