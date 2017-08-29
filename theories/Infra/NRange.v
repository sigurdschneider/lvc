Require Import CSet Util MoreList Take MoreInversion LengthEq NaturalRep.

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

Lemma x_notin_range V `{NaturalRepresentationSucc V} (x:V) k n
  : x ∉ of_list (range succ k n)
    -> asNat x < asNat k \/ asNat k+n <= asNat x.
Proof.
  general induction n; simpl in *.
  - decide (asNat x < asNat k); omega.
  - decide (asNat x = asNat k);
      cset_tac'.
    + exfalso. eapply asNat_inj in e; eauto.
    + eapply IHn in H4; eauto. destruct H4.
      * nr. omega.
      * nr. omega.
Qed.

Lemma x_in_range V `{NaturalRepresentationSucc V} (x:V) k n
  : asNat x >= asNat k /\ asNat k+n > asNat x -> x ∈ of_list (range succ k n).
Proof.
  revert x k.
  induction n; intros; simpl in *.
  - exfalso; omega.
  - decide (asNat x = asNat k); subst; cset_tac'.
    * rewrite <- asNat_iff in n0. exfalso; eauto.
    * rewrite asNat_iff in n0; eauto.
      eapply IHn; eauto. nr. omega.
Qed.

Lemma in_range_x  V `{NaturalRepresentationSucc V} x k n
  : x ∈ of_list (range succ k n) -> asNat x >= asNat k /\ asNat k+n > asNat x.
Proof.
  general induction n; simpl in *; dcr.
  - cset_tac.
  - decide (x === k); subst; try omega;
      cset_tac'; nr; try omega.
    eapply IHn in H3; nr; omega.
    eapply IHn in H3; nr; omega.
Qed.


Lemma take_range  V `{NaturalRepresentationSucc V} k (n:V) d
  : Take.take k (range succ n d) = range succ n (min k d).
Proof.
  general induction k; simpl; eauto.
  repeat cases; eauto.
  simpl in *. f_equal; eauto.
Qed.


Lemma range_nodup V `{NaturalRepresentationSucc V} i d
  : NoDupA _eq (range succ i d).
Proof.
  general induction d; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro.
  rewrite InA_in in H2.
  eapply in_range_x in H2. nr. omega.
Qed.


Ltac range_get_simpl :=
  match goal with
  | [H : get (range _ ?k ?d) ?n ?x |- _ ] =>
    eapply range_get in H; try (is_var x; subst x)
  end.

Smpl Add range_get_simpl : inv_get.

Ltac range_len_simpl :=
  match goal with
  | [ H : context [ ❬@range ?V ?f ?k ?d❭ ] |- _ ] =>
    rewrite (@range_len V f k d) in H
  | [ |- context [ ❬@range ?V ?f ?k ?d❭ ] ] =>
    rewrite (@range_len V f k d)
  end.

Smpl Add range_len_simpl : len.
