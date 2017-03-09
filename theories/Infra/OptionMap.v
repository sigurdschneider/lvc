Require Import Util Option Get LengthEq.

Section ParametricOptionMapIndex.
  Variables X Y : Type.
  Hypothesis f : nat -> X -> option Y : Type.

  Fixpoint omapi_impl (n:nat) (L:list X) : option (list Y) :=
    match L with
      | x::L =>
        mdo v <- f n x;
          mdo vl <- omapi_impl (S n) L;
          Some (v::vl)
      | _ => Some nil
    end.

  Definition omapi := omapi_impl 0.

End ParametricOptionMapIndex.

Arguments omapi [X] [Y] f L.


Section ParametricOptionMap.
  Variables X Y : Type.
  Hypothesis f : X -> option Y : Type.

  Fixpoint omap (L:list X) : option (list Y) :=
    match L with
      | x::L =>
        mdo v <- f x;
          mdo vl <- omap L;
          Some (v::vl)
      | _ => Some nil
    end.

  Lemma omap_inversion (L:list X) (L':list Y)
  : omap L = Some L'
    -> forall n x, get L n x -> { y : Y | get L' n y /\ f x = Some y }.
  Proof.
    intros. general induction L.
    - simpl in H. monad_inv H.
      eapply get_getT in H0. inv H0.
      + eauto using get.
      + edestruct IHL; eauto using getT_get; dcr.
        eauto using get.
  Qed.

End ParametricOptionMap.

Arguments omap [X] [Y] f L.

Lemma omap_agree X Y (f g: X -> option Y) L
: (forall n x, get L n x -> f x = g x)
  -> omap f L = omap g L.
Proof.
  general induction L; simpl; eauto.
  erewrite <- H; eauto using get. erewrite IHL; eauto using get.
Qed.

Lemma omap_agree_2 X X' Y (f: X -> option Y) (g: X' -> option Y) L L'
: (forall n x y, get L n x -> get L' n y -> f x = g y)
  -> length L = length L'
  -> omap f L = omap g L'.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; simpl; eauto.
  erewrite <- H; eauto using get. erewrite IHlength_eq; eauto using get.
Qed.

Lemma omap_length X Y L' (f: X -> option Y) L
: omap f L = Some L'
  -> length L = length L'.
Proof.
  general induction L; simpl in * |- *; eauto.
  clear_trivial_eqs.

  monad_inv H; simpl; eauto.
Qed.

Lemma omap_app X Y (f:X->option Y) L L'
: omap f (L ++ L') =
  mdo v <- omap f L;
  mdo v' <- omap f L';
  Some (v ++ v').
Proof.
  general induction L; simpl in * |- *.
  - destruct (omap f L'); eauto.
  - destruct (f a); simpl; eauto.
    rewrite IHL; eauto.
    destruct (omap f L); simpl; eauto.
    destruct (omap f L'); simpl; eauto.
Qed.

Hint Extern 5 =>
match goal with
| [ EQ : ❬?Y❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?l❭ ] =>
  rewrite <- EQ; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?Y❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?l❭ = ❬?x❭ ] =>
  rewrite <- EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?x❭ = ❬?Y❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?l❭ ] =>
  rewrite EQ; eapply (omap_length _ _ _ _ _ OMAP)
| [ OMAP: omap _ _ = Some ?l  |- ❬?l❭ = ❬?B❭ ] =>
  etransitivity; [ symmetry; eapply (omap_length _ _ _ _ _ OMAP)|]
| [ EQ : ❬?l❭ = ❬?x❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?Y❭ ] =>
  rewrite <- EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
| [ EQ : ❬?x❭ = ❬?l❭, OMAP: omap _ ?Y = Some ?l  |- ❬?x❭ = ❬?Y❭ ] =>
  rewrite EQ; symmetry; eapply (omap_length _ _ _ _ _ OMAP)
end : len.
