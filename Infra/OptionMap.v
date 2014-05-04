Require Import List Option Get.

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
    - isabsurd.
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

Lemma omap_length X Y L' (f: X -> option Y) L 
: omap f L = Some L'
  -> length L = length L'.
Proof.
  general induction L; simpl in * |- *; eauto.
  monad_inv H; simpl; eauto.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)