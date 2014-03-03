Require Import Util List Get.

Set Implicit Arguments.
(** * Lemmas and tactics for lists *)

Lemma app_nil_eq X (L:list X) xl
  : L = xl ++ L -> xl = nil.
intros. rewrite <- (app_nil_l L ) in H at 1.
eauto using app_inv_tail.
Qed.

Lemma cons_app X (x:X) xl
  : x::xl = (x::nil)++xl.
eauto.
Qed.


Fixpoint tabulate X (x:X) n : list X :=
  match n with 
    | 0 => nil
    | S n => x::tabulate x n
  end.


Section ParametricZip.
  Variables X Y Z : Type.
  Hypothesis f : X -> Y -> Z : Type.

  Fixpoint zip (L:list X) (L':list Y) : list Z :=
    match L, L' with
      | x::L, y::L' => f x y::zip L L'
      | _, _ => nil
    end.
  
  Lemma zip_get L L' n (x:X) (y:Y)
  : get L n x -> get L' n y -> get (zip L L') n (f x y).
  Proof.
    intros. general induction n; inv H; inv H0; simpl; eauto using get.
  Qed.

  Lemma get_zip L L' n (z:Z)
  : get (zip L L') n z 
    -> { x : X & {y : Y | get L n x /\ get L' n y /\ f x y = z } } .
  Proof.
    intros. general induction L; destruct L'; isabsurd.
    simpl in H. destruct n. 
    - eexists a; eexists y. inv H; eauto using get.
    - edestruct IHL as [x' [y' ?]]; dcr; try inv H; eauto 20 using get.
  Qed.

End ParametricZip.

Arguments zip [X] [Y] [Z] f L L'.
Arguments zip_get [X] [Y] [Z] f [L] [L'] [n] [x] [y] _ _.

Lemma map_zip X Y Z (f: X -> Y -> Z) W (g: Z -> W) L L'
: map g (zip f L L') = zip (fun x y => g (f x y)) L L'.
Proof.
  general induction L; destruct L'; simpl; eauto using f_equal.
Qed.

Lemma zip_map_l X Y Z (f: X -> Y -> Z) W (g: W -> X) L L'
: zip f (map g L) L' = zip (fun x y => f (g x) y) L L'.
Proof.
  general induction L; destruct L'; simpl; eauto using f_equal.
Qed.

Lemma zip_map_r X Y Z (f: X -> Y -> Z) W (g: W -> Y) L L'
: zip f L (map g L') = zip (fun x y => f x (g y)) L L'.
Proof.
  general induction L; destruct L'; simpl; eauto using f_equal.
Qed.

Lemma zip_ext X Y Z (f f':X -> Y -> Z) L L'
 : (forall x y, f x y = f' x y) -> zip f L L' = zip f' L L'.
Proof.
  general induction L; destruct L'; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma zip_length X Y Z (f:X->Y->Z) L L'
      : length (zip f L L') = min (length L) (length L').
Proof.
  general induction L; destruct L'; simpl; eauto.
Qed.
  


Section ParametricMapIndex.
  Variables X Y : Type.
  Hypothesis f : nat -> X -> Y : Type.

  Fixpoint mapi_impl (n:nat) (L:list X) : list Y :=
    match L with
      | x::L => f n x::mapi_impl (S n) L
      | _ => nil
    end.
  
  Definition mapi := mapi_impl 0.

  Lemma mapi_get_impl L i y n
  : getT (mapi_impl i L) n y -> { x : X & (getT L n x * (f (n+i) x = y))%type }.
  Proof.
    intros. general induction X0; simpl in *; 
            destruct L; simpl in *; inv Heql;
          try now (econstructor; eauto using getT).
    edestruct IHX0; dcr; eauto using getT.
    eexists x1; split; eauto using getT. 
    rewrite <- b. f_equal; omega.
  Qed.

  Lemma mapi_get L n y
  : get (mapi L) n y -> { x : X | get L n x /\ f n x = y }.
  Proof.
    intros. eapply get_getT in H. eapply mapi_get_impl in H; dcr.
    orewrite (n+0 = n) in b.
    eexists; eauto using getT_get.
  Qed.

  Lemma mapi_length L {n}
  : length (mapi_impl n L) = length L.
  Proof.
    general induction L; simpl; eauto using f_equal.
  Qed.

End ParametricMapIndex.

Arguments mapi [X] [Y] f L.
Arguments mapi_impl [X] [Y] f n L.

Lemma map_impl_mapi X Y Z L {n} (f:nat->X->Y) (g:Y->Z)
 : List.map g (mapi_impl f n L) = mapi_impl (fun n x => g (f n x)) n L.
Proof.
  general induction L; simpl; eauto using f_equal.
Qed.


Lemma map_mapi X Y Z L (f:nat->X->Y) (g:Y->Z)
 : List.map g (mapi f L) = mapi (fun n x => g (f n x)) L.
Proof.
  unfold mapi. eapply map_impl_mapi.
Qed.

Lemma mapi_map_ext X Y L (f:nat->X->Y) (g:X->Y) n
 : (forall x n, g x = f n x)
   -> List.map g L = mapi_impl f n L.
Proof.
  intros. general induction L; unfold mapi; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma map_ext_get X Y L (f:X->Y) (g:X->Y)
 : (forall x n, get L n x -> g x = f x)
   -> List.map g L = List.map f L.
Proof.
  intros. general induction L; unfold mapi; simpl; eauto.
  f_equal; eauto using get.
Qed.

Ltac list_eqs :=
  match goal with
    | [ H' : ?x :: ?L = ?L' ++ ?L |- _ ] =>
      rewrite cons_app in H'; eapply app_inv_tail in H'
    | [ H : ?L = ?L' ++ ?L |- _ ] =>
      let A := fresh "A" in
        eapply app_nil_eq in H
    | _ => fail "no matching assumptions"
  end.

Ltac inv_map H :=
  match type of H with
    | get (List.map ?f ?L) ?n ?x =>
      match goal with 
        | [H' : get ?L ?n ?y |- _ ] => 
          let EQ := fresh "EQ" in pose proof (map_get f H' H) as EQ; invc EQ
        | _ => let X := fresh "X" in let EQ := fresh "EQ" in
              pose proof (map_get_4 _ f H) as X; destruct X as [? [? EQ]]; invc EQ
      end
  end.

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)