Require Import OrderedTypeEx Util List Get Computable DecSolve AllInRel Omega.

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

  Lemma zip_tl L L'
    : tl (zip L L') = zip (tl L) (tl L').
  Proof.
    general induction L; destruct L'; simpl; eauto.
    destruct L; simpl; eauto.
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

Lemma zip_length2 {X Y Z} {f:X->Y->Z} DL ZL
: length DL = length ZL
  -> length (zip f DL ZL) = length DL.
Proof.
  intros. rewrite zip_length. rewrite H. rewrite Min.min_idempotent. eauto.
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

Lemma map_ext_get_eq X Y L L' (f:X->Y)
  : (forall x y n, get L n x -> get L' n y -> f x = y)
    -> length L = length L'
    -> List.map f L = L'.
Proof.
  intros GET LEN. length_equify.
  general induction LEN; unfold mapi; simpl; eauto.
  f_equal; eauto using get.
Qed.

Lemma map_ext_get_eq2 X Y L (f:X->Y) (g:X->Y)
 : (forall x n, get L n x -> g x = f x)
   -> List.map g L = List.map f L.
Proof.
  intros. general induction L; unfold mapi; simpl; eauto.
  f_equal; eauto using get.
Qed.

Lemma map_ext_get X Y (R:Y -> Y -> Prop) L (f:X->Y) (g:X->Y)
 : (forall x n, get L n x -> R (g x) (f x))
   -> PIR2 R (List.map g L) (List.map f L).
Proof.
  intros. general induction L; simpl. econstructor.
  econstructor; eauto using get.
Qed.

Lemma mapi_length_ass (X Y : Type) (f : nat -> X -> Y) L k
  : length L = k
    -> length (mapi f L) = k.
Proof.
  intros. subst. eapply mapi_length.
Qed.

Lemma get_mapi_impl X Y L (f:nat->X->Y) n x k
 : get L n x
   -> get (mapi_impl f k L) n (f (n+k) x).
Proof.
  intros. general induction H; simpl; eauto using get.
  econstructor. orewrite (S (n + k) = n + (S k)). eauto.
Qed.

Lemma get_mapi X Y L (f:nat->X->Y) n x
 : get L n x
   -> get (mapi f L) n (f n x).
Proof.
  intros. exploit (get_mapi_impl f 0 H); eauto.
  orewrite (n + 0 = n) in H0. eauto.
Qed.

Hint Resolve mapi_length_ass : len.

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
          let EQ := fresh "EQ" in pose proof (map_get f H' H) as EQ; invcs EQ
        | _ => let X := fresh "X" in let EQ := fresh "EQ" in
              pose proof (map_get_4 _ f H) as X; destruct X as [? [? EQ]]; invcs EQ
      end
  end.

Lemma list_eq_get {X:Type} (L L':list X) eqA n x
  : list_eq eqA L L' -> get L n x -> exists x', get L' n x' /\ eqA x x'.
Proof.
  intros. general induction H.
  inv H0.
  inv H1. eauto using get.
  edestruct IHlist_eq; eauto. firstorder using get.
Qed.

Instance list_R_dec A (R:A->A->Prop)
         `{forall a b, Computable (R a b)} (L:list A) (L':list A) :
  Computable (forall n a b, get L n a -> get L' n b -> R a b).
Proof.
  general induction L; destruct L'.
  + left; isabsurd.
  + left; isabsurd.
  + left; isabsurd.
  + decide (R a a0). edestruct IHL; eauto.
    left. intros. inv H0; inv H1; eauto.
    right. intro. eapply n; intros. eapply H0; eauto using get.
    right. intro. eapply n. eauto using get.
Qed.

Instance list_eq_computable X (R:X -> X-> Prop) `{forall x y, Computable (R x y)}
: forall (L L':list X), Computable (list_eq R L L').
Proof.
  intros. decide (length L = length L').
  - general induction L; destruct L'; isabsurd; try dec_solve.
    decide (R a x); try dec_solve.
    edestruct IHL with (L':=L'); eauto; try dec_solve.
  - right; intro. exploit list_eq_length; eauto.
Qed.


Ltac inv_mapi H :=
  match type of H with
    | get (mapi ?f ?L) ?n ?x =>
      match goal with
        | [H' : get ?L ?n ?y |- _ ] =>
          let EQ := fresh "EQ" in pose proof (mapi_get f H' H) as EQ; invc EQ
        | _ => let X := fresh "X" in let EQ := fresh "EQ" in
              pose proof (mapi_get f _ H) as X; destruct X as [? [? EQ]]; invc EQ;
             clear_trivial_eqs
      end
  end.

Instance list_get_computable X (Y:list X) (R:X->Prop) `{forall (x:X), Computable (R x)}
: Computable (forall n y, get Y n y -> R y).
Proof.
  hnf. general induction Y.
  - left; isabsurd.
  - decide (R a).
    + edestruct IHY; eauto.
      * left; intros. inv H0; eauto using get.
      * right; intros; eauto using get.
    + right; eauto using get.
Defined.

Lemma mapi_get_1 k X Y (L:list X) (f:nat -> X -> Y) n x
: get L n x -> get (mapi_impl f k L) n (f (k+n) x).
Proof.
  intros. general induction H; simpl in *; eauto using get.
  - orewrite (k + 0 = k); eauto using get.
  - orewrite (k + S n = S k + n); eauto using get.
Qed.

Lemma zip_app X Y Z (f : X -> Y -> Z) (xl:list X) (yl:list Y) xl' yl'
: length xl = length yl
  -> zip f (xl ++ xl') (yl ++ yl') = zip f xl yl ++ zip f xl' yl'.
Proof.
  intros. length_equify. general induction H; simpl; f_equal; eauto.
Qed.

Lemma zip_rev X Y Z (f : X -> Y -> Z) (xl:list X) (yl:list Y)
: length xl = length yl
  -> zip f (rev xl) (rev yl) = rev (zip f xl yl).
Proof.
  intros. length_equify. general induction H; simpl; eauto.
  rewrite zip_app.
  - rewrite IHlength_eq; eauto.
  - repeat rewrite rev_length; eauto using length_eq_length.
Qed.


Lemma zip_eq_app_inv X Y Z (f:X->Y->Z) L L' AL DL
: length AL = length DL
  -> L ++ L' = zip f AL DL
  -> exists AL1 AL2 DL1 DL2,
      AL = AL1 ++ AL2 /\ DL = DL1 ++ DL2 /\ L = zip f AL1 DL1 /\ L' = zip f AL2 DL2 /\
      length AL1 = length DL1 /\ length AL2 = length DL2.
Proof.
  intros. general induction L; simpl in *; subst.
  - eexists nil, AL, nil, DL; simpl; intuition.
  - destruct AL, DL; simpl in *; isabsurd. inv H0.
    exploit IHL; try eapply H3. omega. dcr; subst.
    eexists (x::x0), x1, (y::x2), x3; simpl; intuition.
Qed.

Lemma zip_eq_cons_inv X Y Z (f:X->Y->Z) a L L1 L2
:  a :: L = zip f L1 L2
   -> exists b c L1' L2', b::L1'=L1 /\ c::L2'=L2 /\ a = f b c /\ L = zip f L1' L2'.
Proof.
  intros. destruct L1, L2; isabsurd.
  do 4 eexists; intuition; simpl in H; inv H; eauto.
Qed.

Lemma zip_pair_inv X Y (AL1 AL2:list X) (DL1 DL2:list Y)
: length AL1 = length DL1
  -> length AL2 = length DL2
  -> zip pair AL1 DL1 = zip pair AL2 DL2
  -> AL1 = AL2 /\ DL1 = DL2.
Proof.
  intros. length_equify. general induction H; inv H0; simpl in *; isabsurd; eauto.
  - inv H1.
    exploit IHlength_eq; try eapply H5; eauto; dcr; subst; eauto.
Qed.


Lemma zip_pair_app_inv X Y (AL AL1 AL2:list X) (DL DL1 DL2:list Y)
: length AL1 = length DL1
  -> length AL2 = length DL2
  -> length AL = length DL
  -> zip pair AL DL = zip pair (AL1 ++ AL2) (DL1 ++ DL2)
  -> AL = AL1 ++ AL2 /\ DL = DL1 ++ DL2.
Proof.
  intros. length_equify. general induction H1.
  - inv H; inv H0; simpl in *; isabsurd; eauto.
  - inv H; simpl in *; isabsurd.
    + inv H0; simpl in *; isabsurd.
      inv H2. exploit (IHlength_eq nil XL0 nil YL0); eauto. dcr; subst. intuition.
    + inv H2. exploit (IHlength_eq XL0 AL2 YL0 DL2); eauto. dcr; subst. intuition.
Qed.

Ltac inv_zip H :=
  match type of H with
    | get (zip ?f ?L ?L') ?n ?x =>
      match goal with
(*        | [H' : get ?L ?n ?y |- _ ] =>
          let EQ := fresh "EQ" in pose proof (map_get f H' H) as EQ; invc EQ *)
        | _ => let X := fresh "X" in let EQ := fresh "EQ" in
              pose proof (get_zip f _ _ H) as X; destruct X as [? [? [? EQ]]]; invc EQ
      end
  end.


Lemma zip_length_ass (X Y Z : Type) (f : X -> Y -> Z) (L : list X) (L' : list Y) k
  : length L = length L'
    -> k = length L
    -> length (zip f L L') = k.
Proof.
  intros; subst; eauto using zip_length2.
Qed.

Hint Resolve zip_length_ass | 10 : len.

Lemma fold_zip_length_ass (X Y Z : Type) (f : X -> Y -> Y) DL a AP k
  : length AP = length DL
    -> length DL = k
    -> length (fold_left (fun AP0 (z:Z) => zip f DL AP0) a AP) = k.
Proof.
  intros. subst. general induction a; simpl; eauto with len.
  rewrite IHa; eauto with len.
Qed.

Hint Resolve fold_zip_length_ass : len.


Lemma zip_ext_get X Y Z (f f':X -> Y -> Z) L L'
 : (forall x y n, get L n x -> get L' n y -> f x y = f' x y) -> zip f L L' = zip f' L L'.
Proof.
  general induction L; destruct L'; simpl; eauto.
  f_equal; eauto using get.
Qed.

Lemma zip_ext_get2 X1 Y1 X2 Y2 Z (f1:X1 -> Y1 -> Z) (f2:X2 -> Y2 -> Z) L1 L1' L2 L2'
  : length L1 = length L2
    -> length L1' = length L2'
    -> (forall x1 y1 x2 y2 n,
          get L1 n x1 -> get L1' n y1 ->
          get L2 n x2 -> get L2' n y2 ->
          f1 x1 y1 = f2 x2 y2)
    -> zip f1 L1 L1' = zip f2 L2 L2'.
Proof.
  intros LEN1 LEN2 GET. length_equify.
  general induction LEN1; inv LEN2; simpl in * |- *; eauto.
  f_equal; eauto 20 using get.
Qed.

Lemma zip_ext_PIR2 X Y Z (f:X -> Y -> Z) X' Y' Z' (f':X'->Y'->Z') (R:Z->Z'->Prop) L1 L2 L1' L2'
: length L1 = length L2
  -> length L1' = length L2'
  -> length L1 = length L1'
  -> (forall n x y x' y', get L1 n x -> get L2 n y -> get L1' n x' -> get L2' n y' -> R (f x y) (f' x' y'))
  -> PIR2 R (zip f L1 L2) (zip f' L1' L2').
Proof.
  intros A B C.
  length_equify. general induction A; inv B; inv C; simpl; eauto 50 using PIR2, get.
Qed.

Lemma zip_sym X Y Z (f : X -> Y -> Z) (L:list X) (L':list Y)
: length L = length L'
  -> zip f L L' = zip (fun x y => f y x) L' L.
Proof.
  intros. length_equify. general induction H; simpl; eauto.
  f_equal; eauto.
Qed.

Require Import Take Drop.

Lemma take_eta n X (L:list X)
  : L = take n L ++ drop n L.
Proof.
  general induction n; eauto.
  - destruct L; simpl.
    + rewrite drop_nil; eauto.
    + f_equal; eauto.
Qed.

Notation "f ⊜ L1 L2" := (zip f L1 L2) (at level 40, L1 at level 0, L2 at level 0).
