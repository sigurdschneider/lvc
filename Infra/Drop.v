Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Export Infra.Option EqDec AutoIndTac Util Get.

Set Implicit Arguments.

Fixpoint drop {X} (n : nat) (xs : list X) : list X :=
  match n with
    | 0   => xs
    | S n => drop n (tl xs)
  end.

Fixpoint drop_error {X} (n : nat) (xs : list X) : option (list X) :=
  match n with
    | 0   => Some xs
    | S n => match xs with
               | nil => None
               | _::xs => drop_error n xs
             end
  end.


Lemma drop_get X (L:list X) k n v
  : get L (k+n) v -> get (drop k L) n v.
Proof.
  revert L. induction k; simpl; intros. trivial.
  inv H. eauto.
Qed.

Lemma get_drop_eq X (L L':list X) n x y
  : get L n x -> y::L' = drop n L -> x = y.
Proof.
  intros. revert L' y H0.
  induction H; intros; inv H0; eauto.
Qed.

Lemma drop_get_nil X k n (v:X)
  : get (drop k nil) n v -> False.
Proof.
  induction k. intro H; inv H.
  eauto.
Qed.

Lemma get_drop X (L:list X) k n v
  : get (drop k L) n v -> get L (k+n) v.
Proof.
  revert L. induction k; simpl; intros. trivial.
  destruct L. exfalso; eapply drop_get_nil; eauto.
  constructor. eauto.
Qed.

Lemma length_drop_cons X (L:list X) k a x
  : k <= length L -> length (drop k L) = a -> length (drop k (x::L)) = S a.
Proof.
  revert x L. induction k. simpl. intros. f_equal; eauto.
  simpl; intros. destruct L. simpl in H. inv H.
  eapply IHk. simpl in H. omega. eauto.
Qed.

Lemma length_drop X (L:list X) a
  : a <= length L -> length (drop (length L - a) (L)) = a.
Proof.
  revert a. induction L; intros. inv H. reflexivity.
  destruct a0; simpl in *. clear IHL H. induction L; simpl; eauto.
  eapply length_drop_cons. omega.
  eapply IHL. omega.
Qed.

Lemma drop_nil X k
  : drop k nil = (@nil X).
Proof.
  induction k; eauto.
Qed.

Lemma length_drop_minus X (L:list X) k
  : length (drop k L) = length L - k.
Proof.
  general induction k; simpl; try omega.
  destruct L; simpl. rewrite drop_nil. eauto.
  rewrite IHk; eauto.
Qed.

Lemma drop_app X (L L':list X) n
  : drop (length L + n) (L++L') = drop n L'.
Proof.
  revert n; induction L; intros; simpl; eauto.
Qed.

Lemma drop_tl X (L:list X) n
  : tl (drop n L) = drop n (tl L).
Proof.
  revert L. induction n; intros; simpl; eauto.
Qed.

Lemma drop_drop X (L:list X) n n'
  : drop n (drop n' L) = drop (n+n') L.
Proof.
  revert L. induction n; simpl; intros; eauto.
  rewrite <- IHn. rewrite drop_tl; eauto.
Qed.

(*
Lemma get_split X (L L':list X) x v
  : get (L++L') x v -> get L x v + (x >= length L  get L' (x - length L) v).
Proof.
  intros. revert x L' H. induction L; intros; simpl in *. right. rewrite <- minus_n_O; split; eauto; omega.
  simpl in *. inv H. left. constructor. edestruct IHL. eauto. left. constructor. assumption.
  right. split. omega. simpl. eapply H0.
Qed.
*)

Lemma drop_swap X m n (L:list X)
  : drop m (drop n L) = drop n (drop m L).
Proof.
  revert n L; induction m; intros; simpl; eauto.
  rewrite drop_tl. eauto.
Qed.


Lemma drop_nth X k L (x:X) L' d
  : drop k L = x::L' -> nth k L d = x.
Proof.
  revert x L L'; induction k; intros; simpl in * |- *; subst; eauto.
  destruct L. simpl in H. rewrite drop_nil in H. inv H.
  simpl in *. eauto.
Qed.


Lemma drop_map X Y (L:list X) n (f:X -> Y)
  : List.map f (drop n L) = drop n (List.map f L).
Proof.
  general induction n; simpl; eauto.
  rewrite IHn; f_equal; eauto using tl_map.
Qed.

Lemma drop_length_eq X (L L' :list X)
: drop (length L') (L' ++ L) = L.
Proof.
  general induction L'; simpl; eauto.
Qed.

Lemma drop_length X (L L' :list X) n
: n < length L' -> drop n (L' ++ L) = (drop n L' ++ L)%list.
Proof.
  intros. general induction L'; simpl in *; eauto. omega.
  destruct n; simpl; f_equal. eapply IHL'; omega.
Qed.

Lemma drop_length_gr X (L L' :list X) n x
: n > length L' -> drop n (L' ++ x::L) = (drop (n - S(length L')) L)%list.
Proof.
  intros. general induction L'; simpl.
  destruct n. inv H. simpl. f_equal; omega.
  destruct n. inv H.
  simpl. eapply IHL'. simpl in *; omega.
Qed.

Lemma drop_eq X (L L':list X) n y
: y::L' = drop n L -> get L n y.
Proof.
  intros. general induction n; simpl in *.
  + inv H; eauto using get.
  + destruct L.
  - simpl in H. rewrite drop_nil in H. inv H.
  - econstructor; eauto.
Qed.

Lemma drop_shift_1 X (L:list X) y YL i
: y :: YL = drop i L
  -> YL = drop (S i) L.
Proof.
  general induction i; simpl in *.
  - inv H; eauto.
  - destruct L; simpl in *; eauto.
    + rewrite drop_nil in H; inv H.
Qed.

Lemma drop_length_stable X Y (L:list X) (L':list Y) i
: length L = length L'
  -> length (drop i L) = length (drop i L').
Proof.
  general induction i; simpl; eauto. erewrite IHi; eauto.
  destruct L,L'; try inv H; eauto.
Qed.


Lemma get_eq_drop X (L :list X) n x
: get L n x -> x::drop (S n) L = drop n L.
Proof.
  intros. general induction H; simpl; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
