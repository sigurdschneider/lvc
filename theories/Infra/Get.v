Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Import Infra.Option EqDec AutoIndTac Util LengthEq.

Set Implicit Arguments.

(** * Positional membership in a list *)

Inductive getT (X:Type) : list X -> nat -> X -> Type :=
| getTLB xl x : getT (x::xl) 0 x
| getTLS n xl x x' : getT xl n x -> getT (x'::xl) (S n) x.

Inductive get (X:Type) : list X -> nat -> X -> Prop :=
| getLB xl x : get (x::xl) 0 x
| getLS n xl x x' : get xl n x -> get (x'::xl) (S n) x.


Ltac isabsurd :=
  try match goal with
  | [ H : ?x = None, H' : ?x = Some _ |- _ ] => exfalso; rewrite H in H'; inv H'
  | [ H : get ?L ?n _, H' : (forall _, get ?L ?n _ -> False) |- _ ] => exfalso; eapply H'; eapply H
  | [ H : get nil _ _ |- _ ] => exfalso; inv H
(*  | [ H : _ < _ |- _ ] => try now exfalso; inv H *)
  | _ =>
    try now (hnf; intros;
              match goal with
                [ H : _ |- _ ] => exfalso; inversion H; try subst; simpl in *; try congruence
              end)
  end.

(** Get is informative anyway. *)

Lemma get_getT X (x:X) n L
  : get L n x -> getT L n x.
Proof.
  revert n x L. fix 1; intros.
  destruct n, L. exfalso. inv H.
  assert (x0 = x). inv H; eauto. subst. econstructor.
  exfalso. inv H.
  econstructor. eapply get_getT. inv H. eauto.
Qed.

Lemma getT_get X (x:X) n L
  : getT L n x -> get L n x.
Proof.
  intros. general induction X0; eauto using get.
Qed.


(** * Properties of get *)

Lemma get_functional X (xl:list X) n (x x':X) :
  get xl n x -> get xl n x' -> x = x'.
Proof.
  induction 1; inversion 1; subst; eauto.
Qed.

Lemma get_shift X (L:list X) k L1 blk :
  get L k blk -> get (L1 ++ L) (length L1+k) blk.
Proof.
  intros. induction L1; simpl; eauto using get.
Qed.

Lemma shift_get X (L:list X) k L1 blk :
  get (L1 ++ L) (length L1+k) blk -> get L k blk.
Proof.
  intros. induction L1; simpl; eauto using get. eapply IHL1. simpl in H. inv H. eauto.
Qed.

Lemma get_app X (L L':list X) k x
  : get L k x -> get (L ++ L') k x.
Proof.
  revert k. induction L. inversion 1.
  intros; simpl; inv H; eauto using get.
Qed.

Lemma get_nth_default {X:Type} L n m (default:X):
get L n m -> nth n L default = m.
induction 1; auto. Qed.

Lemma get_length {X:Type} L n (s:X)
(getl : get L n s) :
n < length L.
induction getl; simpl; omega.
Qed.

Lemma get_nth X L n m (d:X) :
get L n m -> nth n L d = m.
induction 1; auto. Qed.

Lemma nth_default_nil X (v : X) x : nth_default v nil x = v.
Proof.
  destruct x; reflexivity.
Qed.

Lemma get_nth_error X (L : list X) k x :
  get L k x -> nth_error L k = Some x.
Proof.
  induction 1; auto.
Qed.

Lemma nth_error_nth X (L:list X) d x n
  : nth_error L n = Some x -> nth n L d = x.
Proof.
  revert x n. induction L; intros. destruct n; inv H.
  destruct n; simpl in *. inv H; eauto.
  eauto.
Qed.

Lemma nth_get {X:Type} L n s {default:X}
(lt : n < length L)
(nthL : nth n L default = s):
get L n s.
Proof.
revert n s default lt nthL. induction L; intros.
 exfalso; inv lt.
 destruct n.
  subst. simpl. constructor.
 constructor. eapply IHL; auto.
  simpl in lt. omega.
  simpl in nthL. eauto.
Qed.

Lemma nth_get_neq {X:Type} L n s {default:X}
(neq:s <> default)
(nthL : nth n L default = s):
get L n s.
Proof.
revert n s default neq nthL. induction L; intros.
 simpl in nthL; destruct n; congruence.
 destruct n.
  subst. simpl. constructor.
 constructor. eapply IHL; auto.
  eassumption.
  simpl in nthL. eauto.
Qed.


Lemma nth_error_get X (L : list X) k x :
  nth_error L k = Some x -> get L k x.
Proof.
  revert k; induction L; destruct k; simpl; intros; try discriminate.
    injection H. intros. subst. econstructor.
    constructor. apply IHL; auto.
Qed.

Lemma nth_error_app X (L L':list X) k x
 : nth_error L k = Some x -> nth_error (L++L') k = Some x.
Proof.
  revert k; induction L; simpl; intros k A. destruct k; inversion A.
  destruct k; simpl; eauto.
Qed.

Lemma nth_error_shift X (L L':list X) x
  : nth_error (L++(x::L')) (length L) = Some x.
Proof.
  induction L; simpl; eauto.
Qed.

Lemma nth_app_shift X (L L':list X) x d
  : x < length L -> nth x (L++L') d = nth x L d.
Proof.
  revert x. induction L; intros. inv H.
  destruct x. reflexivity.
  simpl in *. eapply IHL; eauto; omega.
Qed.

Ltac get_functional :=
  match goal with
  | [ H : get ?XL ?n ?x, H' : get ?XL ?n ?y |- _ ] =>
    let EQ := fresh "EQ" in
    pose proof (get_functional H H') as EQ;
    first [ is_var y; subst y; clear H'
          | is_var x; subst x; clear H'
          | simplify_eq EQ; intros; clear H'; clear_trivial_eqs ]
  | _ => fail "no matching get assumptions"
  end.

Ltac eval_nth_get :=
  match goal with
    | [ H : get ?XL ?n _ |- (bind (nth_error ?XL ?n) _) = _ ] =>
        rewrite (get_nth_error H); simpl
    | _ => fail "no matching get assumptions"
  end.

Lemma get_dec {X} (L:list X) n
      : { x | get L n x } + { forall x, get L n x -> False }.
Proof.
  case_eq (nth_error L n); intros. eapply nth_error_get in H.
  left; eauto.
  right; intros. eapply get_nth_error in H0. congruence.
Defined.

Create HintDb get.
Hint Constructors get       : get.
Hint Resolve get_functional : get.
Hint Resolve get_shift      : get.
Hint Resolve nth_error_get  : get.

Ltac simplify_get := try repeat get_functional; repeat eval_nth_get; eauto with get.


Lemma nth_shift X x (L L':list X) d
  : nth (length L+x) (L++L') d = nth x L' d.
Proof.
  induction L; intros; simpl; eauto.
Qed.


Lemma get_range X (L:list X) n v
  : get L n v -> n < length L.
Proof.
  revert n. induction L; intros. inv H.
  simpl. destruct n. omega.
  inv H.
  pose proof (IHL n H4). omega.
Qed.


Hint Resolve get_range : len.


Lemma get_in_range X (L:list X) n
  : n < length L -> { x:X & get L n x }.
Proof.
  general induction n; destruct L; try now(simpl in *; exfalso; omega).
  eauto using get.
  edestruct IHn. instantiate (1:=L). simpl in *; omega.
  eauto using get.
Qed.

Lemma nth_in X L x (d:X)
  : x < length L -> In (nth x L d) L.
Proof.
  revert x. induction L; intros. inv H.
  destruct x; simpl. eauto.
  right. apply IHL. simpl in *. omega.
Qed.

(** In and get *)

Lemma in_get X `{EqDec X eq} (xl : list X) (x : X) :
  In x xl -> { n : nat & get xl n x }.
Proof.
  induction xl; simpl; intros. inv H0.
  decide (x=a); subst.
  exists 0. constructor.
  edestruct (IHxl). destruct H0; eauto; congruence.
  exists (S x0). constructor. assumption.
Qed.

Lemma get_in X `{EqDec X eq} (xl : list X) (x : X) n :
  get xl n x -> In x xl.
Proof.
  revert n. induction xl; simpl; intros; inv H0; firstorder.
Qed.


(** Some helpful tactics *)


Lemma list_map_eq X Y Z (f:X->Z) g (L:list X) (L':list Y) n x
  : List.map f L = List.map g L'
    -> get L n x -> exists y, get L' n y /\ f x = g y.
Proof.
  intros. general induction H0; simpl in *.
  destruct L'; inv H. eexists y; eauto using get.
  destruct L'; inv H.
  edestruct IHget; eauto; dcr.
  eexists x0; split; eauto using get.
Qed.

Lemma map_get_1 X Y (L:list X) (f:X -> Y) n x
  : get L n x -> get (List.map f L) n (f x).
Proof.
  intros. general induction H; simpl in *; eauto using get.
Qed.

Hint Resolve map_get_1.

Lemma map_get_eq X Y (L:list X) (f:X -> Y) n x y
  : get L n x -> f x = y -> get (List.map f L) n y.
Proof.
  intros. general induction H; simpl in *; eauto using get.
Qed.

Lemma map_get_2 X Y (L:list X) (f:X -> Y) n x
  : get (List.map f L) n x -> exists x' : X, get L n x'.
Proof.
  intros. general induction H; simpl in *;
          destruct L; simpl in *; inv Heql; try now (econstructor; eauto using get).
  edestruct IHget; eauto using get.
Qed.

Lemma map_get_3 X Y (L:list X) (f:X -> Y) n x
  : getT (List.map f L) n x -> { x' : X & (getT L n x' * (f x' = x))%type }.
Proof.
  intros. general induction X0; simpl in *;
          destruct L; simpl in *; inv Heql;
          try now (econstructor; eauto using getT).
  edestruct IHX0; dcr; eauto using getT.
Qed.

Lemma map_get_4 X Y (L:list X) (f:X -> Y) n x
  : get (List.map f L) n x -> { x' : X | get L n x' /\ f x' = x }.
Proof.
  intros. eapply get_getT in H. eapply map_get_3 in H; dcr.
  eexists; eauto using getT_get.
Qed.


Lemma map_get X Y (L:list X) (f:X -> Y) n blk Z
  : get L n blk
  -> get (List.map f L) n Z
  -> Z = f blk.
Proof.
  intros. general induction H; simpl in *; inv H0; eauto.
Qed.


Lemma get_length_eq X Y (L:list X) (L':list Y) n x
  : get L n x -> length L = length L' -> exists y, get L' n y.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; inv H; eauto using get.
  edestruct IHlength_eq; eauto using get.
Qed.

Require Compare_dec.

Lemma get_in_range_app X L L' n (x:X)
  : n < length L -> get (L ++ L') n x -> get L n x.
Proof.
  intros. general induction L; simpl in *; eauto; try omega.
  inv H0; eauto using get. econstructor. eapply IHL; eauto. omega.
Qed.

Lemma get_subst X (L L':list X) x x' n
  : get (L ++ x :: L') n x'
    -> get L n x'
       \/ (x = x' /\ n = length L)
       \/ (get L' (n - S (length L)) x' /\ n > length L).
Proof.
  destruct (Compare_dec.lt_eq_lt_dec n (length L)) as [ [A|A] | A]; intros.
  left. eapply get_in_range_app; eauto.
  right. left. orewrite (n = length L + 0) in H.
  eapply shift_get in H. inv H; eauto.
  right. right. split; try omega.
  orewrite (n = (length L + S (n - S (length L)))) in H.
  eapply shift_get in H. inv H. eauto.
Qed.

Lemma get_app_cases X (L L':list X) x' n
  : get (L ++ L') n x'
    -> get L n x'
       \/ (get L' (n - length L) x' /\ n >= length L).
Proof.
  destruct (Compare_dec.le_lt_dec (S n) (length L)) as [ A | A]; intros.
  left. eapply get_in_range_app; eauto.
  right. split; try omega.
  orewrite (n = (length L + (n - length L))) in H.
  eapply shift_get in H. eauto.
Qed.

Lemma get_app_right X  (L L':list X) n n' x
  : n' = (length L' + n) -> get L n x -> get (L' ++ L) n' x.
Proof.
  intros; subst. eapply get_shift; eauto.
Qed.


Lemma get_length_app X (L L':list X) x
  : get (L ++ x :: L') (length L) x.
Proof.
  orewrite (length L = length L + 0). eapply get_shift. constructor.
Qed.

Lemma get_length_app_eq X (L L':list X) x y l
  : l = length L -> get (L ++ x :: L') l y -> x = y.
Proof.
  orewrite (length L = length L + 0). intros; subst.
  eapply shift_get in H0. inv H0. eauto.
Qed.

Lemma get_app_lt X (L L':list X) n x (LE:n < length L)
  : get (L ++ L') n x <-> get L n x.
Proof.
  revert L L' x LE.
  induction n; intros.
  - split; intros H; inv H.
    + destruct L; isabsurd.
      injection H1; intros; subst. eauto using get.
    + econstructor.
  - split; intros H; inv H.
    + destruct L; isabsurd. injection H0; intros; subst.
      econstructor. eapply IHn; eauto. simpl in *. omega.
    + simpl. econstructor. eapply IHn; eauto. simpl in *; omega.
Qed.

Lemma get_app_lt_1 X (L L':list X) n x (LE:n < length L)
  : get (L ++ L') n x -> get L n x.
Proof.
  eapply get_app_lt; eauto.
Qed.

Lemma get_app_ge X (L L':list X) n x (LE:length L <= n)
  : get (L ++ L') n x <-> get L' (n - length L) x.
Proof.
  revert n L' x LE.
  induction L; intros; simpl in *.
  - orewrite (n - 0 = n). reflexivity.
  - destruct n; [ exfalso; omega|]; simpl.
    rewrite <- (IHL n L' x); try omega.
    split; intros; [ inv H|]; eauto using get.
Qed.

Lemma tl_map X Y L (f:X -> Y)
  : List.map f (tl L) = tl (List.map f L).
Proof.
  general induction L; simpl; eauto.
Qed.

(** Some further helpful lemmata *)
Lemma nth_error_default {X:Type} v E a (x : X) : Some v = nth_error E a -> v = nth_default x E a.
Proof.
intros. revert a H. induction E; intros a' H. destruct a'; inv H.
destruct a'. simpl in H. invc H. reflexivity.
simpl in H. specialize (IHE _ H). subst. reflexivity.
Qed.


Lemma get_rev X (L:list X) n x
: get (rev L) n x ->
  get L (length L - S n) x.
Proof.
  intros.
  general induction L; simpl in *; isabsurd.
  edestruct get_app_cases; eauto; dcr.
  - exploit @get_length; eauto.
    rewrite rev_length in H1; simpl in *.
    orewrite (length L - n = S (length L - S n)).
    eauto using get.
  - rewrite rev_length in H2. orewrite (length L - n = 0).
    inv H1; isabsurd; eauto using get.
Qed.

Lemma get_app_right_ge X L L' n (x:X)
  : n >= length L -> get (L ++ L') n x -> get L' (n - length L) x.
Proof.
  intros. general induction L; simpl in *; eauto; try omega.
  - orewrite (n - 0 = n); eauto.
  - inv H0; simpl.
    + exfalso; omega.
    + eapply IHL; eauto. omega.
Qed.

Lemma get_length_right A (L1 L2:list A) n (x y:A)
  : n > length L1
    -> get (L1 ++ x :: L2) n y
    -> get L2 (n - S (length L1)) y.
Proof.
  intros. general induction L1.
  - simpl in *. inv H0; try omega; simpl.
    orewrite (n0 - 0 = n0); eauto.
  - simpl in *. inv H0. omega. simpl in *.
    eapply IHL1; eauto. omega.
Qed.

Hint Extern 5 =>
match goal with
| [ H : ❬?A❭ = ❬?B❭, H' : ❬?C❭ = ❬?B❭, H'' : get ?A ?n _  |- ?n < ❬?C❭]
  => rewrite H'; rewrite <- H; eapply (get_range H'')
end : len.
