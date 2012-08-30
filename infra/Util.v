Require Import Arith Coq.Lists.List.
Require Export Option EqDec AutoIndTac.

Set Implicit Arguments.

Tactic Notation "inv" hyp(A) := inversion A ; subst.
Tactic Notation "invc" hyp(A) := inversion A ; subst ; clear A.

(** * Relations *)
(** The development in this file are based on the material of the Semantics lecture 2011 at Saarland University. *)

Section Relations.
  Variable X:Type.

  Definition rel : Type := X -> X -> Prop.

  (** ** Unary functions and predicates on relations *)
  Section Unary.
    Variable R : rel.

    Definition reflexive :=
      forall x, R x x.

    Definition symmetric :=
      forall x y, R x y -> R y x.

    Definition transitive :=
      forall x y z, R x y -> R y z -> R x z.

    Definition functional :=
      forall x y z, R x y -> R x z -> y=z.

    Definition reducible (x : X) :=
      exists y, R x y.

    Definition normal (x : X) :=
      ~ reducible x.

    Definition total :=
      forall x, reducible x.

    Hint Unfold symmetric transitive functional reducible normal total. 

    (** *** The transitive reflexive closure of a relation *)

    Inductive star : rel  := 
    | star_refl : forall x, star x x
    | S_star    : forall y x z, R x y -> star y z -> star x z.

    CoInductive diverges : X -> Prop :=
    | DivergesI x y : R x y -> diverges y -> diverges x.

    Lemma star_trans (x y z:X) 
      : star x y -> star y z -> star x z.
      intros A. revert z. induction A; eauto using star.
    Qed.
    
    Lemma star_right (x y z:X) 
      : star x y -> R y z -> star x z.
    Proof. 
      intros A B. induction A ; eauto using star. 
    Qed.

    (** *** The transitive reflexive closure of a relation with size index *)

    Inductive starn : nat -> X -> X -> Prop :=
    | starn_refl : forall a, starn 0 a a
    | S_starn : forall x y z n, R x y -> starn n y z -> starn (S n) x z.

    Lemma starn_one
      : forall x y, R x y -> starn (S 0) x y.
    Proof.
      intros. eauto using starn.
    Qed.

    Lemma starn_trans n m :
      forall x y, starn n x y -> forall z, starn m y z -> starn (n+m) x z.
    Proof.
      intros. induction H. simpl. assumption.
      econstructor; eauto. 
    Qed.

    Lemma star0_is_eq a b
      : starn 0 a b -> a = b.
      intros. inversion H. reflexivity.
    Qed.

    Lemma starn_iff_star a b
      : star a b <-> exists n, starn n a b.
      split. induction 1. exists 0; constructor.
      destruct IHstar as [n B]. exists (S n). apply (S_starn H B).
      intros [n B]. induction B. constructor. apply (S_star H IHB).
    Qed.

    (** ** The transitive closure of a relation. *)
    Inductive plus : rel :=
    | plusO x y   : R x y -> plus x y
    | plusS x y z : R x y -> plus y z -> plus x z.

    Lemma plus_trans x y z :
      plus x y -> plus y z -> plus x z.
    Proof.
      intros A B. induction A; eauto using plus.
    Qed.

    Lemma star_plus x y z:
      R x y -> star y z -> plus x z.
    Proof.
      intros. revert x H. induction H0; intros.
      constructor. assumption.
      econstructor 2. apply H1. auto.
    Qed.

    Lemma plus_right x y z :
      plus x y -> R y z -> plus x z.
    Proof.
      intros A B. apply plus_trans with (y:=y); eauto using plus.
    Qed.

    Lemma plus_star x y :
      plus x y -> star x y.
    Proof.
      induction 1; econstructor; try eassumption. constructor.
    Qed.

    Lemma star_plus_plus : forall x y z, star x y -> plus y z -> plus x z.
    Proof.
      intros. induction H; eauto using star, plus.
    Qed.

    Lemma plus_destr : forall x z, plus x z -> exists y, R x y /\ star y z.
    Proof.
      intros. destruct H; exists y; eauto using star, plus, plus_star.
    Qed.

    Lemma star_destr : forall x z, star x z -> x = z \/ plus x z.
    Proof.
      intros. destruct H. left; eauto. right; eauto using star_plus.
    Qed.

    (** *** Termination and Normalization *)
    (** Also know as must-termination and may-termination *)

    Inductive terminates : X -> Prop :=
    | terminatesI x : (forall y, R x y -> terminates y) -> terminates x.
    
    Definition terminating : Prop :=
      forall x, terminates x.

    Definition normalizes' (x:X) : Prop :=
      exists y, star x y /\ normal y.

    Inductive normalizes : X -> Prop :=
    | normalizesI1 x : normal x -> normalizes x
    | normalizesI2 x y : R x y -> normalizes y -> normalizes x.

    Lemma normalizes_normalizes'_agree (x:X) :
      normalizes' x <-> normalizes x.
      split; intros. 
      destruct H as [y [A B]] . revert B. induction A;
      eauto using normalizes.
      induction H. 
      exists x. eauto using star.
      firstorder. exists x0. firstorder using star. 
    Qed.

    Definition normalizing : Prop :=
      forall x, normalizes x.

    Lemma functional_normalizes_terminates x 
      : functional -> normalizes x -> terminates x.
    Proof. 
      intros F N. induction N as [x A|x y A B]; constructor.
      intros y B. exfalso. apply A. now exists y; trivial.
      intros y' C. assert (y=y') by (eapply F; eauto). subst. trivial. 
    Qed.

  End Unary.

  Lemma star_starplus (R : rel) (x y : X)
    : star R x y -> star (plus R) x y. 
  Proof.
    intros. induction H; eauto using star, plus. 
  Qed.  
  
  Lemma star_idem_1 R x y
    : star (star R) x y -> star R x y.
  Proof.
    intros. remember (star R). induction H; subst; eauto using star, star_trans.
  Qed.

  Lemma star_idem_2 R x y
    : star R x y -> star (star R) x y.
  Proof.
    induction 1; eauto using star.
  Qed.



  Lemma div_plus' : forall (R : rel) (x y : X),  star R x y -> diverges (plus R) y -> diverges R x.
  Proof.
    intro R. cofix. intros. destruct H0. apply plus_destr in H0. destruct H0 as [x0' [Step SStep]]. destruct H; eapply DivergesI; eauto using star_trans, star_right.
  Qed.

  Lemma div_ext_star : forall (R : rel) (x y : X),  star R x y -> diverges (plus R) y -> diverges (plus R) x.
  Proof.
    intros. induction H; eauto using diverges, star_plus.
  Qed.


  Lemma div_plus : forall (R : rel) (x : X), diverges (plus R) x -> diverges R x.
  Proof.
    intros. eauto using (div_plus' (star_refl R x)).
  Qed.


  (** Relational approximation *)
  
  Definition rle (R R' : rel) :=
    forall x y, R x y -> R' x y.
  
  Definition req (R R' : rel) :=
    rle R R' /\ rle R' R.
  
  (** Reduction decidability *)
  
  Definition reddec R := 
    forall x, reducible R x \/ normal R x.

End Relations.

Global Hint Unfold symmetric transitive functional reducible normal total.

(** * complete induction and size induction *)

Require Import Omega.

Lemma complete_induction (p : nat -> Prop) (x : nat) 
  : (forall x, (forall y, y<x -> p y) -> p x) -> p x.
Proof. 
  intros A. apply A. induction x; intros y B.
  exfalso ; omega.
  apply A. intros z C. apply IHx. omega. 
Qed.

Lemma gt_terminates 
  : terminating gt.
Proof. 
  intros x. apply complete_induction. clear x.
  intros x A. constructor. exact A. 
Qed.

Lemma size_induction (X : Type) (f : X -> nat) (p: X ->Prop) (x : X) 
  : (forall x, (forall y, f y  < f x -> p y)  -> p x) -> p x.
Proof. 
  intros A. apply A.
  induction (f x); intros y B.
  exfalso; omega.
  apply A. intros z C. apply IHn. omega. 
Qed.

Definition size_recursion (X : Type) (f : X -> nat) (p: X -> Type) (x : X) 
  : (forall x, (forall y, f y  < f x -> p y) -> p x) -> p x.
Proof. 
  intros A. apply A.
  induction (f x); intros y B.
  exfalso; destruct (f y); inv B.
  apply A. intros z C. apply IHn. cbv in B,C. cbv. 
  inv B. assumption. eapply le_S in C. eapply le_trans; eauto.
Defined.

(** * An inductive type for "accessing" the environments *)

Inductive get (X:Type) : list X -> nat -> X -> Type :=
| getLB xl x : get (x::xl) 0 x
| getLS n xl x x' : get xl n x -> get (x'::xl) (S n) x.

(*** properties of get *)
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
  intros. induction L1; simpl; eauto using get. eapply IHL1. simpl in X0. inv X0. eauto.
Qed.

Lemma get_app X (L L':list X) k x
  : get L k x -> get (L ++ L') k x.
Proof.
  revert k. induction L. inversion 1.
  intros; simpl; inv X0; eauto using get.
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
    | [ H : get ?XL ?n _, H' : get ?XL ?n _ |- _ ] =>
      simplify_eq (get_functional H H'); intros; clear H
    | _ => fail "no matching get assumptions"
  end.

Ltac eval_nth_get :=
  match goal with
    | [ H : get ?XL ?n _ |- (bind (nth_error ?XL ?n) _) = _ ] =>
        rewrite (get_nth_error H); simpl
    | _ => fail "no matching get assumptions"
  end.

Create HintDb get.
Hint Constructors get       : get.
Hint Resolve get_functional : get.
Hint Resolve get_shift      : get.
Hint Resolve nth_error_get  : get.

Ltac simplify_get := try repeat get_functional; repeat eval_nth_get; eauto with get.

Class Defaulted (V:Type) := {
  default_el : V
}.

(* Inductive definition of a SubLists relation with explicit position *)

Inductive subList {X : Type} (L : list X) : list X -> nat -> Prop := 
| SubListNil n : subList L nil n 
| SubListCons l L' n : get L n l -> subList L L' (S n) -> subList L (l::L') n.
 
Lemma subList_app_r {X:Type} (P:list X) P1 P2 n:
subList P (P1++P2) n -> subList P P2 (n+length P1).
intros. remember (P1 ++ P2). revert P1 P2 Heql. induction H; intros.
 pose proof (app_eq_nil _ _ (eq_sym Heql)). destruct H. subst. constructor.
 destruct P1. simpl in *. subst. rewrite plus_0_r. constructor; auto.
 simpl in *. rewrite <- plus_Snm_nSm. simpl. eapply IHsubList. congruence.
Qed.
    
Lemma subList_app_l {X:Type} (P:list X) P1 P2 n:
subList P (P1++P2) n -> subList P P1 n.
revert n. induction P1; intros.
  constructor.
  inv H. constructor; auto.
Qed.

Lemma subList_refl' {X:Type} (L1 L2: list X):
subList (L1++L2) L2 (length L1). 
Proof.
 revert L1. induction L2; intros; simpl.
  constructor. 
  pose proof (IHL2 (L1++a:: nil)). 
  rewrite <- app_assoc in H. rewrite app_length in H. 
  rewrite plus_comm in H.  simpl in *.
 constructor; auto. rewrite <- (plus_0_r (length L1)). 
 apply get_shift. constructor.
Qed.

Lemma subList_refl {X:Type} (L: list X) :
subList L L 0.
pose proof (subList_refl' nil L).
simpl in *. auto.
Qed.

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
  inv X0. eauto. 
Qed.

Lemma get_drop_eq X (L L':list X) n x y 
  : get L n x -> y::L' = drop n L -> x = y.
Proof.
  intros. revert L' y H. 
  induction X0; intros; inv H; eauto.
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

Lemma nth_shift X x (L L':list X) d
  : nth (length L+x) (L++L') d = nth x L' d.
Proof.
  induction L; intros; simpl; eauto. 
Qed.


Lemma get_range X (L:list X) n v
  : get L n v -> n < length L.
Proof.
  revert n. induction L; intros. inv X0.
  simpl. destruct n. omega.
  inv X0.
  pose proof (IHL n X1). omega.
Qed.


Lemma get_in_range X (L:list X) n
  : n < length L -> { x:X & get L n x }.
Proof.
  general induction n; destruct L; try now(simpl in *; exfalso; omega). 
  eauto using get.
  edestruct IHn. instantiate (1:=L). simpl in *; omega. 
  eauto using get.
Qed.  

(** Lemmas and tactics for lists *)
Lemma app_nil_eq X (L:list X) xl
  : L = xl ++ L -> xl = nil.
intros. rewrite <- (app_nil_l L ) in H at 1.
eauto using app_inv_tail.
Qed.

Lemma cons_app X (x:X) xl
  : x::xl = (x::nil)++xl.
eauto.
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
  destruct_prop (x=a); subst.
  exists 0. constructor.
  edestruct (IHxl). destruct H0; eauto; congruence. 
  exists (S x0). constructor. assumption.
Qed.

Lemma get_in X `{EqDec X eq} (xl : list X) (x : X) n :
  get xl n x -> In x xl.
Proof.
  revert n. induction xl; simpl; intros; inv X0; firstorder.
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

(** Some helpful tactics *)

Ltac eq e := assert e; eauto; subst; trivial.

Ltac crush := intros; subst; simpl in *; solve [
    eauto
  | contradiction 
  | match goal with [H : ?s |- _] => now(inversion H; eauto) end
  | (constructor; eauto)
  | (constructor 2; eauto)
  | (constructor 3; eauto)
  | intuition
  ].

Tactic Notation "You are here" := fail.

(** Some further helpful lemmata *)
Lemma nth_error_default {X:Type} v E a (x : X) : Some v = nth_error E a -> v = nth_default x E a.
Proof.
intros. revert a H. induction E; intros a' H. destruct a'; inv H.
destruct a'. simpl in H. invc H. reflexivity.
simpl in H. specialize (IHE _ H). subst. reflexivity.
Qed.

Require Export Basics Tactics Morphisms Morphisms_Prop.

Lemma toImpl (A B: Prop) 
  : (A -> B) -> impl A B.
Proof.
  eauto.
Qed.

Ltac bool_to_prop_assumption H :=
  match goal with
    | [ H : context [Is_true (?x && ?y)] |- _ ] 
      => rewrite (toImpl (@andb_prop_elim x y)) in H
    | [ H : context [Is_true (?x || ?y)] |- _ ] 
      => rewrite (toImpl (@orb_prop_elim x y)) in H
    | [ H : context [not (?t)] |- _ ] =>
      match t with
        | context [Is_true (?x && ?y)] =>
          rewrite <- (toImpl (@andb_prop_intro x y)) in H
        | context [Is_true (?x || ?y)] =>
          rewrite <- (toImpl (@orb_prop_intro x y)) in H
        | context [Is_true (negb ?x)] => 
          rewrite <- (toImpl (@negb_prop_intro x)) in H
      end
    | [ H : context [Is_true (negb ?x)] |- _ ] 
      => rewrite (toImpl (@negb_prop_elim x)) in H
    | _ => fail
  end.

Lemma true_prop_intro 
  : Is_true (true) = True.
Proof. 
  eauto.
Qed.

Lemma false_prop_intro 
  : Is_true (false) = False.
Proof. 
  eauto.
Qed.
  
Ltac bool_to_prop_goal :=
  match goal with
   | [ _ : _ |- context [Is_true (?x && ?y)] ] 
     => rewrite <- (toImpl (@andb_prop_intro x y))
   | [ _ : _ |- context [not (Is_true (?x && ?y))] ] 
     => rewrite (toImpl (@andb_prop_elim x y))
   | [ _ : _ |- context [Is_true (?x || ?y)] ]
     => rewrite <- (toImpl (@orb_prop_intro x y))
   | [ _ : _ |- context [not (Is_true (?x || ?y))] ] 
     => rewrite (toImpl (@orb_prop_elim x y))
   | [  _ : _ |- context [Is_true (negb ?x)] ]
     => rewrite <- (toImpl (@negb_prop_intro x))
   | [  _ : _ |- context [Is_true (true)] ]
     => rewrite true_prop_intro
   | [  _ : _ |- context [Is_true (false)] ]
     => rewrite false_prop_intro
   | _ => fail
  end.

Tactic Notation "bool_to_prop" :=
  repeat bool_to_prop_goal.

Tactic Notation "bool_to_prop" "in" hyp (H) :=
  repeat (bool_to_prop_assumption H).

Tactic Notation "bool_to_prop" "in" "*" :=
  repeat (match goal with
    | [ H : _ |- _ ] => bool_to_prop in H
  end).

Ltac isabsurd := 
  try now (hnf; intros; match goal with
                 [ H : _ |- _ ] => exfalso; inversion H
               end).

Ltac destr_assumption H := 
  repeat match goal with
           | [ H : _ /\ _  |- _ ] => destruct H
         end.

Ltac destr :=
  intros; repeat match goal with
                   | |- _ /\ _  => split
                 end.

Tactic Notation "destr" "in" hyp(H) :=
  destr_assumption H.

Tactic Notation "destr" "in" "*" :=
  repeat (match goal with
    | [ H : _ |- _ ] => destr in H
  end).

Tactic Notation "beq_to_prop" :=
  match goal with 
    | [ H : ?Q = true |- Is_true ?Q] => rewrite H; eapply I
    | [ H : Is_true ?Q |- ?Q = true] => destruct Q; try destruct H; reflexivity
    | [ H : Is_true ?Q, H' : ?Q = false |- _ ] => rewrite H' in H; destruct H
    | [ H : Is_true ?Q |- not ((?Q) = false) ] => let X:= fresh "H" in 
      intro X; rewrite X in H; destruct H
    | [ H : ?Q = false |- not (Is_true (?Q)) ] => rewrite H; cbv; trivial
    | [ H : ?Q, H' : not (?Q) |- _ ] => exfalso; apply H'; apply H
    | [ H : not (?Q = false) |- Is_true (?Q) ] => 
      destruct Q; solve [ apply I | exfalso; eapply H; trivial ]
    | |- Is_true true => eapply I
    | [ H : not (Is_true (?Q)) |- ?Q = false ] => 
      destruct Q; solve [ exfalso; eapply H; eapply I | reflexivity ]
  end.


Tactic Notation "cbool" :=
  simpl in *; bool_to_prop in *; destr in *; bool_to_prop; destr; beq_to_prop; isabsurd.

Global Instance inst_eq_dec_list {A} `{EqDec A eq} : EqDec (list A) eq.
hnf. eapply list_eq_dec. eapply equiv_dec.
Defined.

Tactic Notation "orewrite" constr(A) :=
  let X := fresh "OX" in assert A as X by omega; rewrite X; clear X. 

Tactic Notation "orewrite" constr(A) "in" hyp(H) :=
  let X := fresh "OX" in assert A as X by omega; rewrite X in H; clear X. 

Lemma get_app_le X (L L':list X) n x (LE:n < length L)
  : get (L ++ L') n x -> get L n x.
Proof.
  revert L L' x LE. induction n; intros; inv X0;
  destruct L; isabsurd; injection H0; intros; subst. constructor.
  constructor. eapply IHn. simpl in LE; omega. eauto.
Qed.

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

Tactic Notation "simplify" "if" :=
  match goal with
    | [ H : Is_true (?P) |- context [if ?P then _ else _]] => 
      let X := fresh in assert (P = true) as X by cbool; rewrite X; clear X
    | [ H : not (Is_true (?P)) |- context [if ?P then _ else _]] => 
      let X := fresh in assert (P = false) as X by cbool; rewrite X; clear X
  end.

Tactic Notation "simplify" "if" "in" "*" :=
  match goal with 
    | [ H : Is_true (?P), H' : context [if ?P then _ else _] |- _ ] => 
      let X := fresh in assert (P = true) as X by cbool; rewrite X in H'; clear X
    | [ H : not (Is_true (?P)), H' : context [if ?P then _ else _] |- _ ] => 
      let X := fresh in assert (P = false) as X by cbool; rewrite X in H'; clear X
  end.


Lemma bool_extensionality (x y:bool)
  : (x -> y) -> (y -> x) -> x = y.
Proof.
  destruct x,y; intros; eauto. destruct H; eapply I.  destruct H0; eapply I.
Qed.

Ltac eqassumption :=
  match goal with 
    | [ H : ?C ?t |- ?C ?t' ] => 
      let X := fresh in
        cut (C t' = C t); 
          [ rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 |- ?C ?t1' ?t2' ] => 
      let X := fresh in
        cut (C t1' t2' = C t1 t2); 
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 ?t3 |- ?C ?t1' ?t2' ?t3'  ] => 
      let X := fresh in
        cut (C t1' t2' t3' = C t1 t2 t3); 
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
    | [ H : ?C ?t1 ?t2 ?t3 ?t4 |- ?C ?t1' ?t2' ?t3' ?t4' ] => 
      let X := fresh in
        cut (C t1' t2' t3' t4' = C t1 t2 t3 t4); 
          [ intros X; rewrite X; apply H |
            f_equal; try congruence ]
  end.
          
Ltac revert_except E :=
  repeat match goal with
           [H : ?t |- _] =>
           match H with
             | E => fail 1
             | _ => revert H
               end
         end.

Ltac remember_arguments E :=
  let tac x := (try (is_var x; fail 1); remember (x)) in
  repeat (match type of E with
    | ?C ?x _ _ _ _ _ _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ _ => tac x
    | ?C ?x _ _ _ _ => tac x
    | ?C ?x _ _ _ => tac x
    | ?C ?x _ _ => tac x
    | ?C ?x _ => tac x
    | ?C ?x => tac x
  end).

Ltac inv_eqs :=
  progress (match goal with
              | [ H : @eq _ ?x ?x |- _ ] => clear H
              | [ H : @eq _ ?x ?y |- _ ] => inversion H; subst
            end).

Inductive length_eq X Y : list X -> list Y -> Type :=
  | LenEq_nil : length_eq nil nil
  | LenEq_cons x XL y YL : length_eq XL YL -> length_eq (x::XL) (y::YL).


Lemma length_eq_sym X Y (XL:list X) (YL:list Y)
  : length_eq XL YL -> length_eq YL XL.
Proof.
  intros. general induction X0; eauto using length_eq.
Qed.

Lemma length_eq_trans X Y Z (XL:list X) (YL:list Y) (ZL:list Z)
  : length_eq XL YL -> length_eq YL ZL -> length_eq XL ZL.
Proof.
  intros. general induction X0; inv X1; eauto using length_eq.
Qed.

Lemma length_length_eq X Y (L:list X) (L':list Y)
  : length L = length L' -> length_eq L L'.
Proof.
  intros H; general induction L; destruct L'; inv H; eauto using length_eq.
Qed.

Lemma length_eq_length X Y (L:list X) (L':list Y)
  : length_eq L L' -> length L = length L'.
Proof.
  intros H; general induction L; destruct L'; inv H; simpl; eauto.
Qed.
