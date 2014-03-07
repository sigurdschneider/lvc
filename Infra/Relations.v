Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Util.
Require Export Infra.Option EqDec AutoIndTac Tactics.

Set Implicit Arguments.

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
      intros. general induction H0.
      constructor. assumption.
      econstructor 2; eauto. 
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

    Lemma plus_destr x z
    : plus x z -> exists y, R x y /\ star y z.
    Proof.
      intros. destruct H; exists y; eauto using star, plus, plus_star.
    Qed.

    Lemma star_destr : forall x z, star x z -> (x = z) \/ plus x z.
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
      exists y, inhabited (star x y) /\ normal y.

    Inductive normalizes : X -> Prop :=
    | normalizesI1 x : normal x -> normalizes x
    | normalizesI2 x y : R x y -> normalizes y -> normalizes x.

    Lemma normalizes_normalizes'_agree (x:X) :
      normalizes' x <-> normalizes x.
      split; intros. 
      destruct H as [y [A B]] . destruct A.
      general induction H; eauto 20 using  inhabited, normalizes.
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
      intros y B. exfalso. apply A. now exists y; eauto using inhabited.
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
    intro R. cofix. intros. destruct H0. 
    apply plus_destr in H0. destruct H0 as [x0' [Step SStep]]. 
    destruct H; eapply DivergesI; eauto using star_trans, star_right.
  Qed.

  Lemma div_ext_star : forall (R : rel) (x y : X),  star R x y -> diverges (plus R) y -> diverges (plus R) x.
  Proof.
    intros. induction H; eauto using diverges, star_plus.
  Qed.


  Lemma div_plus : forall (R : rel) (x : X), diverges (plus R) x -> diverges R x.
  Proof.
    intros. eauto using (div_plus' (star_refl R x)).
  Qed.

  Lemma div_ext_star_2 (R: rel) x y
  : functional R -> diverges R x -> star R x y -> diverges R y.
  Proof.
    intros. general induction H1; eauto.
    inv H2. eapply IHstar; eauto. erewrite H0; eauto.
  Qed.
  
  Lemma div_ext_plus (R: rel) x y
  : functional R -> diverges R x -> plus R x y -> diverges R y.
  Proof.
    intros. eapply div_ext_star_2; eauto. eapply plus_star; eauto.
  Qed.
  
  Lemma normal_terminates (R: rel) s
  : normal R s -> terminates R s.
  Proof.
    intros. econstructor; intros. exfalso. firstorder.
  Qed.

  (** Relational approximation *)
  
  Definition rle (R R' : rel) :=
    forall x y, R x y -> R' x y.
  
  Definition req (R R' : rel) :=
    (rle R R' * rle R' R)%type.
  
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


Inductive fstNoneOrR {X Y:Type} (R:X->Y->Prop)
  : option X -> option Y -> Prop :=
| fstNone (x:option Y) : fstNoneOrR R None x
| bothR (x:X) (y:Y) : R x y -> fstNoneOrR R (Some x) (Some y)
.

Instance fstNoneOrR_Reflexive {A : Type} {R : relation A} {Rrefl: Reflexive R} 
: Reflexive (fstNoneOrR R).
Proof.
  hnf; intros. destruct x; econstructor; eauto.
Qed.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
