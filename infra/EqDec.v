(** * Wrapper for decidable equalities in coq.
  
   The actual infrarstructure for equivalence relations is already implemented
   in coq. In this file we simply lift it to instances of Computable/Decidable,
   to make the features from DecidableTactics available for equalities.
   In particular this allows you to write if [x = y] then ... and use classical
   reasoning in proofs. *)

Require Export Coq.Classes.EquivDec.
Require Export DecidableTactics.


Global Instance inst_equiv_cm A R `(EqDec A R) (x y : A) :
  Computable (x === y).
Proof.
  constructor. apply H.
Defined.

Global Instance inst_equiv_xm A R `(DecidableEquivalence A R) (x y : A) :
  Decidable (x === y).
Proof.
  constructor. apply H.
Qed.

Instance inst_eq_cm A `(EqDec A eq) (x y : A) : Computable (x = y)
  := {| compute_prop := H x y |}.

Global Instance inst_eq_xm A `(DecidableEquivalence A eq) (x y : A) :
  Decidable (x = y).
Proof.
  constructor. apply H.
Qed.

(* Additional instances for EqDec. *)
Definition option_eq_dec A `(EqDec A eq) (x y : option A) :
  {x = y} + {x <> y}.
Proof.
  decide equality. apply H.
Defined.

Global Instance inst_eq_dec_option A `(EqDec A eq) : EqDec (option A) eq := {
  equiv_dec := (option_eq_dec A _)
}.

(* For backwards compatibility, eq_dec uses equiv_dec for eq. *)
Definition eq_dec {A : Type} (x y : A) `{@EqDec A eq eq_equivalence} :
  {x = y} + {x <> y}.
Proof.
  apply H.
Defined.

Coercion sumbool_bool {A} {B} (x:{A} + {B}) : bool := if x then true else false.

Lemma equiv_dec_refl A `(EqDec A eq) (a:A)
  : equiv_dec a a.
Proof.
  cbv. destruct H; eauto. eapply c. reflexivity.
Qed.

Lemma equiv_dec_R A eq `(EqDec A eq) (a b:A)
  : equiv_dec a b -> eq a b.
Proof.
  intros. cbv in H0. destruct (H a b); eauto; contradiction.
Qed.

Lemma equiv_dec_R_neg A eq `(EqDec A eq) (a b:A)
  : ~equiv_dec a b -> ~eq a b. 
Proof.
  intros. cbv in H0. destruct (H a b); eauto; contradiction.
Qed.


Lemma equiv_dec_false A `(EqDec A eq) (a b:A)
  : a <> b -> false = equiv_dec a b.
Proof.
  intros. destruct (equiv_dec a b); simpl; congruence. 
Qed.

Lemma false_equiv_dec A `(EqDec A eq) (a b:A)
  : false = equiv_dec a b -> a <> b.
Proof.
  intros. destruct (equiv_dec a b); simpl in *; congruence. 
Qed.

(* The following proof is from http://cstheory.stackexchange.com/questions/5158/prove-proof-irrelevance-in-coq *)

Let nu a b (p:a = b) : a = b :=
  match Bool.bool_dec a b with
    | left eqxy => eqxy
    | right neqxy => False_ind _ (neqxy p)
  end.
Lemma bool_pcanonical : forall (a b : bool) (p : a = b), p = nu a b p.
Proof.
  intros. case p. destruct a,b; (try discriminate p);
  unfold nu; simpl; reflexivity.
Qed.

Section PI.
  Variable X:Type.
  Context `{EqDec X eq}.

  Lemma equiv_dec_PI'
    : forall x, forall (p q :true = equiv_dec x x), p = q.
  Proof.
    intros. rewrite (bool_pcanonical _ _ q). rewrite (bool_pcanonical _ _ p).
    unfold nu. destruct (bool_dec true (equiv_dec x x)).
    reflexivity. congruence.
  Qed.

  Lemma equiv_dec_PI'_false
    : forall x y, forall (p q :false = equiv_dec x y), p = q.
  Proof.
    intros. rewrite (bool_pcanonical _ _ q). rewrite (bool_pcanonical _ _ p).
    unfold nu. destruct (equiv_dec x y); simpl. 
    simpl in p. congruence. reflexivity.
  Qed.

  Lemma equiv_dec_PI
    : forall x, forall (p q :equiv_dec x x), p = q.
  Proof.
    intros x q.
    pose proof (@Is_true_eq_true (equiv_dec x x) q).
    revert q.
    rewrite H0. intros. destruct q. destruct q0. reflexivity.
  Qed.

End PI.

Ltac eqsubst_assumption H :=
  match goal with
    | [ H : _ |- _ ] => eapply equiv_dec_R in H
    | [ H : ~ _ |- _ ] => eapply equiv_dec_R_neg in H
  end.

Tactic Notation "eqsubst" "in" hyp(H) :=
  eqsubst_assumption H.

Tactic Notation "eqsubst" :=
  progress (match goal with
    | [ H : _ |- _ ] => eqsubst_assumption H
  end).

Require Import List.

Global Instance inst_in_cm X (a:X) (L:list X) `(EqDec X eq) : Computable (In a L). 
econstructor. eapply In_dec. eapply equiv_dec.
Defined.
  
Lemma dneg_eq A `(EqDec A eq) (a b:A)
  : (~ a <> b) -> a = b.
Proof.
  intros. destruct_prop (a=b); firstorder.
Qed.

