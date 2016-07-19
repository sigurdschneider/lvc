(** * Wrapper for decidable equalities in coq.

   The actual infrarstructure for equivalence relations is already implemented
   in coq. In this file we simply lift it to instances of Computable/Decidable,
   to make the features from Computable available for equalities.
   In particular this allows you to write if [x = y] then ... and use classical
   reasoning in proofs. *)

Require Export Coq.Classes.EquivDec.
Require Export Computable.
Require Import Option AutoIndTac.

Global Instance inst_equiv_cm A R `(EqDec A R) (x y : A) :
  Computable (x === y).
Proof.
  eapply H.
Defined.

Global Instance inst_eq_cm A `(EqDec A eq) (x y : A) : Computable (x = y)
  := H x y.

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

Extraction Inline sumbool_bool.


Coercion sumbool_option {P:Prop} : {P}+{~P} -> option P.
destruct 1. eapply (Some p). eapply None.
Defined.

Extraction Inline sumbool_option.

Lemma sumbool_inversion {P:Prop} (p:{P}+{~P}) x
  : sumbool_option p = Some x -> p = left x.
Proof.
  intros. destruct p; simpl in * |- *; congruence.
Qed.

Coercion sum_option {T:Type} : (T+(T -> False)) -> option T.
destruct 1. eapply (Some t). eapply None.
Defined.


Lemma not_Is_true_eq_false : forall x:bool, ~ Is_true x -> x = false.
  intros [] A; firstorder.
Qed.

Tactic Notation "cases" "in" hyp(H) :=
  match type of H with
  | context [if sumbool_bool ?P then _ else _] => destruct P
  | context [if ?P then _ else _ ] =>
    match goal with
    |  [ H' : Is_true (P) |- _ ] => rewrite (Is_true_eq_true _ H') in H
    | [ H' : ~ Is_true (P) |- _ ] => rewrite (not_Is_true_eq_false _ H') in H
    end
  | context [ match (if ?P then _ else _) with _ => _ end ] =>
    match P with
    | decision_procedure _ =>
      let EQ := fresh "COND" in
      let NEQ := fresh "NOTCOND" in
      destruct P as [EQ|NEQ]; [ clear_trivial_eqs | try solve [exfalso; eauto] ]
    | _ =>
      let EQ := fresh "Heq" in
      let b := fresh "b" in
      remember P as b eqn:EQ; destruct b
    end
  | context [if ?P then _ else _] =>
    match P with
    | decision_procedure _ =>
      let EQ := fresh "COND" in
      let NEQ := fresh "NOTCOND" in
      destruct P as [EQ|NEQ]; [ clear_trivial_eqs | try solve [exfalso; eauto] ]
    | _ =>
      let EQ := fresh "Heq" in
      let b := fresh "b" in
      remember P as b eqn:EQ; destruct b
    end
  end.

Notation "B[ x ]" := (if [ x ] then true else false).

Tactic Notation "cases" :=
  match goal with
  | |- context [if sumbool_bool ?P then _ else _] => destruct P
  | |- context [ match (if ?P then true else false) with _ => _ end ] => destruct P
  | [ H' : Is_true (?P) |- context [if ?P then _ else _] ] =>
    rewrite (Is_true_eq_true _ H')
  | [ H' : ~ Is_true (?P) |- context [if ?P then _ else _] ] =>
    rewrite (not_Is_true_eq_false _ H')
  | |- context [ if ?P then _ else _ ] =>
    match P with
    | negb (?P':decision_procedure _) =>
      let EQ := fresh "COND" in
      let NEQ := fresh "NOTCOND" in
      destruct P' as [EQ|NEQ]; [ clear_trivial_eqs | try solve [exfalso; eauto] ]
    | decision_procedure _ =>
      let EQ := fresh "COND" in
      let NEQ := fresh "NOTCOND" in
      destruct P as [EQ|NEQ]; [ clear_trivial_eqs | try solve [exfalso; eauto] ]
    end
  | |- context [ match ?P with _ => _ end ] =>
    let EQ := fresh "Heq" in
    let b := fresh "b" in
    remember P as b eqn:EQ; destruct b
  end.

Extraction Inline sum_option.

Notation "'mdo' X <= A ; B" := (bind (sumbool_option (@decision_procedure A _)) (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200).


Lemma equiv_dec_refl A `(EqDec A eq) (a:A)
  : equiv_dec a a.
Proof.
  cbv. destruct H; eauto.
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
eapply In_dec. eapply equiv_dec.
Defined.

Lemma dneg_eq A `(EqDec A eq) (a b:A)
  : (~ a <> b) -> a = b.
Proof.
  intros. decide (a=b); firstorder.
Qed.

Global Instance inst_eq_dec_list {A} `{EqDec A eq} : EqDec (list A) eq.
hnf. eapply list_eq_dec. eapply equiv_dec.
Defined.
