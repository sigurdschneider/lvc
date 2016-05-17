Require Import Coq.Arith.Lt Coq.Arith.Plus Coq.Classes.RelationClasses List.
Require Import Util Get Drop Take DecSolve.

(** * AllInRel: Inductive characterization of lists which are element-wise in relation *)

Set Implicit Arguments.

Section PIR2.
  Variable X Y : Type.
  Variable R : X -> Y -> Prop.

  Inductive PIR2
    : list X -> list Y -> Prop :=
  | PIR2_nil : PIR2 nil nil
  | PIR2_cons x XL y (pf:R x y)
    (YL:list Y) :
    PIR2 XL YL ->
    PIR2 (x::XL) (y::YL).

  Lemma PIR2_nth (L:list X) (L':list Y) l blk :
    PIR2 L L'
    -> get L l blk
    -> exists blk':Y,
      get L' l blk' /\ R blk blk'.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHPIR2 as [blk' [A B]]; eauto.
    eexists; repeat split; eauto using get.
  Qed.

  Lemma PIR2_nth_2 (L:list X) (L':list Y) l blk :
    PIR2 L L'
    -> get L' l blk
    -> exists blk',
      get L l blk' /\ R blk' blk.
  Proof.
    intros. general induction H; isabsurd.
    inv H0. eexists; eauto using get.
    edestruct IHPIR2 as [blk' [A B]]; eauto.
    eexists; repeat split; eauto using get.
  Qed.


  Lemma PIR2_drop LT L n
    : PIR2 LT L -> PIR2 (drop n LT) (drop n L).
  Proof.
    general induction n; simpl; eauto.
    destruct L; inv H; simpl; auto.
  Qed.

End PIR2.

Lemma PIR2_app X Y (R:X->Y->Prop) L1 L2 L1' L2'
: PIR2 R (L1) (L1')
  -> PIR2 R (L2) (L2')
  -> PIR2 R (L1 ++ L2) (L1' ++ L2').
Proof.
  intros. general induction H; eauto using PIR2.
Qed.

Lemma PIR2_app' X Y (R:X->Y->Prop) L1 L2 L1' L2'
: PIR2 R (L1 ++ L2) (L1' ++ L2')
  -> length L1 = length L1'
  -> PIR2 R (L1) (L1') /\ PIR2 R (L2) (L2').
Proof.
  intros P LEN. length_equify.
  general induction LEN; simpl in *; eauto using PIR2.
  inv P. exploit IHLEN; eauto. eauto using PIR2.
Qed.

Lemma PIR2_get X Y (R:X->Y->Prop) L L'
: (forall n x x', get L n x -> get L' n x' -> R x x')
  -> length L = length L'
  -> PIR2 R L L'.
Proof.
  intros. eapply length_length_eq in H0.
  general induction H0; eauto 20 using PIR2, get.
Qed.


Instance PIR2_refl X (R:X -> X -> Prop) `{Reflexive _ R} : Reflexive (PIR2 R).
Proof.
  hnf; intros. general induction x; eauto using PIR2.
Qed.

Instance PIR2_sym {A} (R : A -> A-> Prop) `{Symmetric _ R} :
  Symmetric (PIR2 R).
Proof.
  intros; hnf; intros. general induction H0.
  - econstructor.
  - econstructor; eauto.
Qed.

Instance PIR2_trans {X} (R:X -> X -> Prop) `{Transitive _ R}
: Transitive (PIR2 R).
Proof.
  hnf; intros.
  general induction H0; simpl in *.
  + inv H1. econstructor.
  + inv H1.
    - econstructor; eauto.
Qed.

Instance PIR2_equivalence {X} (R:X -> X -> Prop) `{Equivalence _ R}
  : Equivalence (PIR2 R).
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Lemma PIR2_length X Y (R:X->Y->Prop) L L'
: PIR2 R L L' -> length L = length L'.
Proof.
  intros. general induction H; simpl; eauto.
Qed.

Instance PIR2_computable X Y (R:X->Y->Prop) `{forall x y, Computable (R x y)}
: forall (L:list X) (L':list Y), Computable (PIR2 R L L').
Proof.
  intros. decide (length L = length L').
  - general induction L; destruct L'; isabsurd; try dec_solve.
    decide (R a y); try dec_solve.
    edestruct IHL with (L':=L'); eauto; subst; try dec_solve.
  - right; intro; subst. exploit PIR2_length; eauto.
Defined.


Lemma PIR2_flip {X} (R:X->X->Prop) l l'
      : PIR2 R l l'
        -> PIR2 (flip R) l' l.
Proof.
  intros. general induction H.
  - econstructor.
  - econstructor; eauto.
Qed.


Lemma PIR2_take X Y (R: X -> Y -> Prop) L L' n
  : PIR2 R L L'
    -> PIR2 R (take n L) (take n L').
Proof.
  intros REL.
  general induction REL; destruct n; simpl; eauto using PIR2.
Qed.

Ltac provide_invariants_P2 :=
match goal with
  | [ H : PIR2 ?R ?A ?B, H' : get ?A ?n ?b |- _ ] =>
    let X := fresh H in
    destruct (PIR2_nth H H') as [? [? X]]; eauto; inv X;
    repeat get_functional; (try subst) ;
    let X'' := fresh H in pose proof (PIR2_drop n H) as X''
end.

Hint Extern 20 (PIR2 _ ?a ?a') => progress (first [has_evar a | has_evar a' | reflexivity]).
