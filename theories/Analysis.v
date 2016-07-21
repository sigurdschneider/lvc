Require Import Util Get Coq.Classes.RelationClasses MoreList.
Require Import SizeInduction Lattice OptionR DecSolve Annotation.

Set Implicit Arguments.

Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Arguments anni0 [A].

Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Definition mapAnni {A B} (f:A -> B) (ai:anni A) : anni B :=
  match ai with
    | anni0 => anni0
    | anni1 a1 => anni1 (f a1)
    | anni2 a1 a2 => anni2 (f a1) (f a2)
    | anni2opt o1 o2 => anni2opt (mapOption f o1) (mapOption f o2)
  end.

Inductive anni_R A B (R : A -> B -> Prop) : anni A -> anni B -> Prop :=
| anni_R0
  : anni_R R anni0 anni0
| anni_R1 a1 a2
  : R a1 a2 -> anni_R R (anni1 a1) (anni1 a2)
| anni_R2 a1 a1' a2 a2'
  : R a1 a2 -> R a1' a2' -> anni_R R (anni2 a1 a1') (anni2 a2 a2')
| anni_R2o o1 o1' o2 o2'
  : option_R R o1 o2 -> option_R R o1' o2' -> anni_R R (anni2opt o1 o1') (anni2opt o2 o2').

Instance anni_R_refl {A} {R} `{Reflexive A R} : Reflexive (anni_R R).
Proof.
  hnf; intros; destruct x; eauto using anni_R, option_R.
  econstructor; reflexivity.
Qed.

Instance anni_R_sym {A} {R} `{Symmetric A R} : Symmetric (anni_R R).
Proof.
  hnf; intros. inv H0; eauto using anni_R.
  econstructor; symmetry; eauto.
Qed.

Instance anni_R_trans A R `{Transitive A R} : Transitive (anni_R R).
Proof.
  hnf; intros ? ? ? B C.
  inv B; inv C; econstructor; eauto.
  - etransitivity; eauto.
  - etransitivity; eauto.
Qed.

Instance anni_R_equivalence A R `{Equivalence A R} : Equivalence (anni_R R).
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Instance anni_R_anti A R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (anni_R Eq) _ (anni_R R).
Proof.
  intros ? ? B C. inv B; inv C; eauto using anni_R.
  econstructor; eapply option_R_anti; eauto.
Qed.

Instance anni_R_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:anni A) (b:anni B) :
  Computable (anni_R R a b).
Proof.
  destruct a,b; try dec_solve.
  - decide (R a1 a0); dec_solve.
  - decide (R a1 a0); decide (R a2 a3); dec_solve.
  - decide (option_R R a1 a0); decide (option_R R a2 a3); dec_solve.
Defined.

Instance PartialOrder_anni Dom `{PartialOrder Dom}
: PartialOrder (anni Dom) := {
  poLe := anni_R poLe;
  poLe_dec := @anni_R_dec _ _ poLe poLe_dec;
  poEq := anni_R poEq;
  poEq_dec := @anni_R_dec _ _ poEq poEq_dec;
}.
Proof.
  - intros. inv H0; eauto 20 using @anni_R, poLe_refl.
    econstructor; eapply (@poLe_refl _ (PartialOrder_option Dom)); eauto.
Defined.


Definition getAnni A (a:A) (an:anni A) :=
  match an with
  | anni1 a => a
  | _ => a
  end.

Lemma poLe_getAnni A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnni a an) (getAnni a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Definition getAnniLeft A (a:A) (an:anni A) :=
  match an with
  | anni2 a _ => a
  | _ => a
  end.

Lemma poLe_getAnniLeft A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniLeft a an) (getAnniLeft a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Definition getAnniRight A (a:A) (an:anni A) :=
  match an with
  | anni2 _ a => a
  | _ => a
  end.

Lemma poLe_getAnniRight A `{PartialOrder A} (a a':A) an an'
  : poLe a a'
    -> poLe an an'
    -> poLe (getAnniRight a an) (getAnniRight a' an').
Proof.
  intros LE LE'; inv LE'; simpl; eauto.
Qed.

Lemma ann_bottom s' (Dom:Type) `{BoundedSemiLattice Dom}
  :  forall (d : ann Dom), annotation s' d -> setAnn bottom s' ⊑ d.
Proof.
  sind s'; destruct s'; simpl; intros d' Ann; inv Ann; simpl; eauto using @ann_R, bottom_least.
  - econstructor; eauto using bottom_least.
    eapply (IH s'); eauto.
  - econstructor; eauto using bottom_least.
    eapply IH; eauto.
    eapply IH; eauto.
  - econstructor. eauto using bottom_least.
    eapply IH; eauto.
  - econstructor; eauto using bottom_least with len.
    + intros; inv_get. eapply IH; eauto.
    + eapply IH; eauto.
Qed.
