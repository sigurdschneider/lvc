Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined.

Set Implicit Arguments.


Inductive ann_P
           (A : Type)
           (P : A -> Prop)
  : ann A -> Prop
  :=
  | annP0
      (a : A)
    : P a
      -> ann_P P (ann0 a)
  | annP1
      (a : A)
      (an : ann A)
    : P a
      -> ann_P P an
      -> ann_P P (ann1 a an)
  | annP2
      (a : A)
      (an1 an2 : ann A)
    : P a
      -> ann_P P an1
      -> ann_P P an2
      -> ann_P P (ann2 a an1 an2)
  | ann_PF
      (a : A)
      (anF : list (ann A))
      (an2 : ann A)
    : P a
      -> (forall (an1 : ann A) n,
             get anF n an1
             -> ann_P P an1)
      -> ann_P P an2
      -> ann_P P (annF a anF an2)
.



Lemma ann_P_get
      (A : Type)
      (P : A -> Prop)
      (a : ann A)
  :
    ann_P P a -> P (getAnn a)
.
Proof.
  intro annP.
  induction annP; eauto.
Qed.

Instance ann_P_impl A
  : Proper (@pointwise_relation _ _ impl ==> eq ==> impl) (@ann_P A).
Proof.
  unfold Proper, respectful, impl; intros; subst.
  general induction H1; eauto using ann_P.
Qed.

Instance ann_P_iff A
  : Proper (@pointwise_relation _ _ iff ==> eq ==> iff) (@ann_P A).
Proof.
  unfold Proper, respectful, impl; intros; subst; split; intros.
  eapply ann_P_impl; eauto.
  eapply pointwise_subrelation; eauto using iff_impl_subrelation.
  eapply ann_P_impl; eauto.
  eapply pointwise_subrelation; eauto using iff_impl_subrelation.
  eapply pointwise_symmetric; eauto using CRelationClasses.iff_Symmetric.
Qed.
