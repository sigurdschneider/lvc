Require Import Util DecSolve Coq.Classes.RelationClasses PartialOrder.

Set Implicit Arguments.

Definition sig_R {A} {P:A->Prop} (R:A -> A -> Prop) (a b: { a : A | P a}) :=
  match a, b with
  | exist a _, exist b _ => R a b
  end.

Instance sig_R_refl A (P:A->Prop) R `{Reflexive A R} : Reflexive (@sig_R A P R).
Proof.
  hnf in H.
  hnf; intros [a ?]. hnf. eauto.
Qed.

Instance sig_R_sym A (P:A->Prop) R `{Symmetric A R} : Symmetric (@sig_R A P R).
Proof.
  hnf in H.
  hnf; intros [a ?] [b ?]. eapply H.
Qed.

Instance sig_R_trans A (P:A -> Prop) R `{Transitive A R} : Transitive (@sig_R A P R).
Proof.
  hnf; intros [a ?] [b ?] [c ?]. eapply H.
Qed.

Instance sig_R_Equivalence A (P:A -> Prop) R `{Equivalence A R} : Equivalence (@sig_R A P R).
Proof.
  econstructor.
  - hnf; intros; reflexivity.
  - hnf; intros; symmetry; eauto.
  - hnf; intros; etransitivity; eauto.
Qed.

Instance sig_R_anti A P R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (@sig_R _ P Eq) _ (@sig_R _ P R).
Proof.
  intros [a ?] [b ?] B C; simpl in *. eauto.
Qed.

Instance sig_R_dec A (P:A -> Prop) (R:A->A->Prop)
         `{forall a b, Computable (R a b)} (a b:sig P) :
  Computable (sig_R R a b).
Proof.
  destruct a,b; simpl; eauto.
Defined.

Instance sig_R_proj1_sig A (P:A->Prop) (R:A -> A -> Prop)
  : Proper (@sig_R A P R ==> R) (@proj1_sig A P).
Proof.
  unfold Proper, respectful.
  intros [a ?] [b ?]; simpl; eauto.
Qed.
