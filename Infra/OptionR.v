Require Import Util DecSolve Coq.Classes.RelationClasses PartialOrder Terminating.

Set Implicit Arguments.

Inductive option_R A B (R: A -> B -> Prop) : option A -> option B -> Prop :=
| option_R_None : option_R R None None
| option_R_Some a b : R a b -> option_R R (Some a) (Some b).

Instance option_R_refl A R `{Reflexive A R} : Reflexive (option_R R).
Proof.
  unfold Reflexive in *; intros []; eauto using option_R.
Qed.

Instance option_R_sym A R `{Symmetric A R} : Symmetric (option_R R).
Proof.
  unfold Symmetric in *; intros; inv H0; eauto using option_R.
Qed.

Instance option_R_trans A R `{Transitive A R} : Transitive (option_R R).
Proof.
  hnf; intros ? ? ? B C.
  inv B; inv C; econstructor; eauto.
Qed.

Instance option_R_equivalence A R `{Equivalence A R} : Equivalence (option_R R).
Proof.
  econstructor; eauto with typeclass_instances.
Qed.

Instance option_R_anti A R Eq `{EqA:Equivalence _ Eq} `{@Antisymmetric A Eq EqA R}
  : @Antisymmetric _ (option_R Eq) (option_R_equivalence _ _) (option_R R).

Proof.
  intros ? ? B C. inv B; inv C; eauto using option_R.
Qed.

Instance option_R_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:option A) (b:option B) :
  Computable (option_R R a b).
Proof.
  destruct a,b; try dec_solve.
  decide (R a b); dec_solve.
Defined.

Instance PartialOrder_option Dom `{PartialOrder Dom}
: PartialOrder (option Dom) := {
  poLe := option_R poLe;
  poLe_dec := @option_R_dec _ _ poLe poLe_dec;
  poEq := option_R poEq;
  poEq_dec := @option_R_dec _ _ poEq poEq_dec;
}.
Proof.
  - intros; inv H0; eauto using option_R, poLe_refl.
Defined.


Instance terminating_option Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> Terminating (option Dom) poLt.
Proof.
  intros. hnf; intros.
  destruct x.
  - specialize (H d).
    general induction H.
    econstructor; intros. inv H1; inv H2.
    eapply H0; eauto using option_R.
    split; eauto. intro. eapply H3; econstructor; eauto.
  - econstructor; intros. inv H0.
    exfalso. inv H1. eapply H2; reflexivity.
Qed.
