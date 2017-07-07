Require Import Util DecSolve Coq.Classes.RelationClasses.
Require Import Option.

Set Implicit Arguments.

Definition mapOption A B (f:A -> B) (o:option A) : option B :=
  match o with
  | Some a => Some (f a)
  | None => None
  end.

Inductive option_R A B (R: A -> B -> Prop) : option A -> option B -> Prop :=
| option_R_None : option_R R None None
| option_R_Some a b : R a b -> option_R R (Some a) (Some b).

Smpl Add 100
     match goal with
     | [ H : @option_R _ _ _ ?A ?B |- _ ] => inv_if_one_ctor H A B
     end : inv_trivial.

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

Inductive fstNoneOrR (X Y:Type) (R:X->Y->Prop)
  : option X -> option Y -> Prop :=
| fstNone (x:option Y) : fstNoneOrR R None x
| bothR (x:X) (y:Y) : R x y -> fstNoneOrR R (Some x) (Some y)
.

Smpl Add 100
     match goal with
     | [ H : @fstNoneOrR _ _ _ ?A _ |- _ ] =>
       is_constructor_app A; invc H
     end : inv_trivial.

Instance fstNoneOrR_Reflexive {A : Type} {R : relation A} {Rrefl: Reflexive R}
: Reflexive (fstNoneOrR R).
Proof.
  hnf; intros. destruct x; econstructor; eauto.
Qed.

Instance fstNoneOrR_trans A R `{Transitive A R} : Transitive (fstNoneOrR R).
Proof.
  hnf; intros ? ? ? B C.
  inv B; inv C; econstructor; eauto.
Qed.

Instance fstNoneOrR_anti A R Eq `{Equivalence _ Eq}
         `{EqA:Equivalence (option A) (option_R Eq)} `{@Antisymmetric A Eq _ R}
  : @Antisymmetric (option A) _ _ (fstNoneOrR R).
Proof.
  hnf; intros. inv H1; inv H2. reflexivity.
  econstructor. eapply H0; eauto.
Qed.

Instance fstNoneOrR_dec A B (R:A->B->Prop)
         `{forall a b, Computable (R a b)} (a:option A) (b:option B) :
  Computable (fstNoneOrR R a b).
Proof.
  destruct a,b; try dec_solve.
  decide (R a b); dec_solve.
Defined.


Inductive ifFstR {X Y} (R:X -> Y -> Prop) : option X -> Y -> Prop :=
  | IfFstR_None y : ifFstR R None y
  | IfFstR_R x y : R x y -> ifFstR R (Some x) y.

Smpl Add 100
     match goal with
     | [ H : @ifFstR _ _ _ ?A _ |- _ ] =>
       is_constructor_app A; invc H
     end : inv_trivial.


Inductive ifSndR {X Y} (R:X -> Y -> Prop) : X -> option Y -> Prop :=
  | ifsndR_None x : ifSndR R x None
  | ifsndR_R x y : R x y -> ifSndR R x (Some y).

Smpl Add 100
     match goal with
     | [ H : @ifSndR _ _ _ _ ?B |- _ ] =>
       is_constructor_app B; invc H
     end : inv_trivial.
