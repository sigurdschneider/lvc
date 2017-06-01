Require Import Util DecSolve Coq.Classes.RelationClasses.
Require Import Infra.PartialOrder Terminating Option.

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

Instance PartialOrder_option_fstNoneOrR Dom `{PartialOrder Dom}
: PartialOrder (option Dom) := {
  poLe := fstNoneOrR poLe;
  poLe_dec := _;
  poEq := option_R poEq;
  poEq_dec := _;
}.
Proof.
  - intros; inv H0; eauto using fstNoneOrR, poLe_refl.
Defined.

Lemma poLe_opt_inv T H a b
  : @poLe (option T) (@PartialOrder_option_fstNoneOrR T H)
          (@Some T a) (@Some T b)
    -> poLe a b.
Proof.
  inversion 1; eauto.
Qed.

Smpl Add
     match goal with
     | [ H : @poLe (option ?T) (@PartialOrder_option_fstNoneOrR ?T ?H')
                   ?A (@Some ?T ?b) |- _ ] =>
       eapply (@poLe_opt_inv T H') in H
     | [ H : @poLe (option ?T) (@PartialOrder_option_fstNoneOrR ?T ?H')
                   (@Some ?T ?a) None |- _ ] =>
       exfalso; inv H
     | [ H : @poLe (option ?T) (@PartialOrder_option_fstNoneOrR ?T ?H')
                   None _ |- _ ] => clear H
     end : inv_trivial.


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


Lemma poEq_None_inv (T : Type) (H : PartialOrder T) a
  : a ≣ None -> a = None.
Proof.
  intros. invc H0. reflexivity.
Qed.

Smpl Add
     match goal with
     | [ H : ?Y ≣ ⎣⎦ |- _ ] => eapply poEq_None_inv in H; try subst Y
     | [ H : ⎣⎦ ≣ ?Y |- _ ] => symmetry in H; eapply poEq_None_inv in H; try subst Y
     end : inv_trivial.

Lemma poEq_Some_inv (T : Type) (H : PartialOrder T) a b
  : a ≣ Some b -> exists a', a = Some a' /\ poEq a' b.
Proof.
  intros. invc H0. eauto.
Qed.

Smpl Add
     match goal with
     | [ H : ?Y ≣ Some _ |- _ ] => eapply poEq_Some_inv in H;
                                   destruct H as [? [? H]]; try subst Y
     | [ H : Some _ ≣ ?Y |- _ ] => symmetry in H; eapply poEq_Some_inv in H;
                                   destruct H as [? [? H]]; try subst Y
     end : inv_trivial.

Lemma poLe_option_None X `{PartialOrder X} (x:option X)
  :  None ⊑ x.
Proof.
  econstructor.
Qed.

Hint Resolve poLe_option_None.

Lemma poLe_Some_struct A `{PartialOrder A} (a b : A)
  : poLe a b
    -> poLe (Some a) (Some b).
Proof.
  econstructor; eauto.
Qed.

Hint Resolve poLe_Some_struct.