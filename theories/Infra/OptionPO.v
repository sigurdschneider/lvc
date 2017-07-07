Require Import Util DecSolve Coq.Classes.RelationClasses.
Require Import Infra.PartialOrder Terminating Option OptionR.


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

Smpl Add match goal with
         | [ H : poLe _ None |- _ ] => invc H
         | [ H : ⎣ ?x ⎦ <> ⎣ ?x ⎦ |- _ ] => exfalso; apply H; reflexivity
         end : inv_trivial.
