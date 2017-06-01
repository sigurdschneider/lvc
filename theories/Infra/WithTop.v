Require Import Util MapBasics Infra.Lattice Infra.PartialOrder DecSolve .

Set Implicit Arguments.

Inductive withTop (A:Type) :=
| Top : withTop A
| wTA (a:A) : withTop A.

Arguments Top [A].
Arguments wTA [A] a.

Instance withTop_eq_dec A `{EqDec A eq} : EqDec (withTop A) eq.
Proof.
  hnf. destruct x,y; eauto; try dec_solve.
  destruct (H a a0); try dec_solve.
  hnf in e. subst. left; eauto.
Qed.


Inductive withTop_le A R `{EqDec A R} : withTop A -> withTop A -> Prop :=
| WithTopLe_refl a b : R a b -> withTop_le (wTA a) (wTA b)
| WithTopLe_top a : withTop_le a Top.

Instance withTop_le_dec A R `{EqDec A R} (a b:withTop A) : Computable (withTop_le a b).
Proof.
  destruct a,b; hnf; eauto using withTop_le.
  - dec_solve.
  - decide (a === a0); dec_solve.
Defined.

Inductive withTop_eq A R `{EqDec A R} : withTop A -> withTop A -> Prop :=
| WithTopEq_refl a b : R a b -> withTop_eq (wTA a) (wTA b)
| WithTopEq_top : withTop_eq Top Top.

Lemma withTopEq_refl_sym A R `{EqDec A R} a b
  : poEq a b -> withTop_eq (wTA b) (wTA a).
Proof.
  econstructor. symmetry. eauto.
Qed.

Hint Resolve withTopEq_refl_sym.

Instance withTop_eq_comp A R `{EqDec A R} (a b:withTop A)
  : Computable (withTop_eq a b).
Proof.
  destruct a,b; hnf; eauto using withTop_eq.
  - dec_solve.
  - dec_solve.
  - decide (a === a0); dec_solve.
Defined.

Instance withTop_eq_equiv A R `{EqDec A R} : Equivalence (withTop_eq (A:=A) (R:=R)).
Proof.
  constructor.
  - hnf; intros []; eauto using @withTop_eq.
    econstructor. reflexivity.
  - hnf; intros [] []; inversion 1; subst; eauto using @withTop_eq.
    econstructor. symmetry. eauto.
  - hnf; intros [] [] [] X Y; inv X; inv Y; eauto using @withTop_eq.
    econstructor. etransitivity; eauto.
Qed.

Lemma withTop_le_refl A R `{EqDec A R}
  :  forall d d' : withTop A, withTop_eq d d' -> withTop_le d d'.
Proof.
  intros ? ? X; inv X; eauto using withTop_le.
Qed.

Instance withTop_le_Refl A R `{EqDec A R} : Reflexive (withTop_le (A:=A) (R:=R)).
Proof.
  hnf; intros.
  eapply withTop_le_refl. reflexivity.
Qed.

Instance withTop_le_trans A R `{EqDec A R}
  : Transitive (withTop_le (A:=A) (R:=R)).
Proof.
  hnf; intros [] [] [] X Y; inv X; inv Y; eauto using withTop_le.
  econstructor; etransitivity; eauto.
Qed.

Instance withTop_le_Trans A R `{EqDec A R} : Transitive (withTop_le (A:=A) (R:=R)).
Proof.
  hnf; intros.
  eapply withTop_le_trans. etransitivity; eauto. reflexivity.
Qed.

Instance withTop_le_anti A R `{EqDec A R}
  : Antisymmetric (withTop A) (withTop_eq (A:=A) (R:=R)) (withTop_le (A:=A) (R:=R)).
Proof.
  hnf; intros [] [] X Y; inv X; inv Y; eauto using withTop_eq.
Qed.

Instance withTop_PO A R `{EqDec A R} : PartialOrder (withTop A) :=
  {
    poLe := @withTop_le A R _ _;
    poEq := @withTop_eq A R _ _
  }.
Proof.
  - eapply withTop_le_refl.
Defined.

Lemma withTop_poLe_inv A R `{EqDec A R} (a b:A)
  : poLe (wTA a) (wTA b)
    -> a === b.
Proof.
  intros. inv H0. eapply H3.
Qed.

Smpl Add 100 match goal with
             | [ H : @poLe _ _ (wTA _) (wTA _) |- _ ] =>
               eapply withTop_poLe_inv in H
             | [ H : @poLe _ _ Top _ |- _ ] => invc H
             | [ H : @poLe _ _ _ (wTA _) |- _ ] => invc H
             | [ H : @poEq _ _ Top _ |- _ ] => invc H
             | [ H : @poEq _ _ _ Top |- _ ] => invc H
             | [ H : @poEq _ _ _ (wTA _) |- _ ] => invc H
             | [ H : @poEq _ _ (wTA _) _ |- _ ] => invc H
             | [ H : @withTop_le _ _ _ _ _ _ |- _ ] => invc H
             end : inv_trivial.


Definition withTop_generic_join A R `{EqDec A R} (a b:withTop A) :=
  match a, b with
  | Top, _ => Top
  | _, Top => Top
  | wTA a, wTA b => if [ a === b ] then wTA a else Top
  end.

Lemma withTop_generic_join_bound A R `{EqDec A R}
  : forall a b : withTop A, a ⊑ b -> withTop_generic_join a b ⊑ b.
Proof.
  intros []; simpl; intros; repeat cases; eauto; econstructor; eauto.
Qed.

Lemma withTop_generic_join_sym A R `{EqDec A R}
  : forall a b : withTop A, withTop_generic_join a b ≣ withTop_generic_join b a.
Proof.
  intros [] []; simpl; try econstructor.
  repeat cases; try econstructor; eauto.
  - exfalso; eapply NOTCOND. symmetry. eauto.
Qed.

Lemma withTop_generic_join_assoc A R `{EqDec A R}
  : forall a b c : withTop A,
    withTop_generic_join (withTop_generic_join a b) c
                         ≣ withTop_generic_join a (withTop_generic_join b c).
Proof.
  intros [] [] []; simpl; repeat (cases; simpl); eauto.
  - exfalso. eapply NOTCOND. rewrite <- COND. eauto.
  - exfalso. eapply NOTCOND. rewrite COND. eauto.
  - exfalso. eapply NOTCOND. eauto.
Qed.

Lemma poLe_withTopLe_refl A R `{EqDec A R} (a b : A)
  : R a b
    -> poLe (wTA a) (wTA b).
Proof.
  econstructor; eauto.
Qed.

Lemma poEq_withTopEq_refl A R `{EqDec A R} (a b : A)
  : R a b
    -> poEq (wTA a) (wTA b).
Proof.
  econstructor; eauto.
Qed.

Lemma poLe_withTopLe_top A R `{EqDec A R} (x:withTop A)
  : poLe x Top.
Proof.
  econstructor 2.
Qed.

Hint Resolve poEq_withTopEq_refl poLe_withTopLe_refl poLe_withTopLe_top.

Lemma withTop_generic_join_exp A R  `{EqDec A R}
  : forall a b : withTop A, a ⊑ withTop_generic_join a b.
Proof.
  intros [] []; simpl; repeat (cases; simpl); eauto.
Qed.

Instance withTop_generic_join_poEq A R `{EqDec A R}
  : Proper (poEq ==> poEq ==> poEq) (withTop_generic_join (A:=A) (R:=R)).
Proof.
  unfold Proper, respectful; intros.
  destruct x,y,x0,y0; simpl;
    repeat (cases; simpl); eauto;
      clear_trivial_eqs.
  - exfalso. eapply NOTCOND.
    rewrite <- H3, <- H4. eauto.
  - exfalso. eapply NOTCOND. rewrite H4, H3. eauto.
Qed.

Instance withTop_generic_join_poLe A R `{EqDec A R}
  : Proper (poLe ==> poLe ==> poLe) (withTop_generic_join (A:=A) (R:=R)).
Proof.
  unfold Proper, respectful; intros.
  destruct x,y,x0,y0; simpl; eauto using withTop_le;
    repeat (cases; simpl); eauto using withTop_le.
  - exfalso. eapply NOTCOND. rewrite H0, H1. eauto.
Qed.

Instance withTop_JSL A R `{EqDec A R} : JoinSemiLattice (withTop A) :=
  {
    join := @withTop_generic_join A R _ _
  }.
Proof.
  - eapply withTop_generic_join_bound.
  - eapply withTop_generic_join_sym.
  - eapply withTop_generic_join_assoc.
  - eapply withTop_generic_join_exp.
Defined.


Inductive withUnknown (A:Type) :=
| Known (a:A) : withUnknown A
| Unknown : withUnknown A.

Arguments Unknown [A].
Arguments Known [A] a.

Instance withUnknown_eq_dec A `{EqDec A eq} : EqDec (withUnknown A) eq.
Proof.
  hnf. destruct x,y; eauto; try dec_solve.
  destruct (H a a0); try dec_solve.
  hnf in e. subst. left; eauto.
Qed.

Inductive withUnknown_eq A R `{EqDec A R} : withUnknown A -> withUnknown A -> Prop :=
| WithUnknownEq_refl a b : R a b -> withUnknown_eq (Known a) (Known b)
| WithUnknownEq_top : withUnknown_eq Unknown Unknown.


Smpl Add 100 match goal with
             | [ H : Known _ === Known _ |- _ ] => invc H
             | [ H : withUnknown_eq _ _ |- _ ] => invc H
             end : inv_trivial.

Lemma withUnknownEq_refl_sym A `{PartialOrder A} a b
  : poEq a b -> withUnknown_eq (Known b) (Known a).
Proof.
  econstructor. symmetry. eauto.
Qed.

Hint Resolve withUnknownEq_refl_sym.

Instance withUnknown_eq_comp A R `{EqDec A R} (a b:withUnknown A)
  : Computable (withUnknown_eq a b).
Proof.
  destruct a,b; hnf; eauto using withUnknown_eq.
  - decide (a === a0); dec_solve.
  - dec_solve.
  - dec_solve.
Defined.

Instance withUnknown_eq_equiv A R `{EqDec A R}
  : Equivalence (withUnknown_eq (A:=A) (R:=R)).
Proof.
  constructor.
  - hnf; intros []; eauto using @withUnknown_eq.
    econstructor. reflexivity.
  - hnf; intros [] []; inversion 1; subst; eauto using @withUnknown_eq.
    econstructor. symmetry. eauto.
  - hnf; intros [] [] [] X Y; inv X; inv Y; eauto using @withUnknown_eq.
    econstructor. etransitivity; eauto.
Qed.

Instance withUnknown_PO A R `{EqDec A R} : PartialOrder (withUnknown A) :=
  {
    poLe := @withUnknown_eq A R _ _ ;
    poEq := @withUnknown_eq A R _ _
  }.
Proof.
  - eauto.
  - hnf; intros; eauto.
Defined.

Instance withUnknown_EqDec A R `{EqDec A R}
  : EqDec (withUnknown A) (@withUnknown_eq _ _ _ _).
Proof.
  hnf. eapply withUnknown_eq_comp.
Defined.

Inductive withBot (A:Type) :=
| Bot : withBot A
| WBElt (a:A) : withBot A.

Arguments Bot [A].
Arguments WBElt [A] a.

Instance withBot_eq_dec A `{EqDec A eq} : EqDec (withBot A) eq.
Proof.
  hnf. destruct x,y; eauto; try dec_solve.
  destruct (H a a0); try dec_solve.
  hnf in e. subst. left; eauto.
Qed.


Inductive withBot_le A `{PartialOrder A} : withBot A -> withBot A -> Prop :=
| WithBotLe_refl a b : poLe a b -> withBot_le (WBElt a) (WBElt b)
| WithBotLe_bot a : withBot_le Bot a.

Instance withBot_le_dec A `{PartialOrder A} (a b:withBot A) : Computable (withBot_le a b).
Proof.
  destruct a,b; hnf; eauto using withBot_le.
  - dec_solve.
  - decide (poLe a a0); dec_solve.
Defined.

Inductive withBot_eq A `{PartialOrder A} : withBot A -> withBot A -> Prop :=
| WithBotEq_refl a b : poEq a b -> withBot_eq (WBElt a) (WBElt b)
| WithBotEq_bot : withBot_eq Bot Bot.

Lemma withBotEq_refl_sym A `{PartialOrder A} a b
  : poEq a b -> withBot_eq (WBElt b) (WBElt a).
Proof.
  econstructor. symmetry. eauto.
Qed.

Hint Resolve withBotEq_refl_sym.

Instance withBot_eq_comp A `{PartialOrder A} (a b:withBot A)
  : Computable (withBot_eq a b).
Proof.
  destruct a,b; hnf; eauto using withBot_eq.
  - dec_solve.
  - dec_solve.
  - decide (poEq a a0); dec_solve.
Defined.

Instance withBot_eq_equiv A `{PartialOrder A} : Equivalence (withBot_eq (A:=A)).
Proof.
  constructor.
  - hnf; intros []; eauto using @withBot_eq.
  - hnf; intros [] []; inversion 1; subst; eauto using @withBot_eq.
  - hnf; intros [] [] [] X Y; inv X; inv Y; eauto using @withBot_eq.
    econstructor. etransitivity; eauto.
Qed.

Lemma withBotLe_refl A `{PartialOrder A}
  :  forall d d' : withBot A, withBot_eq d d' -> withBot_le d d'.
Proof.
  intros ? ? X; inv X; eauto using withBot_le.
Qed.


Instance withBot_le_trans A `{PartialOrder A}
  : Transitive (withBot_le (A:=A)).
Proof.
  hnf; intros [] [] [] X Y; inv X; inv Y; eauto using withBot_le.
Qed.

Instance withBot_le_anti A `{PartialOrder A}
  : Antisymmetric (withBot A) (withBot_eq (A:=A)) (withBot_le (A:=A)).
Proof.
  hnf; intros [] [] X Y; inv X; inv Y; eauto using withBot_eq.
  exploit poLe_antisymmetric; eauto.
Qed.

Instance withBot_PO A `{PartialOrder A} : PartialOrder (withBot A) :=
  {
    poLe := @withBot_le A _;
    poEq := @withBot_eq A _
  }.
Proof.
  - eapply withBotLe_refl.
Defined.

Instance withBot_lower_bounded A `{PartialOrder A} : LowerBounded (withBot A) :=
  {
    bottom := Bot
  }.
Proof.
  intros. destruct a; econstructor.
Qed.
