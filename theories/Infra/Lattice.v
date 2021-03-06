
(*
Lattice development from Daniel W.H. James and Ralf Hinze
http://www.cs.ox.ac.uk/people/daniel.james/lattice.html

Updated to accomodate non-extensional equalities
*)

Require Export Containers.OrderedType Setoid Coq.Classes.Morphisms Computable.
Require Export Util Get MoreList PartialOrder.
Require Import EqDec DecSolve List AllInRel OptionPO.

Class JoinSemiLattice (A : Type) `{PartialOrder A} :=
  {
      join : A -> A -> A;

      join_bound : forall a b, poLe a b -> poLe (join a b) b;
      join_commutative : forall a b, poEq (join a b) (join b a);
      join_associative : forall a b c, poEq (join (join a b) c) (join a (join b c));
      join_poLe : forall a b, poLe a (join a b);

      join_respects_eq :> Proper (poEq ==> poEq ==> poEq) join;
      join_respects_le :> Proper (poLe ==> poLe ==> poLe) join
  }.


Arguments join : simpl never.

Lemma join_wellbehaved
  : forall A `{JoinSemiLattice A} x y, poEq x (join x y) <-> poLe y x.
  split.
  - intros. rewrite H1. rewrite join_commutative. eapply join_poLe.
  - intros. eapply poLe_antisymmetric. eapply join_poLe.
    rewrite join_commutative.
    rewrite join_bound; eauto.
Qed.


Lemma join_poLe_right X `{JoinSemiLattice X} x y
  : poLe y (join x y).
Proof.
  rewrite join_commutative. eapply join_poLe.
Qed.

Hint Immediate join_poLe_right.

Lemma join_idempotent
  :  forall A `{JoinSemiLattice A} x, poEq (join x x) x.
Proof.
  intros. symmetry. rewrite join_wellbehaved. reflexivity.
Qed.

Lemma join_idempotent'
  :  forall A `{JoinSemiLattice A} x y, poLe x y -> poEq (join x y) y.
Proof.
  intros. symmetry. rewrite join_commutative.
  eapply join_wellbehaved. eauto.
Qed.

Class LowerBounded (A : Type) `{PartialOrder A} :=
  {
    bottom : A;
    bottom_least : forall a, poLe bottom a;
  }.

Infix "⊔" := join (at level 70, no associativity).
Notation "⊥" := bottom (at level 70, no associativity).

Arguments bottom : simpl never.

Instance pair_semilattice A B `{JoinSemiLattice A} `{JoinSemiLattice B}
  : JoinSemiLattice (A * B) := {
  join x y := (join (fst x) (fst y), join (snd x) (snd y))
}.
Proof.
  - intros [a1 b2] [b1 b3]; split; simpl; clear_trivial_eqs;
      eapply join_bound; eauto.
  - intros [a1 a2] [b1 b2]; split; simpl; eapply join_commutative.
  - intros [a1 a2] [b1 b2] [c1 c2]; split; simpl; eapply join_associative.
  - intros [a1 a2] [b1 b2]; split; simpl; eapply join_poLe.
  - intros [a1 a2] [b1 b2] [EQa EQb] [c1 c2] [d1 d2] [EQc EQd]; simpl in *;
      split; eapply join_respects_eq; eauto.
  - intros [a1 a2] [b1 b2] [LEa LEb] [c1 c2] [d1 d2] [LEc LEd]; simpl in *;
      split; eapply join_respects_le; eauto.
Defined.

Instance pair_boundedsemilattice A B `{LowerBounded A} `{LowerBounded B}
  : LowerBounded (A * B) := {
  bottom := (bottom, bottom);
}.
Proof.
  - intros [a b]; split; simpl; eapply bottom_least.
Defined.


Instance bool_joinsemilattice
  : JoinSemiLattice bool := {
  join := orb
}.
Proof.
  - intros []; simpl; eauto.
  - intros [] []; simpl; eauto.
  - intros [] [] []; simpl; eauto.
  - intros [] []; simpl; eauto.
  - intros [] [] LE [] [] LE'; simpl in *; eauto.
Defined.

Instance bool_lowerbounded : LowerBounded bool :=
  {
    bottom := false
  }.
Proof.
  intros; econstructor.
Defined.

Definition ojoin A join (x y:option A) :=
  match x, y with
  | x, None => x
  | None, y => y
  | Some x, Some y => Some (join x y)
  end.

Instance ojoin_poEq A `{JoinSemiLattice A}
  : Proper (poEq ==> poEq ==> poEq) (ojoin A join).
Proof.
  unfold Proper, respectful.
  intros ? ? EQ ? ? EQ'; inversion EQ; inversion EQ'; subst; simpl; eauto.
  econstructor. rewrite H1, H4. reflexivity.
Qed.

Instance ojoin_poLe A `{JoinSemiLattice A}
  : Proper (poLe ==> poLe ==> poLe) (ojoin A join).
Proof.
  unfold Proper, respectful.
  intros ? [y|] EQ ? [y'|] EQ'; inversion EQ; inversion EQ'; subst; simpl;
    eauto.
  - econstructor. rewrite H5. rewrite join_commutative. eapply join_poLe.
  - econstructor. rewrite H3. eapply join_poLe.
  - econstructor. rewrite H3. rewrite H6. reflexivity.
Qed.

Instance option_boundedsemilattice A `{JoinSemiLattice A}
  : @JoinSemiLattice (option A) (PartialOrder_option_fstNoneOrR _) := {
  join := ojoin _ join
}.
Proof.
  - intros [a|] [b|]; simpl; intros; clear_trivial_eqs;
      econstructor; eauto using join_bound.
  - intros [a|] [b|]; simpl; econstructor; eauto using join_commutative.
  - intros [a1|] [b1|] [c1|]; simpl; econstructor; eauto using join_associative.
  - intros [a|] [b|]; simpl; econstructor; eauto using join_poLe.
Defined.

Lemma join_struct T `{JoinSemiLattice T} (a b a' b':T)
  : a ⊑ a'
    -> b ⊑ b'
    -> a ⊔ b ⊑ (a' ⊔ b').
Proof.
  intros A B. rewrite A, B. reflexivity.
Qed.


Lemma join_struct_eq T `{JoinSemiLattice T} (a b a' b':T)
  : a ≣ a'
    -> b ≣ b'
    -> a ⊔ b ≣ (a' ⊔ b').
Proof.
  intros A B. rewrite A, B. reflexivity.
Qed.


Lemma fold_left_join_struct T `{JoinSemiLattice T} (A A':list T) (b b':T)
  : PIR2 poLe A A'
    -> b ⊑ b'
    -> fold_left join A b ⊑ fold_left join A' b'.
Proof.
  intros pir. revert b b'.
  induction pir; simpl; eauto.
  intros. eapply IHpir.
  eapply join_struct; eauto.
Qed.


Lemma PIR2_bottom_least A B `{LowerBounded A} (ZL:list B) (l:list A)
  : ❬ZL❭ = ❬l❭
    -> PIR2 poLe (tab (⊥) ‖ZL‖) l.
Proof.
  intros. eapply PIR2_get; intros; inv_get; eauto with len.
  eapply bottom_least.
Qed.


Lemma fold_left_join_start_swap X `{JoinSemiLattice X} (a b:X) A
  : poEq (fold_left join A (join a b)) (join b (fold_left join A a)).
Proof.
  general induction A; simpl.
  - simpl. rewrite join_commutative. reflexivity.
  - rewrite !IHA.
    rewrite <- !join_associative.
    setoid_rewrite join_commutative at 2.
    reflexivity.
Qed.


Lemma proj1_sig_poEq X `{PartialOrder X} P (a b:{ x : X | P x })
  : poEq a b -> poEq (proj1_sig a) (proj1_sig b).
Proof.
  destruct a,b; eauto.
Qed.


Lemma join_false_left x
  : false ⊔ x = x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma join_false_right x
  : x ⊔ false = x.
Proof.
  destruct x; reflexivity.
Qed.


Ltac clear_join_false :=
  match goal with
  | [ H : context [false ⊔ _] |- _ ] => rewrite join_false_left in H
  | [ H : context [_ ⊔ false] |- _ ] => rewrite join_false_right in H
  end.

Smpl Add clear_join_false : inv_trivial.


Lemma join_poLe_left (X : Type) (H : PartialOrder X) (H0 : JoinSemiLattice X)
      (x y z : X)
  : x ⊑ z -> y ⊑ z -> x ⊔ y ⊑ z.
Proof.
  intros.
  rewrite H1, H2.
  rewrite (join_idempotent _ z).
  reflexivity.
Qed.
