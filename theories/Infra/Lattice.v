
(*
Lattice development from Daniel W.H. James and Ralf Hinze
http://www.cs.ox.ac.uk/people/daniel.james/lattice.html

Updated to accomodate non-extensional equalities
*)

Require Export Containers.OrderedType Setoid Coq.Classes.Morphisms Computable.
Require Export PartialOrder.
Require Import EqDec DecSolve.

Class JoinSemiLattice (A : Type) `{PartialOrder A} :=
  {
      join : A -> A -> A;

      join_idempotent : forall a, poEq (join a a) a;
      join_commutative : forall a b, poEq (join a b) (join b a);
      join_associative : forall a b c, poEq (join (join a b) c) (join a (join b c));
      join_poLe : forall a b, poLe a (join a b);

      join_respects_eq :> Proper (poEq ==> poEq ==> poEq) join;
      join_respects_le :> Proper (poLe ==> poLe ==> poLe) join
  }.

Class LowerBounded (A : Type) `{PartialOrder A} :=
  {
    bottom : A;
    bottom_least : forall a, poLe bottom a;
  }.

Infix "⊔" := join (at level 70, no associativity).
Notation "⊥" := bottom (at level 70, no associativity).

Instance pair_semilattice A B `{JoinSemiLattice A} `{JoinSemiLattice B}
  : JoinSemiLattice (A * B) := {
  join x y := (join (fst x) (fst y), join (snd x) (snd y))
}.
Proof.
  - intros [a b]; split; simpl; eapply join_idempotent.
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

Require Import OptionR.

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
  intros ? ? EQ ? ? EQ'; inversion EQ; inversion EQ'; subst; simpl;
    eauto using option_R.
  econstructor. rewrite H1, H4. reflexivity.
Qed.

Instance ojoin_poLe A `{JoinSemiLattice A}
  : Proper (poLe ==> poLe ==> poLe) (ojoin A join).
Proof.
  unfold Proper, respectful.
  intros ? [y|] EQ ? [y'|] EQ'; inversion EQ; inversion EQ'; subst; simpl;
    eauto using fstNoneOrR.
  - econstructor. rewrite H5. rewrite join_commutative. eapply join_poLe.
  - econstructor. rewrite H3. eapply join_poLe.
  - econstructor. rewrite H3. rewrite H6. reflexivity.
Qed.

Instance option_boundedsemilattice A `{JoinSemiLattice A}
  : @JoinSemiLattice (option A) (PartialOrder_option_fstNoneOrR _) := {
  join := ojoin _ join
}.
Proof.
  - intros [a|]; simpl; eauto using option_R, join_idempotent.
  - intros [a|] [b|]; simpl; eauto using option_R, join_commutative.
  - intros [a1|] [b1|] [c1|]; simpl; eauto using option_R, join_associative.
  - intros [a|] [b|]; simpl; eauto using fstNoneOrR, join_poLe.
Defined.
