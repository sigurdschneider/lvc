
(*
Lattice development from Daniel W.H. James and Ralf Hinze
http://www.cs.ox.ac.uk/people/daniel.james/lattice.html

Updated to accomodate non-extensional equalities
*)

Require Export Containers.OrderedType Setoid Coq.Classes.Morphisms.

(**
TODO: make Order a prerequite of Lattice; then
then things become simpler(?). The problem of
going round in a circle does not show up (derive
Order from Lattice and then Lattice from order;
is the order the same?).
*)

Class SemiLattice (A : Type) `{OrderedType A} := {
  bottom : A;
  join : A -> A -> A;

  join_idempotent : forall a, join a a === a;
  join_commutative : forall a b, join a b === join b a;
  join_associative : forall a b c, join (join a b) c === join a (join b c)

(* todo: add those back (A needs _eq and _lt defs then)  
  join_respects_eq :> Proper (_eq ==> _eq ==> _eq) join;
  join_respects_le :> Proper (_lt ==> _lt ==> _lt) join*)
}.

(*
Class Lattice (A : Type) `{OrderedType A} := {
  meet : A -> A -> A;
  join : A -> A -> A;

  meet_idempotent : forall a, meet a a === a;
  meet_commutative : forall a b, meet a b === meet b a;
  meet_associative : forall a b c, meet (meet a b) c === meet a (meet b c);
  meet_absorptive : forall a b : A, meet a (join a b) === a;
 
  meet_respects_eq :> Proper (equal ==> _eq ==> _eq) meet;
  meet_respects_le :> Proper (_le ==> _le ==> _le) meet;
  
  join_idempotent : forall a, join a a === a;
  join_commutative : forall a b, join a b === join b a;
  join_associative : forall a b c, join (join a b) c === join a (join b c);
  join_absorptive : forall a b : A, join a (meet a b) === a

  join_respects_eq : Proper (_eq ==> _eq ==> _eq) join;
  join_respects_le : Proper (_le ==> _le ==> _le) join
}.
*)
Generalizable Variable A.

(* Infix "/*\" := meet (at level 40, left associativity) : lattice_scope. *)
Infix "\*/" := join (at level 50, left associativity) : lattice_scope.

Local Open Scope lattice_scope.


Section SemiLatticeTheory.
  Context `{l : SemiLattice A}.
  Hint Immediate join_idempotent join_commutative join_associative.

  (** *)

End SemiLatticeTheory.

(*

Section LatticeTheory.
  Context `{l : Lattice A}.
  Hint Immediate meet_idempotent meet_commutative meet_associative meet_absorptive.
  Hint Immediate join_idempotent join_commutative join_associative join_absorptive.

  Lemma lte_meet_join : forall a b, a /*\ b === a <-> a \*/ b === b.
  Proof.
  split; intro EQ. rewrite <- EQ.
    rewrite join_commutative.
    rewrite meet_commutative.
    rewrite join_absorptive.
    reflexivity.
    rewrite meet_absorptive.
    reflexivity.
   Qed.

  (** *)

  Definition meet_distributive_l_law := forall x y z, x /*\ (y \*/ z) = (x /*\ y) \*/ (x /*\ z).
  Definition meet_distributive_r_law := forall x y z, (x \*/ y) /*\ z = (x /*\ z) \*/ (y /*\ z).
  Definition join_distributive_l_law := forall x y z, x \*/ (y /*\ z) = (x \*/ y) /*\ (x \*/ z).
  Definition join_distributive_r_law := forall x y z, (x /*\ y) \*/ z= (x \*/ z) /*\ (y \*/ z).

  (** One law implies the other three. *)

  Lemma meet_distributive_l_r : meet_distributive_l_law -> meet_distributive_r_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y z.
  rewrite meet_commutative.
  rewrite meet_distributive_l.
  rewrite meet_commutative.
  rewrite (meet_commutative z y).
  reflexivity.
  Qed.

  Lemma meet_distributive_r_l : meet_distributive_r_law -> meet_distributive_l_law.
  Proof.
  unfold meet_distributive_r_law; intro meet_distributive_r.
  intros x y z.
  rewrite meet_commutative.
  rewrite meet_distributive_r.
  rewrite meet_commutative.
  rewrite (meet_commutative z x).
  reflexivity.
  Qed.

  Lemma join_distributive_l_r : join_distributive_l_law -> join_distributive_r_law.
  Proof.
  unfold join_distributive_l_law; intro join_distributive_l.
  intros x y z.
  rewrite join_commutative.
  rewrite join_distributive_l.
  rewrite join_commutative.
  rewrite (join_commutative z y).
  reflexivity.
  Qed.

  Lemma join_distributive_r_l : join_distributive_r_law -> join_distributive_l_law.
  Proof.
  unfold join_distributive_r_law; intro join_distributive_r.
  intros x y z.
  rewrite join_commutative.
  rewrite join_distributive_r.
  rewrite join_commutative.
  rewrite (join_commutative z x).
  reflexivity.
  Qed.

  Lemma distributive_meet_l_join_l : meet_distributive_l_law -> join_distributive_l_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros x y z.
  rewrite meet_distributive_l.
  rewrite (meet_commutative (x \*/ y) x).
  rewrite meet_absorptive.
  rewrite (meet_distributive_l_r meet_distributive_l).
  rewrite <- (join_associative x (x /*\ z) (y /*\ z)).
  rewrite join_absorptive.
  reflexivity.
  Qed.

  Lemma distributive_join_l_meet_l : join_distributive_l_law -> meet_distributive_l_law.
  Proof.
  unfold join_distributive_l_law; intro join_distributive_l.
  intros x y z.
  rewrite join_distributive_l.
  rewrite (join_commutative (x /*\ y) x).
  rewrite join_absorptive.
  rewrite (join_distributive_l_r join_distributive_l).
  rewrite <- meet_associative.
  rewrite meet_absorptive.
  reflexivity.
  Qed.

  Definition median_law := forall x y z,
    (x /*\ y) \*/ (y /*\ z) \*/ (z /*\ x) = (x \*/ y) /*\ (y \*/ z) /*\ (z \*/ x).

  Definition cancel_law := forall a b c, a /*\ b = c /*\ b /\ a \*/ b = c \*/ b -> a = c.

  Lemma distr_cancel : meet_distributive_l_law -> cancel_law.
  Proof.
  unfold meet_distributive_l_law; intro meet_distributive_l.
  intros a b c [Hi Hs].
  rewrite <- (join_absorptive a b).
  rewrite Hi.
  rewrite (distributive_meet_l_join_l meet_distributive_l).
  rewrite Hs.
  rewrite join_commutative.
  rewrite <- (distributive_meet_l_join_l meet_distributive_l).
  rewrite Hi.
  rewrite join_absorptive.
  reflexivity.
  Qed.
End LatticeTheory.
*)


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*) 