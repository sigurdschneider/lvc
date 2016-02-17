Require Import Setoid Morphisms.
Require Export Coq.Classes.Equivalence.
Open Scope equiv_scope.

Generalizable All Variables.

(** * Ordered Types

   This file corresponds to OrderedType.v in the standard FSets/FMaps
   library. It contains a formalization of types equipped with a total
   and decidable order.
   Notations on ordered types are defined in scope [compare_scope],
   delimited by key [compare].
   *)
Delimit Scope compare_scope with compare.

(** ** Strict orders : the [StrictOrder] class

   A strict order [lt] with respect to an equivalence relation [eq]
   on a type [A] is an antireflexive transitive relation, ie. it
   is a transitive relation that does not contain two congruent terms.
   We define the class [StrictOrder A lt eq] of such objects.
   *)
Class StrictOrder {A} lt eq {equiv : Equivalence eq} := {
  StrictOrder_Transitive :> Transitive lt;
  StrictOrder_Irreflexive : forall (x y : A), lt x y -> x =/= y
}.
Definition lt_StrictOrder `{StrictOrder A lt_ eq_} := lt_.

(** If [x] and [y] belong to a strict order, we define the
   notations [x >>> y] and [y <<< x]. *)
Notation " x >>> y " := (lt_StrictOrder y x)
  (at level 70, no associativity, only parsing) : compare_scope.
Notation " x <<< y " := (lt_StrictOrder x y)
  (at level 70, no associativity) : compare_scope.
Open Scope compare_scope.

(** A couple of useful basic properties about strict orders. *)
Set Implicit Arguments. Unset Strict Implicit.
Section StrictOrderProps.
  Context `{StrictOrder A}.

  Property lt_antirefl : forall x, ~x <<< x.
  Proof.
    intros; intro Hlt; apply (StrictOrder_Irreflexive x x Hlt); reflexivity.
  Qed.
  Property lt_not_eq : forall x y, x <<< y -> x =/= y.
  Proof.
    intros; apply StrictOrder_Irreflexive; auto.
  Qed.
  Property gt_not_eq : forall x y, x >>> y -> x =/= y.
  Proof.
    intros; intro abs; symmetry in abs; revert abs; apply lt_not_eq; auto.
  Qed.
  Property eq_not_lt : forall x y, x === y -> ~ x <<< y.
  Proof.
    intros; intro abs; apply (lt_not_eq abs); auto.
  Qed.
  Property eq_not_gt : forall x y, x === y -> ~ x >>> y.
  Proof.
    intros; intro abs; apply (gt_not_eq abs); auto.
  Qed.
  Property lt_not_gt : forall x y, x <<< y -> ~(x >>> y).
  Proof.
    intros; intro abs; refine (lt_not_eq _ _).
    apply transitivity with y; eauto. reflexivity.
  Qed.
End StrictOrderProps.
Unset Implicit Arguments.

(** ** Ordered types : the [OrderedType] class

   [OrderedType] is the class of types that enjoy decidable comparison for
   a given setoid equality and strict order relation with respect to this
   equality. An instance of [OrderedType] for a type [A] must bring :
   - the equality relation [eq]
   - a proof that [eq] is an equivalence relation
   - the order relation [lt]
   - an instance of [StrictOrder] for [lt] and [eq]
   - a comparison function [cmp : A -> A -> comparison]
   - a proof that [cmp] really implements [lt] and [eq]

   With respect to the original formalization in the FSets/FMaps library,
   the fundamental difference is that the comparison function is purely
   computational, whereas the return type of the [compare] function in
   [FSets.OrderedType] includes proofs. In that sense, this formalisation
   is more similar to [FSets.OrderedTypeAlt]. To define the specification
   that the function [cmp] must meet, unlike [OrderedTypeAlt], we use
   the following inductive view [compare_spec] :
   *)
Inductive compare_spec {A} eq lt (x y : A) : comparison -> Prop :=
| compare_spec_lt : lt x y -> compare_spec eq lt x y Lt
| compare_spec_eq : eq x y -> compare_spec eq lt x y Eq
| compare_spec_gt : lt y x -> compare_spec eq lt x y Gt.

(** [compare_spec] describes what is the correct result for a comparison
   between two elements [x] and [y] ; in particular, a suitable comparison
   function is a function that is included in this relation.

   Given these definitions, we can now define the [OrderedType] class.
   *)
Class OrderedType (A : Type) := {
  _eq : relation A;
  _lt : relation A;
  OT_Equivalence :> Equivalence _eq;
  OT_StrictOrder :> StrictOrder _lt _eq;
  _cmp : A -> A -> comparison;
  _compare_spec : forall x y, compare_spec _eq _lt x y (_cmp x y)
}.

(** If [x] and [y] belong to an ordered type [A], we can write [compare x y]
   to denote the comparison of [x] and [y], as well as the special handy
   notation [x =?= y]. *)
Definition compare `{OrderedType A} := _cmp.
Notation " x =?= y " :=
  (compare (x :>) (y :>)) (no associativity, at level 70) : compare_scope.

(** The following lemma is a convenient way to access the specification of
   the [compare] function. Its typical use is the following : if a comparison
   [x =?= y] appears in the Coq context, [destruct (compare_dec x y)] will
   create 3 branches for each result of the comparison, and add the correct
   hypothesis in each branch. It is almost as easy to work with as the
   original dependently-typed [OrderedType.compare] function.
   *)
Definition compare_dec `{H : OrderedType A} :
  forall x y, compare_spec equiv lt_StrictOrder x y (compare x y) :=
    @_compare_spec A H.

(** [compare] is made globally opaque so that case analysis can be done
   easily by destructing [compare_dec _ _]. *)
Global Opaque compare.

(** We define shortcut notations [x == y], [x << y] and [x >> y]
   for purely computational equality and ordering tests, and
   their specification as well. *)
Definition is_compare `{OrderedType A} (x y : A) c :=
  match x =?= y, c with
    | Eq, Eq | Lt, Lt | Gt, Gt => true
    | _, _ => false
  end.
Notation " x == y " :=
  (is_compare x y Eq) (no associativity, at level 70) : compare_scope.
Notation " x << y " :=
  (is_compare x y Lt) (no associativity, at level 70) : compare_scope.
Notation " x >> y " :=
  (is_compare x y Gt) (no associativity, at level 70) : compare_scope.

Property compare_1 `{OrderedType A} : forall x y, x =?= y = Lt -> x <<< y.
Proof.
  intros; destruct (compare_dec x y); auto; congruence.
Qed.
Property compare_2 `{OrderedType A} : forall x y, x =?= y = Eq -> x === y.
Proof.
  intros; destruct (compare_dec x y); auto; congruence.
Qed.
Property compare_3 `{OrderedType A} : forall x y, x =?= y = Gt -> x >>> y.
Proof.
  intros; destruct (compare_dec x y); auto; congruence.
Qed.

(** Decidability lemmas for equality and orders, specified in a way
   similar to [compare_spec]. *)
Inductive decides {A} (R : relation A) (x y : A) : bool -> Prop :=
| decides_true : R x y -> decides R x y true
| decides_false : ~(R x y) -> decides R x y false.

Property eq_dec `{OrderedType A} :
  forall (x y : A), decides equiv x y (x==y).
Proof.
  intros; unfold is_compare. destruct (compare_dec x y); constructor.
  apply lt_not_eq; auto.
  assumption.
  apply gt_not_eq; auto.
Qed.
Property lt_dec `{OrderedType A} :
  forall x y, decides lt_StrictOrder x y (x<<y).
Proof.
  intros; unfold is_compare. destruct (compare_dec x y); constructor.
  assumption.
  intro abs; apply (lt_not_eq abs); auto.
  apply lt_not_gt; auto.
Qed.
Property gt_dec `{OrderedType A} :
  forall x y, decides lt_StrictOrder y x (x>>y).
Proof.
  intros; unfold is_compare. destruct (compare_dec x y); constructor.
  apply lt_not_gt; auto.
  intro abs; apply (gt_not_eq abs); auto.
  assumption.
Qed.

(** More lemmas about ordered types, in particular the fact that
   the order relations are morphisms for equality. *)
Set Implicit Arguments. Unset Strict Implicit.
Property eq_lt `{OrderedType A} :
  forall (x x' y : A), x === x' -> x <<< y -> x' <<< y.
Proof.
  intros; destruct (compare_dec x' y); auto.
  contradiction (lt_not_eq H1); transitivity x'; auto.
  contradiction (lt_not_eq (x:=x) (y:=x')); auto; transitivity y; auto.
Qed.
Corollary eq_lt2 `{OrderedType A} :
  forall (x x' y : A), x === x' -> x' <<< y -> x <<< y.
Proof.
  intros; apply eq_lt with x'; auto; symmetry; auto.
Qed.
Property eq_gt `{OrderedType A} :
  forall (x x' y : A), x === x' -> x >>> y -> x' >>> y.
Proof.
  intros; destruct (compare_dec x' y); auto.
  contradiction (gt_not_eq (x:=x) (y:=x')); auto; transitivity y; auto.
  contradiction (gt_not_eq H1); transitivity x'; auto.
Qed.
Instance lt_m `{OrderedType A} : Proper (_eq ==> _eq ==> iff) _lt.
Proof.
  repeat intro; split; intro Hlt.
  apply (eq_lt (x:=x)); auto. apply (eq_gt (x:=x0)); auto.
  apply (eq_lt (x:=y)); try symmetry; auto.
  apply (eq_gt (x:=y0)); try symmetry; auto.
Qed.
Instance le_m `{OrderedType A} : Proper (_eq ==> _eq ==> iff) (complement _lt).
Proof.
  repeat intro; split; intro Hlt; unfold complement in  *.
  rewrite H1 in Hlt; rewrite H0 in Hlt; assumption.
  rewrite H0, H1; assumption.
Qed.

(** Shortcut lemmas for the [order] tactic *)
Section OrderLemmas.
  Context `{OrderedType A}.
  Variables x y z : A.

  Corollary lt_eq : x <<< y -> y === z -> x <<< z.
  Proof.
    intros; rewrite <- H1; assumption.
  Qed.
  Corollary le_eq : ~x <<< y -> y === z -> ~x <<< z.
  Proof.
    intros; rewrite <- H1; assumption.
  Qed.
  Corollary eq_le : x === y -> ~y <<< z -> ~x <<< z.
  Proof.
    intros; rewrite H0; assumption.
  Qed.
  Corollary neq_eq : x =/= y -> y === z -> x =/= z.
  Proof.
    intros; rewrite <- H1; assumption.
  Qed.
  Corollary eq_neq : x === y -> y =/= z -> x =/= z.
  Proof.
    intros; rewrite H0; assumption.
  Qed.

  Property le_lt_trans : ~ y <<< x -> y <<< z -> x <<< z.
  Proof.
    intros; destruct (compare_dec x z); auto.
    rewrite <- H2 in H1; contradiction.
    contradiction H0; transitivity z; auto.
  Qed.
  Property lt_le_trans : x <<< y -> ~ z <<< y -> x <<< z.
  Proof.
    intros; destruct (compare_dec x z); auto.
    rewrite <- H2 in H1; contradiction.
    contradiction H1; transitivity x; auto.
  Qed.
  Property le_neq : ~x <<< y -> x =/= y -> x >>> y.
  Proof.
    intros; destruct (compare_dec x y); auto; contradiction.
  Qed.

  Lemma elim_compare_eq : x === y -> x =?= y = Eq.
  Proof.
    intros; destruct (compare_dec x y); auto.
    contradiction (lt_not_eq H1 H0).
    contradiction (lt_not_eq H1 (symmetry H0)).
  Qed.
  Lemma elim_compare_lt : x <<< y -> x =?= y = Lt.
  Proof.
    intros; destruct (compare_dec x y); auto.
    contradiction (lt_not_eq H0 H1).
    contradiction (lt_not_gt H1 H0).
  Qed.
  Lemma elim_compare_gt : x >>> y -> x =?= y = Gt.
  Proof.
    intros; destruct (compare_dec x y); auto.
    contradiction (lt_not_gt H1 H0).
    contradiction (gt_not_eq H0 H1).
  Qed.
End OrderLemmas.
Unset Implicit Arguments.

(** The following is the adaptation of the original [order] tactic
   developed by P. Letouzey in the original library. It should
   prove exactly the same goals, with a slight decrease in performance
   due to the extra implicit instance parameters.
   *)
Ltac normalize_notations :=
  match goal with
 | H : ?R ?x ?y |- _ =>
   progress ((change (x === y) in H) || (change (x <<< y) in H) ||
     (change (x >>> y) in H)); normalize_notations
 | H : ~(?R ?x ?y) |- _ =>
   progress ((change (x =/= y) in H) || (change (~ x <<< y) in H) ||
     (change (~ y <<< x) in H)); normalize_notations
 | |- ?R ?x ?y =>
   progress (change (x === y) || change (x <<< y) || change (y <<< x))
 | |- ~?R ?x ?y =>
   progress (change (x =/= y) || change (~x <<< y) || change (~y <<< x))
 | _ => idtac
  end.

Ltac abstraction := match goal with
 | H : False |- _ => elim H
 | H : ?x <<< ?x |- _ => elim (lt_antirefl H)
 | H : ?x =/= ?x |- _ => elim (H (reflexivity x))
 | H : ?x === ?x |- _ => clear H; abstraction
 | H : ~?x <<< ?x |- _ => clear H; abstraction
 | |- ?x === ?x => reflexivity
 | |- ?x <<< ?x => elimtype False; abstraction
 | |- ~ _ => intro; abstraction
 | H1: ~?x <<< ?y, H2: ?x =/= ?y |- _ =>
     generalize (le_neq H1 H2); clear H1 H2; intro; abstraction
 | H1: ~?x <<< ?y, H2: ?y =/= ?x |- _ =>
     symmetry in H2; generalize (le_neq H1 H2);
       clear H1 H2; intro; abstraction
 | H : ?x =/= ?y |- _ => revert H; abstraction
 | H : ~?x <<< ?y |- _ => revert H; abstraction
 | H : ?x <<< ?y |- _ => revert H; abstraction
 | H : ?x === ?y |- _ => revert H; abstraction
 | _ => idtac
end.

Ltac do_eq a b EQ := match goal with
 | |- ?x <<< ?y -> _ => let H := fresh "H" in
     (intro H;
      (generalize (eq_lt EQ H); clear H; intro H) ||
      (generalize (lt_eq H EQ); clear H; intro H) ||
      idtac);
      do_eq a b EQ
 | |- ~?x <<< ?y -> _ => let H := fresh "H" in
     (intro H;
      (generalize (eq_le (symmetry EQ) H); clear H; intro H) ||
      (generalize (le_eq H EQ); clear H; intro H) ||
      idtac);
      do_eq a b EQ
 | |- ?x === ?y -> _ => let H := fresh "H" in
     (intro H;
      (generalize (transitivity (symmetry EQ) H); clear H; intro H) ||
      (generalize (transitivity H EQ); clear H; intro H) ||
      idtac);
      do_eq a b EQ
 | |- ?x =/= ?y -> _ => let H := fresh "H" in
     (intro H;
      (generalize (eq_neq (symmetry EQ) H); clear H; intro H) ||
      (generalize (neq_eq H EQ); clear H; intro H) ||
      idtac);
      do_eq a b EQ
 | |- a <<< ?y => apply eq_lt with b; [exact (symmetry EQ)|]
 | |- ?y <<< a => apply lt_eq with b; [|exact (symmetry EQ)]
 | |- a === ?y => transitivity b; [exact EQ|]
 | |- ?y === a => transitivity b; [|exact (symmetry EQ)]
 | _ => idtac
 end.

Ltac propagate_eq := abstraction; match goal with
 | |- ?a === ?b -> _ =>
     let EQ := fresh "EQ" in (intro EQ; do_eq a b EQ; clear EQ);
     propagate_eq
 | _ => idtac
end.

(* Example test `{OrderedType A} : *)
(*   forall (x x' x'' x''' y a b c d e f g h : A), *)
(*     x === x -> x === x' -> x' === x'' -> *)
(*     x =/= y -> b =/= x -> *)
(*     y >>> x -> c <<< x -> *)
(*     x'' === x''' -> *)
(*     ~a >>> x -> ~d <<< x -> *)
(*     e === x -> x === e -> *)
(*     f >>> x. *)
(* Proof. *)
(*   intros. *)
(*   propagate_eq. *)

Ltac do_lt x y LT := match goal with
 | |- x <<< y -> _ => intros _; do_lt x y LT
 | |- y <<< ?z -> _ => let H := fresh "H" in
     (intro H; generalize (transitivity LT H); intro); do_lt x y LT
 | |- ?z <<< x -> _ => let H := fresh "H" in
     (intro H; generalize (transitivity H LT); intro); do_lt x y LT
 | |- _ <<< _ -> _ => intro; do_lt x y LT

 | |- ~y <<< x -> _ => intros _; do_lt x y LT
 | |- ~x <<< ?z -> _ => let H := fresh "H" in
     (intro H; generalize (le_lt_trans H LT); intro); do_lt x y LT
 | |- ~?z <<< y -> _ => let H := fresh "H" in
     (intro H; generalize (lt_le_trans LT H); intro); do_lt x y LT
 | |- ~_ <<< _ -> _ => intro; do_lt x y LT
 | _ => idtac
 end.

Definition hide_lt `{StrictOrder A lt_ eq_} := lt_StrictOrder.

Ltac propagate_lt := abstraction; match goal with
 | |- ?x <<< ?y -> _ =>
     let LT := fresh "LT" in
       (intro LT; do_lt x y LT; change (hide_lt x y) in LT);
       propagate_lt
 | _ => unfold hide_lt in *
end.

Ltac order :=
 intros;
 normalize_notations;
 abstraction;
 propagate_eq;
 propagate_lt;
 auto;
 propagate_lt;
 eauto.

Ltac false_order := elimtype False; order.

Hint Extern 0 (_eq _ _) => reflexivity.
Hint Extern 0 (_ === _) => reflexivity.
Hint Extern 2 (_eq _ _) => symmetry; assumption.
Hint Extern 2 (_ === _) => symmetry; assumption.
Hint Extern 1 (Equivalence _) => constructor; congruence.
Hint Extern 1 (Equivalence _) => apply OT_Equivalence.
Hint Extern 1 (StrictOrder _) => apply OT_StrictOrder.
Hint Extern 1 (RelationClasses.StrictOrder _) =>
  constructor; repeat intro; order.
Hint Extern 1 (Proper _ _) => apply lt_m.
Hint Extern 1 (Proper _ _) => repeat intro; intuition order.

(** ** Specific Ordered types : [OrderedType] with specific equality

   Sometimes, one wants to consider ordered types where the equality
   has to be Leibniz equality or any other specific equality. Because there
   is no 'with' construct for  typeclasses, as there is for modules, we
   define another class for these types and show that such types
   also match [OrderedType]. An alternative would be to take the equality
   relation ouf of the [OrderedType] instance and add it as a parameter.
*)
Class SpecificOrderedType
  (A : Type) (eqA : relation A) := {
  SOT_Equivalence :> Equivalence eqA ;
  SOT_lt : relation A;
  SOT_StrictOrder : StrictOrder SOT_lt eqA;
  SOT_cmp : A -> A -> comparison;
  SOT_compare_spec : forall x y, compare_spec eqA SOT_lt x y (SOT_cmp x y)
}.
Instance SOT_as_OT `{SpecificOrderedType A} : OrderedType A := {
  _eq := eqA;
  OT_StrictOrder := SOT_StrictOrder;
  _compare_spec := SOT_compare_spec
}.
Instance SOT_SO_to_SO `{SpecificOrderedType A eqA} : StrictOrder SOT_lt eqA | 4.
Proof.
  intros; apply SOT_StrictOrder.
Defined.

(** ** Usual Ordered types : [OrderedType] with Leibniz equality

   A typical case is to require an instance of [OrderedType] where the equality
   is the Leibniz equality. We define the notation [UsualOrderedType] for that
   purpose.
   *)
Notation "'UsualOrderedType' A" :=
  (SpecificOrderedType A (@eq A))(at level 30).

(** * Facts about setoid list membership

   The remainer of this file correspond to the final section
   of the [OrderedTypeFacts] functor and the [KeyOrderedType] functor.
   They are used especially in [SetList] and [MapList].
   *)
Set Implicit Arguments. Unset Strict Implicit.
Section ForNotations.
  Require Import SetoidList.
  Notation In:=(InA _eq).
  Notation Inf:=(lelistA _lt).
  Notation Sort:=(sort _lt).
  Notation NoDup:=(NoDupA _eq).

  Context `{Helt : OrderedType elt}.
  Implicit Types x y : elt.

  Lemma In_eq : forall l x y, x === y -> In x l -> In y l.
  Proof. apply InA_eqA; eauto with typeclass_instances. Qed.

  Lemma ListIn_In : forall l x, List.In x l -> In x l.
  Proof. apply In_InA; eauto with typeclass_instances. Qed.

  Lemma Inf_lt : forall l x y, x <<< y -> Inf y l -> Inf x l.
  Proof.
    apply InfA_ltA; constructor; repeat intro; order.
  Qed.

  Lemma Inf_eq : forall l x y, x === y -> Inf y l -> Inf x l.
  Proof.
    apply InfA_eqA; eauto with typeclass_instances.
  Qed.

  Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> a <<< x.
  Proof.
    apply SortA_InfA_InA; eauto with typeclass_instances.
  Qed.

  Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> x <<< y) -> Inf x l.
  Proof. exact (@In_InfA _ _lt). Qed.

  Lemma In_Inf : forall l x, (forall y, In y l -> x <<< y) -> Inf x l.
  Proof.
    apply InA_InfA; eauto with typeclass_instances.
  Qed.

  Lemma Inf_alt :
    forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> x <<< y)).
  Proof.
    apply InfA_alt; eauto with typeclass_instances.
  Qed.

  Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
  Proof.
    apply SortA_NoDupA; eauto with typeclass_instances.
  Qed.
End ForNotations.
Unset Implicit Arguments.
Hint Resolve @ListIn_In @Sort_NoDup @Inf_lt.
Hint Immediate @In_eq @Inf_lt.

Module KeyOrderedType.
Section KeyOrderedType.
  Set Implicit Arguments.
  Unset Strict Implicit.

  Variable key : Type.
  Hypothesis (key_OT : OrderedType key).
  Variable elt : Type.

  Definition eqk (p p':key*elt) := fst p === fst p'.
  Definition eqke (p p':key*elt) :=
    fst p === fst p' /\ (snd p) = (snd p').
  Definition ltk (p p':key*elt) := fst p <<< fst p'.

  Local Instance eqk_Equiv : Equivalence eqk.
  Proof.
    constructor; repeat intro; unfold eqk in *; eauto.
    transitivity (fst y); auto.
  Qed.
  Local Instance eqke_Equiv : Equivalence eqke.
  Proof.
    constructor; repeat intro; unfold eqke in *; intuition.
    transitivity (fst y); auto.
    congruence.
  Qed.
  Local Instance ltk_SO : RelationClasses.StrictOrder ltk.
  Proof.
    constructor; repeat intro; unfold ltk in *; intuition order. 
  Qed.
  Local Instance ltk_m : Proper (eqk ==> eqk ==> iff) ltk.
  Proof.
    repeat intro; unfold ltk, eqk in *; intuition order.
  Qed.
  Ltac teauto := eauto with typeclass_instances.

  Hint Unfold eqk eqke ltk.
  Hint Extern 2 (eqke ?a ?b) => split.

  (* eqke is stricter than eqk *)
  Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
  Proof.
    unfold eqk, eqke; intuition.
  Qed.

  (* ltk ignore the second components *)
  Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
  Proof. auto. Qed.

  Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
  Proof. auto. Qed.
  Hint Immediate ltk_right_r ltk_right_l.

  (* eqk, eqke are equalities, ltk is a strict order *)
  Lemma eqk_refl : forall e, eqk e e.
  Proof. auto. Qed.

  Lemma eqke_refl : forall e, eqke e e.
  Proof. auto. Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
  Proof. auto. Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
  Proof. unfold eqke; intuition. Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
  Proof.
    intros; unfold eqk in *; auto; transitivity (fst e'); auto.
  Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
  Proof.
    unfold eqke; intuition; [ eauto | congruence ].
    transitivity (fst (a0, b0)); auto.
  Qed.

  Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
  Proof.
    intros; unfold ltk in *; auto; transitivity (fst e'); auto.
  Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
  Proof.
    unfold eqk, ltk; auto; intros; apply lt_not_eq; auto.
  Qed.

  Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
  Proof.
    unfold eqke, ltk; intuition; simpl in *; subst.
    exact (lt_not_eq H H1).
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
  Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke.
  Hint Immediate eqk_sym eqke_sym.

  (* Additionnal facts *)

  Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
  Proof.
    unfold eqk, ltk; simpl; auto.
    intros; apply eq_not_lt; auto.
  Qed.

  Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
  Proof.
    intros; unfold ltk, eqk in *; auto; order.
  Qed.

  Lemma eqk_ltk : forall e e' e'', eqk e e' -> ltk e' e'' -> ltk e e''.
  Proof.
      intros (k,e) (k',e') (k'',e'').
      unfold ltk, eqk; simpl; eauto; order.
  Qed.
  Hint Resolve eqk_not_ltk.
  Hint Immediate ltk_eqk eqk_ltk.

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.
  Hint Resolve InA_eqke_eqk.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA ltk).

  Hint Unfold MapsTo In.

  (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)
  Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
  Proof.
    firstorder.
    exists x; auto.
    induction H.
    destruct y.
    exists e; auto.
    destruct IHInA as [e H0].
    exists e; auto.
  Qed.

  Lemma MapsTo_eq : forall l x y e, x === y -> MapsTo x e l -> MapsTo y e l.
  Proof.
    intros; unfold MapsTo in *; apply InA_eqA with (x,e); teauto.
  Qed.

  Lemma In_eq : forall l x y, x === y -> In x l -> In y l.
  Proof.
    destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
  Qed.

  Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
  Proof. apply InfA_eqA; teauto. Qed.

  Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
  Proof. apply InfA_ltA; teauto. Qed.

  Hint Immediate Inf_eq.
  Hint Resolve Inf_lt.

  Lemma Sort_Inf_In :
      forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
  Proof.
    apply SortA_InfA_InA; teauto.
  Qed.

  Lemma Sort_Inf_NotIn :
      forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
  Proof.
    intros; red; intros.
    destruct H1 as [e' H2].
    elim (@ltk_not_eqk (k,e) (k,e')).
    eapply Sort_Inf_In; eauto.
    red; simpl; auto.
  Qed.

  Lemma Sort_NoDupA: forall l, Sort l -> NoDupA eqk l.
  Proof.
    apply SortA_NoDupA; teauto.
  Qed.

  Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
  Proof.
   inversion 1; intros; eapply Sort_Inf_In; eauto.
  Qed.

  Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
      ltk e e' \/ eqk e e'.
  Proof.
    inversion_clear 2; auto.
    left; apply Sort_In_cons_1 with l; auto.
  Qed.

  Lemma Sort_In_cons_3 :
    forall x l k e, Sort ((k,e)::l) -> In x l -> x =/= k.
  Proof.
    inversion_clear 1; red; intros.
    exact (Sort_Inf_NotIn H0 H1 (In_eq H2 H)).
  Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> k === k' \/ In k l.
  Proof.
    inversion 1.
    inversion_clear H0; eauto.
    destruct H1; simpl in *; intuition.
  Qed.

  Lemma In_inv_2 : forall k k' e e' l,
      InA eqk (k, e) ((k', e') :: l) -> k =/= k' -> InA eqk (k, e) l.
  Proof.
   inversion_clear 1; unfold eqk in H0; simpl in H0; order.
  Qed.

  Lemma In_inv_3 : forall x x' l,
      InA eqke x (x' :: l) -> ~eqk x x' -> InA eqke x l.
  Proof.
   inversion_clear 1; compute in H0; intuition.
  Qed.

End KeyOrderedType.
Hint Unfold eqk eqke ltk.
Hint Extern 2 (eqke ?a ?b) => split.
Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke.
Hint Immediate eqk_sym eqke_sym.
Hint Resolve eqk_not_ltk.
Hint Immediate ltk_eqk eqk_ltk.
Hint Resolve InA_eqke_eqk.
Hint Unfold MapsTo In.
Hint Immediate Inf_eq.
Hint Resolve Inf_lt.
Hint Resolve Sort_Inf_NotIn.
Hint Resolve In_inv_2 In_inv_3.

Implicit Arguments eqk [[key] [elt] [key_OT]].
Implicit Arguments eqke [[key] [elt] [key_OT]].
Implicit Arguments ltk [[key] [elt] [key_OT]].
Implicit Arguments MapsTo [[key] [elt] [key_OT]].
Implicit Arguments In [[key] [elt] [key_OT]].
End KeyOrderedType.
