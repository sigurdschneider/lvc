Require Export Containers.OrderedTypeEx SetoidList.
Require Export Morphisms.

(** This file defines the interface of typeclass-based
   finite multisets, also called finite bags *)

(** * Pointwise-equality for multisets

   We define pointwise equality for any structure with a membership
   predicate [In : elt -> container -> Prop], and prove it is an
   equivalence relation. This is required for the sets' interface.
   *)
Section MEqual.
  Variable container : Type.
  Variable elt : Type.
  Variable Mult : elt -> container -> nat.
  Definition MEqual_pw (s s' : container) : Prop :=
    forall a : elt, Mult a s = Mult a s'.
  Program Definition MEqual_pw_Equivalence : Equivalence MEqual_pw :=
    Build_Equivalence _ _ _ _.
  Next Obligation.
    constructor; auto.
  Qed.
  Next Obligation.
    firstorder.
  Qed.
  Next Obligation.
    repeat intro; rewrite H. apply H0.
  Qed.
End MEqual.
Hint Unfold MEqual_pw.

(** * [FBag] : the interface of bags

   We define the class [FBag] of structures that implement finite
   bags. An instance of [FBag] for an ordered type [A] contains the
   type [bag A] of sets of elements of type [A]. It also contains all
   the operations that these sets support : insertion, membership,
   etc. The specifications of these operations are in a different
   class (see below).
   *)
Class FBag `{OrderedType A} := {
  (** The container type *)
  bag : Type;

  (** The specification of all bag operations is done
     with respect to the multiplicity function. *)
  Mult : A -> bag -> nat;

  (** Bag Operations  *)
  empty : bag;
  is_empty : bag -> bool;
  mem : A -> bag -> bool;

  add : A -> bag -> bag;
  singleton : A -> bag;
  remove : A -> bag -> bag;
  union : bag -> bag -> bag;
  inter : bag -> bag -> bag;
  diff : bag -> bag -> bag;

  equal : bag -> bag -> bool;
  subbag : bag -> bag -> bool;

  fold : forall {B : Type}, (A -> nat -> B -> B) -> bag -> B -> B;
  for_all : (A -> bool) -> bag -> bool;
  exists_ : (A -> bool) -> bag -> bool;
  filter : (A -> bool) -> bag -> bag;
  partition : (A -> bool) -> bag -> bag * bag;

  cardinal : bag -> nat;
  elements : bag -> list (A * nat);
  choose :  bag -> option A;
  min_elt :  bag -> option A;
  max_elt :  bag -> option A;

  (** Bags should be ordered types as well, in order to be able *)
  (*  to use bags in containers. *)
  FBag_OrderedType :>
    SpecificOrderedType _ (MEqual_pw bag A Mult) (MEqual_pw_Equivalence _ _ _)
}.
Implicit Arguments bag [[H] [FBag]].

(** Bag notations (see below) are interpreted in scope [bag_scope],
   delimited with key [scope]. We bind it to the type [bag] and to
   other operations defined in the interface. *)
Delimit Scope bag_scope with bag.
Bind Scope bag_scope with bag.
Arguments Scope In [type_scope _ _ _ bag_scope].
Arguments Scope Mult [type_scope _ _ _ bag_scope].
Arguments Scope is_empty [type_scope _ _ bag_scope].
Arguments Scope mem [type_scope _ _ _ bag_scope].
Arguments Scope add [type_scope _ _ _ bag_scope].
Arguments Scope remove [type_scope _ _ _ bag_scope].
Arguments Scope union [type_scope _ _ bag_scope bag_scope].
Arguments Scope inter [type_scope _ _ bag_scope bag_scope].
Arguments Scope diff [type_scope _ _ bag_scope bag_scope].
Arguments Scope equal [type_scope _ _ bag_scope bag_scope].
Arguments Scope subbag [type_scope _ _ bag_scope bag_scope].
Arguments Scope fold [type_scope _ _ _ _ bag_scope _].
Arguments Scope for_all [type_scope _ _ _ _ bag_scope].
Arguments Scope exists_ [type_scope _ _ _ _ bag_scope].
Arguments Scope filter [type_scope _ _ _ _ bag_scope].
Arguments Scope partition [type_scope _ _ _ _ bag_scope].
Arguments Scope cardinal [type_scope _ _ bag_scope].
Arguments Scope elements [type_scope _ _ bag_scope].
Arguments Scope choose [type_scope _ _ bag_scope].
Arguments Scope min_elt [type_scope _ _ bag_scope].
Arguments Scope max_elt [type_scope _ _ bag_scope].

(** All projections should be made opaque for tactics using [delta]-conversion,
   otherwise the underlying instances may appear during proofs, which then
   causes several problems (notations not being used, unification failures...).
   This doesnt stop computation with [compute] or [vm_compute] though, which is
   exactly what we want.
*)
Global Opaque
  bag In empty is_empty mem add singleton remove
  union inter diff equal subbag fold
  for_all exists_ filter partition cardinal elements choose
  FBag_OrderedType.

(** There follow definitions of predicates about bags expressable
   in terms of [Mult], and which are not provided by the [FBag] class. *)
Definition In `{FBag elt} a s :=
  exists n, Mult a s = S n.
Definition Equal `{FBag elt} s s' :=
  forall a : elt, Mult a s = Mult a s'.
Definition Subbag `{FBag elt} s s' :=
  forall a : elt, Mult a s <= Mult a s'.
Definition Empty `{FBag elt} s :=
  forall a : elt, ~ In a s.
Definition MEmpty `{FBag elt} s :=
  forall a : elt, Mult a s = 0.
Definition For_all `{FBag elt} (P : elt -> Prop) s :=
  forall x, In x s -> P x.
Definition Exists `{FBag elt} (P : elt -> Prop) s :=
  exists x, In x s /\ P x.

(** We also define a couple of notations for bag-related operations.
   These notations can be used to avoid ambiguity when dealing
   simultaneously with operations on lists and bags that have
   similar names ([mem], [In], ...). *)
Notation "s [=] t" := (Equal s t) (at level 70, no associativity) : bag_scope.
Notation "s [<=] t" := (Subbag s t) (at level 70, no associativity) : bag_scope.
Notation "v '\In' S" := (In v S)(at level 70, no associativity) : bag_scope.
Notation "v # S" := (Mult v S)(at level 70, no associativity) : bag_scope.

Notation "'{||}'" := (empty)(at level 0, no associativity) : bag_scope.
Notation "'{|' v '|}'" := (singleton v) : bag_scope.
Notation "'{|' v ';' S '|}'" := (add v S)(v at level 99) : bag_scope.
Notation "'{|' S '~' v '|}'" := (remove v S)(S at level 99) : bag_scope.
Notation "v '\in' S" := (mem v S)(at level 70, no associativity) : bag_scope.
Notation "S '++' T" := (union S T) : bag_scope.
Notation "S '\' T" := (diff S T) (at level 60, no associativity) : bag_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** * [FBagSpecs] : finite bags' specification

   We provide the specifications of bag operations in a separate class
   [FBagSpecs] parameterized by an [FBag] instance.
   *)
Class FBagSpecs_Mult `(FBag A) := {
  Mult_1 : forall s (x y : A), x === y -> Mult x s = Mult y s
(*   In_1 : forall s (x y : A), x === y -> In x s -> In y s *)
}.
Class FBagSpecs_mem `(FBag A) := {
  mem_1 : forall s x, In x s -> mem x s = true;
  mem_2 : forall s x, mem x s = true -> In x s
}.
Class FBagSpecs_equal `(FBag A) := {
  equal_1 : forall s s', Equal s s' -> equal s s' = true;
  equal_2 : forall s s',  equal s s' = true -> Equal s s'
}.
Class FBagSpecs_subbag `(FBag A) := {
  subbag_1 : forall s s', Subbag s s' -> subbag s s' = true;
  subbag_2 : forall s s', subbag s s' = true -> Subbag s s'
}.
Class FBagSpecs_empty `(FBag A) := {
  empty_1 : MEmpty empty
}.
Class FBagSpecs_is_empty `(FBag A) := {
  is_empty_1 : forall s, MEmpty s -> is_empty s = true;
  is_empty_2 : forall s, is_empty s = true -> MEmpty s
}.
Class FBagSpecs_add `(FBag A) := {
  add_mult : forall s (x y : A), Mult x (add y s) =
    if x == y then S (Mult x s) else Mult x s
(*   add_1 : forall s (x y : A), x === y -> In y (add x s); *)
(*   add_2 : forall s x y, In y s -> In y (add x s); *)
(*   add_3 : forall s (x y : A), x =/= y -> In y (add x s) -> In y s *)
}.
Class FBagSpecs_remove `(FBag A) := {
  remove_mult : forall s (x y : A), Mult x (remove y s) =
    if x == y then pred (Mult x s) else Mult x s
(*   remove_1 : forall s (x y : A), x === y -> ~ In y (remove x s); *)
(*   remove_2 : forall s (x y : A), *)
(*     x =/= y -> In y s -> In y (remove x s); *)
(*   remove_3 : forall s x y, In y (remove x s) -> In y s *)
}.
Class FBagSpecs_singleton `(FBag A) := {
  singleton_mult : forall s (x y : A), Mult x s =
    if x == y then 1 else 0
(*   singleton_1 : forall (x y : A), In y (singleton x) -> x === y; *)
(*   singleton_2 : forall (x y : A), x === y -> In y (singleton x) *)
}.
Class FBagSpecs_union `(FBag A) := {
  union_mult : forall s s' x, Mult x (union s s') = Mult x s + Mult x s'
(*   union_1 : forall s s' x, *)
(*     In x (union s s') -> In x s \/ In x s'; *)
(*   union_2 : forall s s' x, In x s -> In x (union s s'); *)
(*   union_3 : forall s s' x, In x s' -> In x (union s s') *)
}.
Require Import Min.
Class FBagSpecs_inter `(FBag A) := {
  inter_mult : forall s s' x, Mult x (inter s s') = min (Mult x s) (Mult x s')
(*   inter_1 : forall s s' x, In x (inter s s') -> In x s; *)
(*   inter_2 : forall s s' x, In x (inter s s') -> In x s'; *)
(*   inter_3 : forall s s' x, *)
(*     In x s -> In x s' -> In x (inter s s') *)
}.
Class FBagSpecs_diff `(FBag A) := {
  diff_mult : forall s s' x, Mult x (diff s s') = Mult x s - Mult x s'
(*   diff_1 : forall s s' x, In x (diff s s') -> In x s; *)
(*   diff_2 : forall s s' x, In x (diff s s') -> ~ In x s'; *)
(*   diff_3 : forall s s' x, *)
(*     In x s -> ~ In x s' -> In x (diff s s') *)
}.
Class FBagSpecs_fold `(FBag A) := {
  fold_1 : forall s (B : Type) (i : B) (f : A -> nat -> B -> B),
      fold f s i = fold_left (fun a en => f (fst en) (snd en) a) (elements s) i
}.
Class FBagSpecs_cardinal `(FBag A) := {
  cardinal_1 : forall s, cardinal s = length (elements s)
}.
Class FBagSpecs_filter `(FBag A) := {
  filter_mult_1 : forall s x f `{Morphism _ (_eq ==> @eq bool) f},
    In x (filter f s) -> Mult x (filter f s) = Mult x s;
  filter_mult_2 : forall s x f `{Morphism _ (_eq ==> @eq bool) f},
    In x (filter f s) -> f x = true;
  filter_mult_3 : forall s x f `{Morphism _ (_eq ==> @eq bool) f},
    f x = true -> Mult x s = Mult x (filter f s)
(*   filter_1 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     In x (filter f s) -> In x s; *)
(*   filter_2 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     In x (filter f s) -> f x = true; *)
(*   filter_3 : forall s x f `{Morphism _ (_eq ==> @eq bool) f}, *)
(*     In x s -> f x = true -> In x (filter f s) *)
}.
Class FBagSpecs_for_all `(FBag A) := {
  for_all_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    For_all (fun x => f x = true) s -> for_all f s = true;
  for_all_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    for_all f s = true -> For_all (fun x => f x = true) s
}.
Class FBagSpecs_exists `(FBag A) := {
  exists_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    Exists (fun x => f x = true) s -> exists_ f s = true;
  exists_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    exists_ f s = true -> Exists (fun x => f x = true) s
}.
Class FBagSpecs_partition `(FBag A) := {
  partition_1 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    Equal (fst (partition f s)) (filter f s);
  partition_2 : forall s f `{Morphism _ (_eq ==> @eq bool) f},
    Equal (snd (partition f s)) (filter (fun x => negb (f x)) s)
}.
Class FBagSpecs_elements `(FBag A) := {
  elements_1 : forall s x, In x s -> InA _eq (x, Mult x s) (elements s);
  elements_2 : forall s x n, InA _eq (x, n) (elements s) -> Mult x s =  n;
  elements_3 : forall s, sort _lt (elements s);
  elements_3w : forall s, NoDupA _eq (elements s)
}.
Class FBagSpecs_choose `(FBag A) := {
  choose_1 : forall s x, choose s = Some x -> In x s;
  choose_2 : forall s, choose s = None -> Empty s;
  choose_3 : forall s s' x y,
    choose s = Some x -> choose s' = Some y -> Equal s s' -> x === y
}.
Class FBagSpecs_min_elt `(FBag A) := {
  min_elt_1 : forall s x, min_elt s = Some x -> In x s;
  min_elt_2 : forall s x y,
    min_elt s = Some x -> In y s -> ~ y <<< x;
  min_elt_3 : forall s, min_elt s = None -> Empty s
}.
Class FBagSpecs_max_elt `(FBag A) := {
  max_elt_1 : forall s x, max_elt s = Some x -> In x s;
  max_elt_2 : forall s x y,
    max_elt s = Some x -> In y s -> ~ x <<< y;
  max_elt_3 : forall s, max_elt s = None -> Empty s
}.

Class FBagSpecs `(F : FBag A) := {
  FFBagSpecs_Mult :> FBagSpecs_Mult F;
  FFBagSpecs_mem :> FBagSpecs_mem F;
  FFBagSpecs_equal :> FBagSpecs_equal F;
  FFBagSpecs_subbag :> FBagSpecs_subbag F;
  FFBagSpecs_empty :> FBagSpecs_empty F;
  FFBagSpecs_is_empty :> FBagSpecs_is_empty F;
  FFBagSpecs_add :> FBagSpecs_add F;
  FFBagSpecs_remove :> FBagSpecs_remove F;
  FFBagSpecs_singleton :> FBagSpecs_singleton F;
  FFBagSpecs_union :> FBagSpecs_union F;
  FFBagSpecs_inter :> FBagSpecs_inter F;
  FFBagSpecs_diff :> FBagSpecs_diff F;
  FFBagSpecs_fold :> FBagSpecs_fold F;
  FFBagSpecs_cardinal :> FBagSpecs_cardinal F;
  FFBagSpecs_filter :> FBagSpecs_filter F;
  FFBagSpecs_for_all :> FBagSpecs_for_all F;
  FFBagSpecs_exists :> FBagSpecs_exists F;
  FFBagSpecs_partition :> FBagSpecs_partition F;
  FFBagSpecs_elements :> FBagSpecs_elements F;
  FFBagSpecs_choose :> FBagSpecs_choose F;
  FFBagSpecs_min_elt :> FBagSpecs_min_elt F;
  FFBagSpecs_max_elt :> FBagSpecs_max_elt F
}.
(* About FBagSpecs. *)

(* Because of a bug (or limitation, depending on your leniency)
   of interaction between hints and implicit typeclasses parameters
   we define aliases to add as hints. *)
Definition zmem_1 `{H : @FBagSpecs A HA F} :=
  @mem_1 _ _ _ (@FFBagSpecs_mem _ _ _ H).
Definition zequal_1 `{H : @FBagSpecs A HA F} :=
  @equal_1 _ _ _ (@FFBagSpecs_equal _ _ _ H).
Definition zsubbag_1 `{H : @FBagSpecs A HA F} :=
  @subbag_1 _ _ _ (@FFBagSpecs_subbag _ _ _ H).
Definition zempty_1 `{H : @FBagSpecs A HA F} :=
  @empty_1 _ _ _ (@FFBagSpecs_empty _ _ _ H).
Definition zis_empty_1 `{H : @FBagSpecs A HA F} :=
  @is_empty_1 _ _ _ (@FFBagSpecs_is_empty _ _ _ H).
Definition zchoose_1 `{H : @FBagSpecs A HA F} :=
  @choose_1 _ _ _ (@FFBagSpecs_choose _ _ _ H).
Definition zchoose_2 `{H : @FBagSpecs A HA F} :=
  @choose_2 _ _ _ (@FFBagSpecs_choose _ _ _ H).
Definition zadd_mult `{H : @FBagSpecs A HA F} :=
  @add_mult _ _ _ (@FFBagSpecs_add _ _ _ H).
Definition zremove_mult `{H : @FBagSpecs A HA F} :=
  @remove_mult _ _ _ (@FFBagSpecs_remove _ _ _ H).
Definition zsingleton_mult `{H : @FBagSpecs A HA F} :=
  @singleton_mult _ _ _ (@FFBagSpecs_singleton _ _ _ H).
Definition zunion_mult `{H : @FBagSpecs A HA F} :=
  @union_mult _ _ _ (@FFBagSpecs_union _ _ _ H).
Definition zinter_mult `{H : @FBagSpecs A HA F} :=
  @inter_mult _ _ _ (@FFBagSpecs_inter _ _ _ H).
Definition zdiff_mult `{H : @FBagSpecs A HA F} :=
  @diff_mult _ _ _ (@FFBagSpecs_diff _ _ _ H).
Definition zfold_1 `{H : @FBagSpecs A HA F} :=
  @fold_1 _ _ _ (@FFBagSpecs_fold _ _ _ H).
Definition zfilter_mult_3 `{H : @FBagSpecs A HA F} :=
  @filter_mult_3 _ _ _ (@FFBagSpecs_filter _ _ _ H).
Definition zfor_all_1 `{H : @FBagSpecs A HA F} :=
  @for_all_1 _ _ _ (@FFBagSpecs_for_all _ _ _ H).
Definition zexists_1 `{H : @FBagSpecs A HA F} :=
  @exists_1 _ _ _ (@FFBagSpecs_exists _ _ _ H).
Definition zpartition_1 `{H : @FBagSpecs A HA F} :=
  @partition_1 _ _ _ (@FFBagSpecs_partition _ _ _ H).
Definition zpartition_2 `{H : @FBagSpecs A HA F} :=
  @partition_2 _ _ _ (@FFBagSpecs_partition _ _ _ H).
Definition zelements_1 `{H : @FBagSpecs A HA F} :=
  @elements_1 _ _ _ (@FFBagSpecs_elements _ _ _ H).
Definition zelements_3w `{H : @FBagSpecs A HA F} :=
  @elements_3w _ _ _ (@FFBagSpecs_elements _ _ _ H).
Definition zelements_3 `{H : @FBagSpecs A HA F} :=
  @elements_3 _ _ _ (@FFBagSpecs_elements _ _ _ H).

Definition zMult_1 `{H : @FBagSpecs A HA F} :=
  @Mult_1 _ _ _ (@FFBagSpecs_Mult _ _ _ H).
Definition zmem_2 `{H : @FBagSpecs A HA F} :=
  @mem_2 _ _ _ (@FFBagSpecs_mem _ _ _ H).
Definition zequal_2 `{H : @FBagSpecs A HA F} :=
  @equal_2 _ _ _ (@FFBagSpecs_equal _ _ _ H).
Definition zsubbag_2 `{H : @FBagSpecs A HA F} :=
  @subbag_2 _ _ _ (@FFBagSpecs_subbag _ _ _ H).
Definition zis_empty_2 `{H : @FBagSpecs A HA F} :=
  @is_empty_2 _ _ _ (@FFBagSpecs_is_empty _ _ _ H).
Definition zfor_all_2 `{H : @FBagSpecs A HA F} :=
  @for_all_2 _ _ _ (@FFBagSpecs_for_all _ _ _ H).
Definition zexists_2 `{H : @FBagSpecs A HA F} :=
  @exists_2 _ _ _ (@FFBagSpecs_exists _ _ _ H).
Definition zelements_2 `{H : @FBagSpecs A HA F} :=
  @elements_2 _ _ _ (@FFBagSpecs_elements _ _ _ H).
Definition zmin_elt_1 `{H : @FBagSpecs A HA F} :=
  @min_elt_1 _ _ _ (@FFBagSpecs_min_elt _ _ _ H).
Definition zmin_elt_2 `{H : @FBagSpecs A HA F} :=
  @min_elt_2 _ _ _ (@FFBagSpecs_min_elt _ _ _ H).
Definition zmin_elt_3 `{H : @FBagSpecs A HA F} :=
  @min_elt_3 _ _ _ (@FFBagSpecs_min_elt _ _ _ H).
Definition zmax_elt_1 `{H : @FBagSpecs A HA F} :=
  @max_elt_1 _ _ _ (@FFBagSpecs_max_elt _ _ _ H).
Definition zmax_elt_2 `{H : @FBagSpecs A HA F} :=
  @max_elt_2 _ _ _ (@FFBagSpecs_max_elt _ _ _ H).
Definition zmax_elt_3 `{H : @FBagSpecs A HA F} :=
  @max_elt_3 _ _ _ (@FFBagSpecs_max_elt _ _ _ H).

Hint Resolve @zmem_1 @zequal_1 @zsubbag_1 @zempty_1
  @zis_empty_1 @zchoose_1 @zchoose_2 @zadd_mult @zremove_mult
  @zsingleton_mult @zunion_mult @zinter_mult @zdiff_mult
  @zfold_1 @zfilter_mult_3 @zfor_all_1 @zexists_1
    @zpartition_1 @zpartition_2 @zelements_1 @zelements_3w @zelements_3
    : bag.
Hint Immediate @zMult_1 @zmem_2 @zequal_2 @zsubbag_2 @zis_empty_2
  @zfor_all_2 @zexists_2 @zelements_2
  @zmin_elt_1 @zmin_elt_2 @zmin_elt_3 @zmax_elt_1 @zmax_elt_2 @zmax_elt_3
  : bag.
Typeclasses Opaque bag.