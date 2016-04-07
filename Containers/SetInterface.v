Require Export OrderedType SetoidList.
Require Export Morphisms.

Generalizable All Variables.

(** This file defines the interface of typeclass-based
   finite sets *)

(** * Pointwise-equality

   We define pointwise equality for any structure with a membership
   predicate [In : elt -> container -> Prop], and prove it is an
   equivalence relation. This is required for the sets' interface.
   *)
Section Equal.
  Variable container : Type.
  Variable elt : Type.
  Variable In : elt -> container -> Prop.
  Definition Equal_pw (s s' : container) : Prop :=
    forall a : elt, In a s <-> In a s'.
  Program Definition Equal_pw_Equivalence : Equivalence Equal_pw :=
    Build_Equivalence _ _ _ _.
  Next Obligation.
    constructor; auto.
  Qed.
  Next Obligation.
    constructor; firstorder.
  Qed.
  Next Obligation.
    constructor; firstorder eauto.
  Qed.
End Equal.
Hint Unfold Equal_pw.

(** * [FSet] : the interface of sets

   We define the class [FSet] of structures that implement finite
   sets. An instance of [FSet] for an ordered type [A] contains the
   type [set A] of sets of elements of type [A]. It also contains all
   the operations that these sets support : insertion, membership,
   etc. The specifications of these operations are in a different
   class (see below).

   The operations provided are the same as in the standard [FSets]
   library.

   The last member of the class states that for any ordered type [A],
   [set A] is itself an ordered type for pointwise equality. This makes
   building sets of sets possible.
   *)
Class FSet `{OrderedType A} := {
  (** The container type *)
  set : Type;

  (** The specification of all set operations is done
     with respect to the sole membership predicate. *)
  In : A -> set -> Prop;

  (** Set Operations  *)
  empty : set;
  is_empty : set -> bool;
  mem : A -> set -> bool;

  add : A -> set -> set;
  singleton : A -> set;
  remove : A -> set -> set;
  union : set -> set -> set;
  inter : set -> set -> set;
  diff : set -> set -> set;

  equal : set -> set -> bool;
  subset : set -> set -> bool;

  fold : forall {B : Type}, (A -> B -> B) -> set -> B -> B;
  for_all : (A -> bool) -> set -> bool;
  exists_ : (A -> bool) -> set -> bool;
  filter : (A -> bool) -> set -> set;
  partition : (A -> bool) -> set -> set * set;

  cardinal : set -> nat;
  elements : set -> list A;
  choose :  set -> option A;
  min_elt :  set -> option A;
  max_elt :  set -> option A;

  (** Sets should be ordered types as well, in order to be able
     to use sets in containers. *)
  FSet_OrderedType :>
    SpecificOrderedType _ (Equal_pw set A In)
}.
Implicit Arguments set [[H] [FSet]].

(** Set notations (see below) are interpreted in scope [set_scope],
   delimited with key [scope]. We bind it to the type [set] and to
   other operations defined in the interface. *)
Delimit Scope set_scope with set.
Bind Scope set_scope with set.
Arguments Scope In [type_scope _ _ _ set_scope].
Arguments Scope is_empty [type_scope _ _ set_scope].
Arguments Scope mem [type_scope _ _ _ set_scope].
Arguments Scope add [type_scope _ _ _ set_scope].
Arguments Scope remove [type_scope _ _ _ set_scope].
Arguments Scope union [type_scope _ _ set_scope set_scope].
Arguments Scope inter [type_scope _ _ set_scope set_scope].
Arguments Scope diff [type_scope _ _ set_scope set_scope].
Arguments Scope equal [type_scope _ _ set_scope set_scope].
Arguments Scope subset [type_scope _ _ set_scope set_scope].
Arguments Scope fold [type_scope _ _ _ _ set_scope _].
Arguments Scope for_all [type_scope _ _ _ set_scope].
Arguments Scope exists_ [type_scope _ _ _ set_scope].
Arguments Scope filter [type_scope _ _ _ set_scope].
Arguments Scope partition [type_scope _ _ _ set_scope].
Arguments Scope cardinal [type_scope _ _ set_scope].
Arguments Scope elements [type_scope _ _ set_scope].
Arguments Scope choose [type_scope _ _ set_scope].
Arguments Scope min_elt [type_scope _ _ set_scope].
Arguments Scope max_elt [type_scope _ _ set_scope].

(** All projections should be made opaque for tactics using [delta]-conversion,
   otherwise the underlying instances may appear during proofs, which then
   causes several problems (notations not being used, unification failures...).
   This doesnt stop computation with [compute] or [vm_compute] though, which is
   exactly what we want.
*)
Global Opaque
  set In empty is_empty mem add singleton remove
  union inter diff equal subset fold
  for_all exists_ filter partition cardinal elements choose
  FSet_OrderedType.

(** There follow definitions of predicates about sets expressable
   in terms of [In], and which are not provided by the [FSet] class. *)
Definition Equal `{FSet elt} s s' :=
  forall a : elt, In a s <-> In a s'.
Definition Subset `{FSet elt} s s' :=
  forall a : elt, In a s -> In a s'.
Definition Empty `{FSet elt} s :=
  forall a : elt, ~ In a s.
Definition For_all `{FSet elt} (P : elt -> Prop) s :=
  forall x, In x s -> P x.
Definition Exists `{FSet elt} (P : elt -> Prop) s :=
  exists x, In x s /\ P x.

(** We also define a couple of notations for set-related operations.
   These notations can be used to avoid ambiguity when dealing
   simultaneously with operations on lists and sets that have
   similar names ([mem], [In], ...). *)
Notation "s [=] t" := (Equal s t) (at level 70, no associativity) : set_scope.
Notation "s [<=] t" := (Subset s t) (at level 70, no associativity, only parsing) : set_scope.
Notation "v '\In' S" := (In v S)(at level 70, no associativity) : set_scope.

Notation "'{}'" := (empty)(at level 0, no associativity) : set_scope.
Notation "'{' v '}'" := (singleton v) : set_scope.
Notation "'{' v ';' S '}'" := (add v S)(v at level 99) : set_scope.
Notation "'{' S '~' v '}'" := (remove v S)(S at level 99) : set_scope.
Notation "v '\in' S" := (mem v S)(at level 70, no associativity) : set_scope.
Notation "S '∪' T" := (union S T) (left associativity, at level 61) : set_scope.
Notation "S '\' T" := (diff S T) (at level 61, left associativity) : set_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** * [FSetSpecs] : finite sets' specification

   We provide the specifications of set operations in a separate class
   [FSetSpecs] parameterized by an [FSet] instance. The specifications
   are the same as in the standard [FSets.FSetInterface.S] module type,
   with the exception that compatibility hypotheses for functions used
   in [filter], [exists_], etc are replaced by morphism hypotheses,
   which can be handled by the typeclass mechanism.
   *)
Class FSetSpecs_In `(FSet A) := {
  In_1 : forall s (x y : A), x === y -> In x s -> In y s
}.
Class FSetSpecs_mem `(FSet A) := {
  mem_1 : forall s x, In x s -> mem x s = true;
  mem_2 : forall s x, mem x s = true -> In x s
}.
Class FSetSpecs_equal `(FSet A) := {
  equal_1 : forall s s', Equal s s' -> equal s s' = true;
  equal_2 : forall s s',  equal s s' = true -> Equal s s'
}.
Class FSetSpecs_subset `(FSet A) := {
  subset_1 : forall s s', Subset s s' -> subset s s' = true;
  subset_2 : forall s s', subset s s' = true -> Subset s s'
}.
Class FSetSpecs_empty `(FSet A) := {
  empty_1 : Empty empty
}.
Class FSetSpecs_is_empty `(FSet A) := {
  is_empty_1 : forall s, Empty s -> is_empty s = true;
  is_empty_2 : forall s, is_empty s = true -> Empty s
}.
Class FSetSpecs_add `(FSet A) := {
  add_1 : forall s (x y : A), x === y -> In y (add x s);
  add_2 : forall s x y, In y s -> In y (add x s);
  add_3 : forall s (x y : A), x =/= y -> In y (add x s) -> In y s
}.
Class FSetSpecs_remove `(FSet A) := {
  remove_1 : forall s (x y : A), x === y -> ~ In y (remove x s);
  remove_2 : forall s (x y : A),
    x =/= y -> In y s -> In y (remove x s);
  remove_3 : forall s x y, In y (remove x s) -> In y s
}.
Class FSetSpecs_singleton `(FSet A) := {
  singleton_1 : forall (x y : A), In y (singleton x) -> x === y;
  singleton_2 : forall (x y : A), x === y -> In y (singleton x)
}.
Class FSetSpecs_union `(FSet A) := {
  union_1 : forall s s' x,
    In x (union s s') -> In x s \/ In x s';
  union_2 : forall s s' x, In x s -> In x (union s s');
  union_3 : forall s s' x, In x s' -> In x (union s s')
}.
Class FSetSpecs_inter `(FSet A) := {
  inter_1 : forall s s' x, In x (inter s s') -> In x s;
  inter_2 : forall s s' x, In x (inter s s') -> In x s';
  inter_3 : forall s s' x,
    In x s -> In x s' -> In x (inter s s')
}.
Class FSetSpecs_diff `(FSet A) := {
  diff_1 : forall s s' x, In x (diff s s') -> In x s;
  diff_2 : forall s s' x, In x (diff s s') -> ~ In x s';
  diff_3 : forall s s' x,
    In x s -> ~ In x s' -> In x (diff s s')
}.
Class FSetSpecs_fold `(FSet A) := {
  fold_1 : forall s (B : Type) (i : B) (f : A -> B -> B),
      fold f s i = fold_left (fun a e => f e a) (elements s) i
}.
Class FSetSpecs_cardinal `(FSet A) := {
  cardinal_1 : forall s, cardinal s = length (elements s)
}.
Class FSetSpecs_filter `(FSet A) := {
  filter_1 : forall s x f `{Proper _ (_eq ==> @eq bool) f},
    In x (filter f s) -> In x s;
  filter_2 : forall s x f `{Proper _ (_eq ==> @eq bool) f},
    In x (filter f s) -> f x = true;
  filter_3 : forall s x f `{Proper _ (_eq ==> @eq bool) f},
    In x s -> f x = true -> In x (filter f s)
}.
Class FSetSpecs_for_all `(FSet A) := {
  for_all_1 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    For_all (fun x => f x = true) s -> for_all f s = true;
  for_all_2 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    for_all f s = true -> For_all (fun x => f x = true) s
}.
Class FSetSpecs_exists `(FSet A) := {
  exists_1 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    Exists (fun x => f x = true) s -> exists_ f s = true;
  exists_2 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    exists_ f s = true -> Exists (fun x => f x = true) s
}.
Class FSetSpecs_partition `(FSet A) := {
  partition_1 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    Equal (fst (partition f s)) (filter f s);
  partition_2 : forall s f `{Proper _ (_eq ==> @eq bool) f},
    Equal (snd (partition f s)) (filter (fun x => negb (f x)) s)
}.
Class FSetSpecs_elements `(FSet A) := {
  elements_1 : forall s x, In x s -> InA _eq x (elements s);
  elements_2 : forall s x, InA _eq x (elements s) -> In x s;
  elements_3 : forall s, sort _lt (elements s);
  elements_3w : forall s, NoDupA _eq (elements s)
}.
Class FSetSpecs_choose `(FSet A) := {
  choose_1 : forall s x, choose s = Some x -> In x s;
  choose_2 : forall s, choose s = None -> Empty s;
  choose_3 : forall s s' x y,
    choose s = Some x -> choose s' = Some y -> Equal s s' -> x === y
}.
Class FSetSpecs_min_elt `(FSet A) := {
  min_elt_1 : forall s x, min_elt s = Some x -> In x s;
  min_elt_2 : forall s x y,
    min_elt s = Some x -> In y s -> ~ y <<< x;
  min_elt_3 : forall s, min_elt s = None -> Empty s
}.
Class FSetSpecs_max_elt `(FSet A) := {
  max_elt_1 : forall s x, max_elt s = Some x -> In x s;
  max_elt_2 : forall s x y,
    max_elt s = Some x -> In y s -> ~ x <<< y;
  max_elt_3 : forall s, max_elt s = None -> Empty s
}.

Class FSetSpecs `(F : FSet A) := {
  FFSetSpecs_In :> FSetSpecs_In F;
  FFSetSpecs_mem :> FSetSpecs_mem F;
  FFSetSpecs_equal :> FSetSpecs_equal F;
  FFSetSpecs_subset :> FSetSpecs_subset F;
  FFSetSpecs_empty :> FSetSpecs_empty F;
  FFSetSpecs_is_empty :> FSetSpecs_is_empty F;
  FFSetSpecs_add :> FSetSpecs_add F;
  FFSetSpecs_remove :> FSetSpecs_remove F;
  FFSetSpecs_singleton :> FSetSpecs_singleton F;
  FFSetSpecs_union :> FSetSpecs_union F;
  FFSetSpecs_inter :> FSetSpecs_inter F;
  FFSetSpecs_diff :> FSetSpecs_diff F;
  FFSetSpecs_fold :> FSetSpecs_fold F;
  FFSetSpecs_cardinal :> FSetSpecs_cardinal F;
  FFSetSpecs_filter :> FSetSpecs_filter F;
  FFSetSpecs_for_all :> FSetSpecs_for_all F;
  FFSetSpecs_exists :> FSetSpecs_exists F;
  FFSetSpecs_partition :> FSetSpecs_partition F;
  FFSetSpecs_elements :> FSetSpecs_elements F;
  FFSetSpecs_choose :> FSetSpecs_choose F;
  FFSetSpecs_min_elt :> FSetSpecs_min_elt F;
  FFSetSpecs_max_elt :> FSetSpecs_max_elt F
}.
(* About FSetSpecs. *)

(* Because of a bug (or limitation, depending on your leniency)
   of interaction between hints and implicit typeclasses parameters
   we define aliases to add as hints. *)
Definition zmem_1 `{H : @FSetSpecs A HA F} :=
  @mem_1 _ _ _ (@FFSetSpecs_mem _ _ _ H).
Definition zequal_1 `{H : @FSetSpecs A HA F} :=
  @equal_1 _ _ _ (@FFSetSpecs_equal _ _ _ H).
Definition zsubset_1 `{H : @FSetSpecs A HA F} :=
  @subset_1 _ _ _ (@FFSetSpecs_subset _ _ _ H).
Definition zempty_1 `{H : @FSetSpecs A HA F} :=
  @empty_1 _ _ _ (@FFSetSpecs_empty _ _ _ H).
Definition zis_empty_1 `{H : @FSetSpecs A HA F} :=
  @is_empty_1 _ _ _ (@FFSetSpecs_is_empty _ _ _ H).
Definition zchoose_1 `{H : @FSetSpecs A HA F} :=
  @choose_1 _ _ _ (@FFSetSpecs_choose _ _ _ H).
Definition zchoose_2 `{H : @FSetSpecs A HA F} :=
  @choose_2 _ _ _ (@FFSetSpecs_choose _ _ _ H).
Definition zadd_1 `{H : @FSetSpecs A HA F} :=
  @add_1 _ _ _ (@FFSetSpecs_add _ _ _ H).
Definition zadd_2 `{H : @FSetSpecs A HA F} :=
  @add_2 _ _ _ (@FFSetSpecs_add _ _ _ H).
Definition zremove_1 `{H : @FSetSpecs A HA F} :=
  @remove_1 _ _ _ (@FFSetSpecs_remove _ _ _ H).
Definition zremove_2 `{H : @FSetSpecs A HA F} :=
  @remove_2 _ _ _ (@FFSetSpecs_remove _ _ _ H).
Definition zsingleton_2 `{H : @FSetSpecs A HA F} :=
  @singleton_2 _ _ _ (@FFSetSpecs_singleton _ _ _ H).
Definition zunion_1 `{H : @FSetSpecs A HA F} :=
  @union_1 _ _ _ (@FFSetSpecs_union _ _ _ H).
Definition zunion_2 `{H : @FSetSpecs A HA F} :=
  @union_2 _ _ _ (@FFSetSpecs_union _ _ _ H).
Definition zunion_3 `{H : @FSetSpecs A HA F} :=
  @union_3 _ _ _ (@FFSetSpecs_union _ _ _ H).
Definition zinter_3 `{H : @FSetSpecs A HA F} :=
  @inter_3 _ _ _ (@FFSetSpecs_inter _ _ _ H).
Definition zdiff_3 `{H : @FSetSpecs A HA F} :=
  @diff_3 _ _ _ (@FFSetSpecs_diff _ _ _ H).
Definition zfold_1 `{H : @FSetSpecs A HA F} :=
  @fold_1 _ _ _ (@FFSetSpecs_fold _ _ _ H).
Definition zfilter_3 `{H : @FSetSpecs A HA F} :=
  @filter_3 _ _ _ (@FFSetSpecs_filter _ _ _ H).
Definition zfor_all_1 `{H : @FSetSpecs A HA F} :=
  @for_all_1 _ _ _ (@FFSetSpecs_for_all _ _ _ H).
Definition zexists_1 `{H : @FSetSpecs A HA F} :=
  @exists_1 _ _ _ (@FFSetSpecs_exists _ _ _ H).
Definition zpartition_1 `{H : @FSetSpecs A HA F} :=
  @partition_1 _ _ _ (@FFSetSpecs_partition _ _ _ H).
Definition zpartition_2 `{H : @FSetSpecs A HA F} :=
  @partition_2 _ _ _ (@FFSetSpecs_partition _ _ _ H).
Definition zelements_1 `{H : @FSetSpecs A HA F} :=
  @elements_1 _ _ _ (@FFSetSpecs_elements _ _ _ H).
Definition zelements_3w `{H : @FSetSpecs A HA F} :=
  @elements_3w _ _ _ (@FFSetSpecs_elements _ _ _ H).
Definition zelements_3 `{H : @FSetSpecs A HA F} :=
  @elements_3 _ _ _ (@FFSetSpecs_elements _ _ _ H).

Definition zIn_1 `{H : @FSetSpecs A HA F} :=
  @In_1 _ _ _ (@FFSetSpecs_In _ _ _ H).
Definition zmem_2 `{H : @FSetSpecs A HA F} :=
  @mem_2 _ _ _ (@FFSetSpecs_mem _ _ _ H).
Definition zequal_2 `{H : @FSetSpecs A HA F} :=
  @equal_2 _ _ _ (@FFSetSpecs_equal _ _ _ H).
Definition zsubset_2 `{H : @FSetSpecs A HA F} :=
  @subset_2 _ _ _ (@FFSetSpecs_subset _ _ _ H).
Definition zis_empty_2 `{H : @FSetSpecs A HA F} :=
  @is_empty_2 _ _ _ (@FFSetSpecs_is_empty _ _ _ H).
Definition zadd_3 `{H : @FSetSpecs A HA F} :=
  @add_3 _ _ _ (@FFSetSpecs_add _ _ _ H).
Definition zremove_3 `{H : @FSetSpecs A HA F} :=
  @remove_3 _ _ _ (@FFSetSpecs_remove _ _ _ H).
Definition zsingleton_1 `{H : @FSetSpecs A HA F} :=
  @singleton_1 _ _ _ (@FFSetSpecs_singleton _ _ _ H).
Definition zinter_1 `{H : @FSetSpecs A HA F} :=
  @inter_1 _ _ _ (@FFSetSpecs_inter _ _ _ H).
Definition zinter_2 `{H : @FSetSpecs A HA F} :=
  @inter_2 _ _ _ (@FFSetSpecs_inter _ _ _ H).
Definition zdiff_1 `{H : @FSetSpecs A HA F} :=
  @diff_1 _ _ _ (@FFSetSpecs_diff _ _ _ H).
Definition zdiff_2 `{H : @FSetSpecs A HA F} :=
  @diff_2 _ _ _ (@FFSetSpecs_diff _ _ _ H).
Definition zfilter_1 `{H : @FSetSpecs A HA F} :=
  @filter_1 _ _ _ (@FFSetSpecs_filter _ _ _ H).
Definition zfilter_2 `{H : @FSetSpecs A HA F} :=
  @filter_2 _ _ _ (@FFSetSpecs_filter _ _ _ H).
Definition zfor_all_2 `{H : @FSetSpecs A HA F} :=
  @for_all_2 _ _ _ (@FFSetSpecs_for_all _ _ _ H).
Definition zexists_2 `{H : @FSetSpecs A HA F} :=
  @exists_2 _ _ _ (@FFSetSpecs_exists _ _ _ H).
Definition zelements_2 `{H : @FSetSpecs A HA F} :=
  @elements_2 _ _ _ (@FFSetSpecs_elements _ _ _ H).
Definition zmin_elt_1 `{H : @FSetSpecs A HA F} :=
  @min_elt_1 _ _ _ (@FFSetSpecs_min_elt _ _ _ H).
Definition zmin_elt_2 `{H : @FSetSpecs A HA F} :=
  @min_elt_2 _ _ _ (@FFSetSpecs_min_elt _ _ _ H).
Definition zmin_elt_3 `{H : @FSetSpecs A HA F} :=
  @min_elt_3 _ _ _ (@FFSetSpecs_min_elt _ _ _ H).
Definition zmax_elt_1 `{H : @FSetSpecs A HA F} :=
  @max_elt_1 _ _ _ (@FFSetSpecs_max_elt _ _ _ H).
Definition zmax_elt_2 `{H : @FSetSpecs A HA F} :=
  @max_elt_2 _ _ _ (@FFSetSpecs_max_elt _ _ _ H).
Definition zmax_elt_3 `{H : @FSetSpecs A HA F} :=
  @max_elt_3 _ _ _ (@FFSetSpecs_max_elt _ _ _ H).

Hint Resolve @zmem_1 @zequal_1 @zsubset_1 @zempty_1
  @zis_empty_1 @zchoose_1 @zchoose_2 @zadd_1 @zadd_2 @zremove_1
  @zremove_2 @zsingleton_2 @zunion_1 @zunion_2 @zunion_3
  @zinter_3 @zdiff_3 @zfold_1 @zfilter_3 @zfor_all_1 @zexists_1
    @zpartition_1 @zpartition_2 @zelements_1 @zelements_3w @zelements_3
    : set.
Hint Immediate @zIn_1 @zmem_2 @zequal_2 @zsubset_2 @zis_empty_2 @zadd_3
  @zremove_3 @zsingleton_1 @zinter_1 @zinter_2 @zdiff_1 @zdiff_2
  @zfilter_1 @zfilter_2 @zfor_all_2 @zexists_2 @zelements_2
    @zmin_elt_1 @zmin_elt_2 @zmin_elt_3 @zmax_elt_1 @zmax_elt_2 @zmax_elt_3
    : set.
(* Typeclasses Opaque set. *)
