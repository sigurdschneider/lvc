Require Export OrderedType SetoidList.
Require Import Morphisms.

Generalizable All Variables.

(** This file defines the interface of typeclass-based
   finite maps. *)

Definition Cmp {elt:Type} (cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

(** * [FMaps] : the interface of maps

   We define the class [FMap] of structures that implement finite
   maps. An instance of [FMaps] for an ordered type [key] contains a
   constructor [dict] which for any type [elt] builds the type of maps
   associating [key]s to [elt]s. It also contains all the operations
   that these structuress support : insertion, membership, etc.  The
   specifications of these operations are in a different class (see
   below).

   The operations provided are the same as in the standard [FMaps]
   library, plus two extra operations for more efficient multimaps :
   [insert] and [adjust].

   The last member of the class states that for any ordered type [key] and
   any type [elt], [dict key elt] is itself an ordered type.
   *)
Class FMap `{OrderedType key} := {
  (** the abstract type of maps *)
  dict : forall (elt : Type), Type;

  (** The specification of all map operations is done
     with respect to the sole [MapsTo] predicate. *)
  MapsTo : forall {elt : Type},
    key -> elt -> dict elt -> Prop;

  (** Map operations *)
  empty : forall (elt : Type), dict elt;
  is_empty : forall {elt : Type}, dict elt -> bool;
  mem : forall {elt : Type}, key -> dict elt -> bool;

  add : forall {elt : Type},
    key -> elt -> dict elt -> dict elt;
  find : forall {elt : Type},
    key -> dict elt -> option elt;
  remove : forall {elt : Type},
    key -> dict elt -> dict elt;

  equal : forall {elt : Type},
    (elt -> elt -> bool) -> dict elt -> dict elt -> bool;

  map : forall {elt elt' : Type},
    (elt -> elt') -> dict elt -> dict elt';
  mapi : forall {elt elt' : Type},
    (key -> elt -> elt') -> dict elt -> dict elt';
  map2 : forall {elt elt' elt'' : Type},
    (option elt -> option elt' -> option elt'') ->
    dict elt -> dict elt' ->  dict elt'';
  fold : forall {elt : Type},
    forall {A : Type}, (key -> elt -> A -> A) -> dict elt -> A -> A;

  cardinal : forall {elt : Type}, dict elt -> nat;
  elements : forall {elt : Type},
    dict elt -> list (key*elt);

  (** Extra map update operations using combining functions *)
  insert : forall {elt : Type},
    key -> elt -> (elt -> elt) -> dict elt -> dict elt;
  adjust : forall {elt : Type},
    key -> (elt -> elt) -> dict elt -> dict elt;

  (** Maps are ordered types *)
  FMap_OrderedType :> forall `{OrderedType elt}, OrderedType (dict elt)
}.
Implicit Arguments dict [[H] [FMap]].

(** Map notations (see below) are interpreted in scope [map_scope],
   delimited with key [scope]. We bind it to the type [map] and to
   other operations defined in the interface. *)
Delimit Scope map_scope with map.
Bind Scope map_scope with dict.
Arguments Scope MapsTo [type_scope _ _ type_scope _ _ map_scope].
Arguments Scope is_empty [type_scope _ _ type_scope map_scope].
Arguments Scope mem [type_scope _ _ type_scope _ map_scope].
Arguments Scope add [type_scope _ _ type_scope _ _ map_scope].
Arguments Scope find [type_scope _ _ type_scope _ map_scope].
Arguments Scope remove [type_scope _ _ type_scope _ map_scope].
Arguments Scope equal [type_scope _ _ type_scope _ map_scope map_scope].
Arguments Scope map [type_scope _ _ type_scope type_scope _ map_scope].
Arguments Scope mapi [type_scope _ _ type_scope type_scope _ map_scope].
Arguments Scope map2 [type_scope _ _ type_scope type_scope
  type_scope _ map_scope map_scope].
Arguments Scope fold [type_scope _ _ type_scope type_scope _ map_scope _].
Arguments Scope cardinal [type_scope _ _ type_scope map_scope].
Arguments Scope elements [type_scope _ _ type_scope map_scope].
Arguments Scope insert [type_scope _ _ type_scope _ _ _ map_scope].
Arguments Scope adjust [type_scope _ _ type_scope _ _ map_scope].

(** All projections should be made opaque for tactics using [delta]-conversion,
   otherwise the underlying instances may appear during proofs, which then
   causes several problems (notations not being used, unification failures...).
   This doesnt stop computation with [compute] or [vm_compute] though, which is
   exactly what we want.
*)
Global Opaque dict MapsTo empty is_empty mem add find remove
  equal map mapi map2 fold cardinal elements insert adjust (* choose *)
    FMap_OrderedType.

(** There follow definitions of predicates about maps expressable
   in terms of [MapsTo], and which are not provided by the [FMap] class. *)
Definition In  `{FMap key} {elt : Type}
  (k:key)(m: dict key elt) : Prop := exists e:elt, MapsTo k e m.

Definition Empty `{FMap key} {elt : Type} m :=
  forall (a : key)(e:elt) , ~ MapsTo a e m.

Definition eq_key  `{FMap key} {elt} := @KeyOrderedType.eqk _ _ elt.
Definition eq_key_elt `{FMap key} {elt} := @KeyOrderedType.eqke _ _ elt.
Definition lt_key `{FMap key} {elt} :=  @KeyOrderedType.ltk _ _ elt.

Definition Equal `{FMap key} {elt : Type} (m m' : dict key elt) :=
  forall y, find y m = find y m'.
Definition Equiv `{FMap key} {elt : Type} (eq_elt:elt->elt->Prop)
  (m m' : dict key elt)  :=
  (forall k, In k m <-> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
Definition Equivb `{FMap key} {elt : Type}
  (cmp: elt->elt->bool) := Equiv (Cmp cmp).

(** We also define a couple of notations for maps operations.
   New: notations other than 'Map[A,B]' must be explicitly
   imported from MapNotations since they can be incompatible
   with list notations.
   *)
Notation "'Map' '[' A ',' B ']'" :=
  (dict A B)(at level 0, no associativity).

Set Implicit Arguments.
Unset Strict Implicit.

(** * [FMapSpecs] : finite maps' specification

   We provide the specifications of map operations in a separate class
   [FMapSpecs] parameterized by an [FMap] instance. The specifications
   are the same as in the standard [FMaps.FMapInterface.S] module type.
   *)
Class FMapSpecs_MapsTo `(FMap key) := {
  MapsTo_1 : forall elt (m : Map[key,elt]) x y e,
    x === y -> MapsTo x e m -> MapsTo y e m
}.
Class FMapSpecs_mem `(FMap key) := {
  mem_1 : forall elt (m : Map[key,elt]) x,
    In x m -> mem x m = true;
  mem_2 : forall elt (m : Map[key,elt]) x,
    mem x m = true -> In x m
}.
Class FMapSpecs_empty `(FMap key) := {
  empty_1 : forall elt, Empty (empty elt)
}.
Class FMapSpecs_is_empty `(FMap key) := {
  is_empty_1 : forall elt (m : Map[key,elt]),
    Empty m -> is_empty m = true;
  is_empty_2 : forall elt (m : Map[key,elt]),
    is_empty m = true -> Empty m
}.
Class FMapSpecs_add `(FMap key) := {
  add_1 : forall elt (m : Map[key,elt]) x y e,
    x === y -> MapsTo y e (add x e m);
  add_2 : forall elt (m : Map[key,elt]) x y e e',
    x =/= y -> MapsTo y e m -> MapsTo y e (add x e' m);
  add_3 : forall elt (m : Map[key,elt]) x y e e',
    x =/= y -> MapsTo y e (add x e' m) -> MapsTo y e m
}.
Class FMapSpecs_remove `(FMap key) := {
  remove_1 : forall elt (m : Map[key,elt]) x y,
    x === y -> ~ In y (remove x m);
  remove_2 : forall elt (m : Map[key,elt]) x y e,
    x =/= y -> MapsTo y e m -> MapsTo y e (remove x m);
  remove_3 : forall elt (m : Map[key,elt]) x y e,
    MapsTo y e (remove x m) -> MapsTo y e m
}.
Class FMapSpecs_find `(FMap key) := {
  find_1 : forall elt (m : Map[key,elt]) x e,
    MapsTo x e m -> find x m = Some e;
  find_2 : forall elt (m : Map[key,elt]) x e,
    find x m = Some e -> MapsTo x e m
}.
Class FMapSpecs_elements `(FMap key) := {
  elements_1 : forall elt (m : Map[key,elt]) x e,
    MapsTo x e m -> InA eq_key_elt (x,e) (elements m);
  elements_2 : forall elt (m : Map[key,elt]) x e,
    InA eq_key_elt (x,e) (elements m) -> MapsTo x e m;
  elements_3 : forall elt (m : Map[key,elt]),
    sort lt_key (elements m);
  elements_3w : forall elt (m : Map[key,elt]),
    NoDupA eq_key (elements m)
}.
Class FMapSpecs_cardinal `(FMap key) := {
  cardinal_1 : forall elt (m : Map[key,elt]),
    cardinal m = length (elements m)
}.
Class FMapSpecs_fold `(FMap key) := {
  fold_1 : forall elt (m : Map[key,elt])
    (A : Type) (i : A) (f : key -> elt -> A -> A),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i
}.
Class FMapSpecs_equal `(FMap key) := {
  equal_1 : forall elt
    (m m' : Map[key,elt]) (cmp : elt -> elt -> bool),
    Equivb cmp m m' -> equal cmp m m' = true;
  equal_2 : forall elt
    (m m' : Map[key,elt]) (cmp : elt -> elt -> bool),
    equal cmp m m' = true -> Equivb cmp m m'
}.
Class FMapSpecs_map `(FMap key) := {
  map_1 : forall (elt elt':Type)(m: Map[key,elt])
    (x:key)(e:elt)(f:elt->elt'),
    MapsTo x e m -> MapsTo x (f e) (map f m);
  map_2 : forall (elt elt':Type)(m: Map[key,elt])
    (x:key)(f:elt->elt'),
    In x (map f m) -> In x m
}.
Class FMapSpecs_mapi `(FMap key) := {
  mapi_1 : forall (elt elt':Type)(m: Map[key,elt])
    (x:key)(e:elt) (f:key->elt->elt'), MapsTo x e m ->
    exists y, y === x /\ MapsTo x (f y e) (mapi f m);
  mapi_2 : forall (elt elt':Type)(m: Map[key,elt])
    (x:key) (f:key->elt->elt'), In x (mapi f m) -> In x m
}.
Class FMapSpecs_map2 `(FMap key) := {
  map2_1 : forall (elt elt' elt'':Type)(m: Map[key,elt]) m'
    (x:key)(f:option elt->option elt'->option elt''),
    In x m \/ In x m' ->
    find x (map2 f m m') = f (find x m) (find x m');
  map2_2 : forall (elt elt' elt'':Type)(m: Map[key,elt]) m'
    (x:key)(f:option elt->option elt'->option elt''),
    In x (map2 f m m') -> In x m \/ In x m'
}.
Class FMapSpecs_insert `(FMap key) := {
  insert_1 : forall elt (m : Map[key,elt]) x y e d f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (insert x d f m);
  insert_2 : forall elt (m : Map[key,elt]) x y d f,
    x === y -> ~ In y m -> MapsTo y d (insert x d f m);
  insert_3 : forall elt (m : Map[key,elt]) x y e d f,
    x =/= y -> MapsTo y e m -> MapsTo y e (insert x d f m);
  insert_4 : forall elt (m : Map[key,elt]) x y e d f,
    x =/= y -> MapsTo y e (insert x d f m) -> MapsTo y e m
}.
Class FMapSpecs_adjust `(FMap key) := {
  adjust_1 : forall elt (m : Map[key,elt]) x y e f,
    x === y -> MapsTo y e m -> MapsTo y (f e) (adjust x f m);
  adjust_2 : forall elt (m : Map[key,elt]) x y e f,
    x =/= y -> MapsTo y e m -> MapsTo y e (adjust x f m);
  adjust_3 : forall elt (m : Map[key,elt]) x y e f,
    x =/= y -> MapsTo y e (adjust x f m) -> MapsTo y e m
}.

Class FMapSpecs `(F : FMap key) := {
  FFMapSpecs_MapsTo :> FMapSpecs_MapsTo F;
  FFMapSpecs_mem :> FMapSpecs_mem F;
  FFMapSpecs_empty :> FMapSpecs_empty F;
  FFMapSpecs_is_empty :> FMapSpecs_is_empty F;
  FFMapSpecs_add :> FMapSpecs_add F;
  FFMapSpecs_remove :> FMapSpecs_remove F;
  FFMapSpecs_find :> FMapSpecs_find F;
  FFMapSpecs_elements :> FMapSpecs_elements F;
  FFMapSpecs_cardinal :> FMapSpecs_cardinal F;
  FFMapSpecs_fold :> FMapSpecs_fold F;
  FFMapSpecs_equal :> FMapSpecs_equal F;
  FFMapSpecs_map :> FMapSpecs_map F;
  FFMapSpecs_mapi :> FMapSpecs_mapi F;
  FFMapSpecs_map2 :> FMapSpecs_map2 F;
  FFMapSpecs_insert :> FMapSpecs_insert F;
  FFMapSpecs_adjust :> FMapSpecs_adjust F
}.
(* About Build_FMapSpecs. *)
(* About FMapSpecs. *)

(** Extra Ordering : A SpecificOrderedType for maps where the
   equality is the point-wise equality on bindings. Data
   structures who implement this ordered type should provide
   the adequate instance of this class.
   *)
Section Equal.
  Variable container : Type.
  Variable key : Type.
  Variable elt : Type.
  Variable MapsTo : key -> elt -> container -> Prop.
  Definition Equal_kw (s s' : container) : Prop :=
    forall k v, MapsTo k v s <-> MapsTo k v s'.
  Definition Equal_kw_Equivalence : Equivalence Equal_kw.
  Proof. constructor.
    constructor; auto.
    constructor; firstorder.
    constructor; unfold Equal_kw in *.
    rewrite H, H0; auto.
    rewrite H, H0; auto.
  Qed.
End Equal.
Hint Unfold Equal_kw.
Class FMapSpecs_SpecificOrderedType `(F : FMap key) := {
  FMap_SpecificOrderedType :> forall `{OrderedType elt},
    SpecificOrderedType _ (Equal_kw (elt:=elt)
      (fun k v m => exists v', v === v' /\ MapsTo k v' m))
}.

(* Aliases for hints. See SetInterface for the reason why we do that. *)
Definition zMapsTo_1 `{H : @FMapSpecs key Hkey F} :=
  @MapsTo_1 _ _ _ (@FFMapSpecs_MapsTo _ _ _ H).
Definition zmem_2 `{H : @FMapSpecs key Hkey F} :=
  @mem_2 _ _ _ (@FFMapSpecs_mem _ _ _ H).
Definition zis_empty_2 `{H : @FMapSpecs key Hkey F} :=
  @is_empty_2 _ _ _ (@FFMapSpecs_is_empty _ _ _ H).
Definition zmap_2 `{H : @FMapSpecs key Hkey F} :=
  @map_2 _ _ _ (@FFMapSpecs_map _ _ _ H).
Definition zmapi_2 `{H : @FMapSpecs key Hkey F} :=
  @mapi_2 _ _ _ (@FFMapSpecs_mapi _ _ _ H).
Definition zadd_3 `{H : @FMapSpecs key Hkey F} :=
  @add_3 _ _ _ (@FFMapSpecs_add _ _ _ H).
Definition zremove_3 `{H : @FMapSpecs key Hkey F} :=
  @remove_3 _ _ _ (@FFMapSpecs_remove _ _ _ H).
Definition zfind_2  `{H : @FMapSpecs key Hkey F} :=
  @find_2  _ _ _ (@FFMapSpecs_find _ _ _ H).
Definition zinsert_4 `{H : @FMapSpecs key Hkey F} :=
  @insert_4 _ _ _ (@FFMapSpecs_insert _ _ _ H).
Definition zadjust_3 `{H : @FMapSpecs key Hkey F} :=
  @adjust_3 _ _ _ (@FFMapSpecs_adjust _ _ _ H).
Definition zmem_1 `{H : @FMapSpecs key Hkey F} :=
  @mem_1 _ _ _ (@FFMapSpecs_mem _ _ _ H).
Definition zis_empty_1 `{H : @FMapSpecs key Hkey F} :=
  @is_empty_1 _ _ _ (@FFMapSpecs_is_empty _ _ _ H).
Definition zadd_1 `{H : @FMapSpecs key Hkey F} :=
  @add_1 _ _ _ (@FFMapSpecs_add _ _ _ H).
Definition zadd_2 `{H : @FMapSpecs key Hkey F} :=
  @add_2 _ _ _ (@FFMapSpecs_add _ _ _ H).
Definition zremove_1 `{H : @FMapSpecs key Hkey F} :=
  @remove_1 _ _ _ (@FFMapSpecs_remove _ _ _ H).
Definition zremove_2 `{H : @FMapSpecs key Hkey F} :=
  @remove_2 _ _ _ (@FFMapSpecs_remove _ _ _ H).
Definition zfind_1 `{H : @FMapSpecs key Hkey F} :=
  @find_1 _ _ _ (@FFMapSpecs_find _ _ _ H).
Definition zelements_3 `{H : @FMapSpecs key Hkey F} :=
  @elements_3 _ _ _ (@FFMapSpecs_elements _ _ _ H).
Definition zfold_1 `{H : @FMapSpecs key Hkey F} :=
  @fold_1 _ _ _ (@FFMapSpecs_fold _ _ _ H).
Definition zmap_1 `{H : @FMapSpecs key Hkey F} :=
  @map_1 _ _ _ (@FFMapSpecs_map _ _ _ H).
Definition zmapi_1 `{H : @FMapSpecs key Hkey F} :=
  @mapi_1 _ _ _ (@FFMapSpecs_mapi _ _ _ H).
Definition zinsert_1 `{H : @FMapSpecs key Hkey F} :=
  @insert_1 _ _ _ (@FFMapSpecs_insert _ _ _ H).
Definition zinsert_2 `{H : @FMapSpecs key Hkey F} :=
  @insert_2 _ _ _ (@FFMapSpecs_insert _ _ _ H).
Definition zinsert_3 `{H : @FMapSpecs key Hkey F} :=
  @insert_3 _ _ _ (@FFMapSpecs_insert _ _ _ H).
Definition zadjust_1 `{H : @FMapSpecs key Hkey F} :=
  @adjust_1 _ _ _ (@FFMapSpecs_adjust _ _ _ H).
Definition zadjust_2 `{H : @FMapSpecs key Hkey F} :=
  @adjust_2 _ _ _ (@FFMapSpecs_adjust _ _ _ H).

Hint Immediate @zMapsTo_1 @zmem_2 @zis_empty_2
  @zmap_2 @zmapi_2 @zadd_3 @zremove_3 @zfind_2
  @zinsert_4 @zadjust_3
  : map.
Hint Resolve @zmem_1 @zis_empty_1 @zis_empty_2 @zadd_1 @zadd_2 @zremove_1
  @zremove_2 @zfind_1 @zfold_1 @zmap_1 @zmapi_1 @zmapi_2
  @zinsert_1 @zinsert_2 @zinsert_3 @zadjust_1 @zadjust_2
  : map.
Hint Unfold eq_key eq_key_elt lt_key.
(* Typeclasses Opaque dict. *)