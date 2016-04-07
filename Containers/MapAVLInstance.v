Require Import MapInterface.
Require MapAVL.

Generalizable All Variables.

(** The file provides an instance of [FMap] based on AVL trees.
   It also provides the corresponding instance of [FMapSpecs], ie.
   the proofs that the map operations respect their specification.
   *)

(** * [MapAVL_FMap] : an instance of [FMap] based on AVL trees *)
Instance MapAVL_FMap  `{Hkey : OrderedType key} : FMap := {
  dict := @MapAVL.dict key Hkey;
  MapsTo := @MapAVL.MapsTo key Hkey;
  empty := @MapAVL.empty key Hkey;
  is_empty := @MapAVL.is_empty key Hkey;
  mem := @MapAVL.mem key Hkey;

  add := @MapAVL.add key Hkey;
  insert := @MapAVL.insert key Hkey;
  adjust := @MapAVL.adjust key Hkey;
  find := @MapAVL.find key Hkey;
  remove := @MapAVL.remove key Hkey;

  equal := @MapAVL.equal key Hkey;

  map := @MapAVL.map key Hkey;
  mapi := @MapAVL.mapi key Hkey;
  map2 := @MapAVL.map2 key Hkey;
  fold := @MapAVL.fold key Hkey;

  cardinal := @MapAVL.cardinal key Hkey;
  elements := @MapAVL.elements key Hkey;

  FMap_OrderedType := @MapAVL.map_OrderedType key Hkey
}.

(** * [MapAVL_FMapSpecs] : specifications for [MapAVL_FMap] *)
Instance MapAVL_FMapSpecs_MapsTo `{Hkey : OrderedType key} :
  FMapSpecs_MapsTo MapAVL_FMap := {
  MapsTo_1 := @MapAVL.MapsTo_1 _ _
}.
Instance MapAVL_FMapSpecs_mem `{Helt : OrderedType elt} :
  FMapSpecs_mem MapAVL_FMap := {
  mem_1 := @MapAVL.mem_1 _ _;
  mem_2 := @MapAVL.mem_2 _ _
}.
Instance MapAVL_FMapSpecs_empty `{Helt : OrderedType elt} :
  FMapSpecs_empty MapAVL_FMap := {
  empty_1 := @MapAVL.empty_1 _ _
}.
Instance MapAVL_FMapSpecs_is_empty `{Helt : OrderedType elt} :
  FMapSpecs_is_empty MapAVL_FMap := {
  is_empty_1 := @MapAVL.is_empty_1 _ _;
  is_empty_2 := @MapAVL.is_empty_2 _ _
}.
Instance MapAVL_FMapSpecs_add `{Helt : OrderedType elt} :
  FMapSpecs_add MapAVL_FMap := {
  add_1 := @MapAVL.add_1 _ _;
  add_2 := @MapAVL.add_2 _ _;
  add_3 := @MapAVL.add_3 _ _
}.
Instance MapAVL_FMapSpecs_insert `{Helt : OrderedType elt} :
  FMapSpecs_insert MapAVL_FMap := {
  insert_1 := @MapAVL.insert_1 _ _;
  insert_2 := @MapAVL.insert_2 _ _;
  insert_3 := @MapAVL.insert_3 _ _;
  insert_4 := @MapAVL.insert_4 _ _
}.
Instance MapAVL_FMapSpecs_adjust `{Helt : OrderedType elt} :
  FMapSpecs_adjust MapAVL_FMap := {
  adjust_1 := @MapAVL.adjust_1 _ _;
  adjust_2 := @MapAVL.adjust_2 _ _;
  adjust_3 := @MapAVL.adjust_3 _ _
}.
Instance MapAVL_FMapSpecs_remove `{Helt : OrderedType elt} :
  FMapSpecs_remove MapAVL_FMap := {
  remove_1 := @MapAVL.remove_1 _ _;
  remove_2 := @MapAVL.remove_2 _ _;
  remove_3 := @MapAVL.remove_3 _ _
}.
Instance MapAVL_FMapSpecs_find `{Helt : OrderedType elt} :
  FMapSpecs_find MapAVL_FMap := {
  find_1 := @MapAVL.find_1 _ _;
  find_2 := @MapAVL.find_2 _ _
}.
Instance MapAVL_FMapSpecs_elements `{Helt : OrderedType elt} :
  FMapSpecs_elements MapAVL_FMap := {
  elements_1 := @MapAVL.elements_1 _ _;
  elements_2 := @MapAVL.elements_2 _ _;
  elements_3 := @MapAVL.elements_3 _ _;
  elements_3w := @MapAVL.elements_3w _ _
}.
Instance MapAVL_FMapSpecs_cardinal `{Helt : OrderedType elt} :
  FMapSpecs_cardinal MapAVL_FMap := {
  cardinal_1 := @MapAVL.cardinal_1 _ _
}.
Instance MapAVL_FMapSpecs_fold `{Helt : OrderedType elt} :
  FMapSpecs_fold MapAVL_FMap := {
  fold_1 := @MapAVL.fold_1 _ _
}.
Instance MapAVL_FMapSpecs_equal `{Helt : OrderedType elt} :
  FMapSpecs_equal MapAVL_FMap := {
  equal_1 := @MapAVL.equal_1 _ _;
  equal_2 := @MapAVL.equal_2 _ _
}.
Instance MapAVL_FMapSpecs_map `{Helt : OrderedType elt} :
  FMapSpecs_map MapAVL_FMap := {
  map_1 := @MapAVL.map_1 _ _;
  map_2 := @MapAVL.map_2 _ _
}.
Instance MapAVL_FMapSpecs_mapi `{Helt : OrderedType elt} :
  FMapSpecs_mapi MapAVL_FMap := {
  mapi_1 := @MapAVL.mapi_1 _ _;
  mapi_2 := @MapAVL.mapi_2 _ _
}.
Instance MapAVL_FMapSpecs_map2 `{Helt : OrderedType elt} :
  FMapSpecs_map2 MapAVL_FMap := {
  map2_1 := @MapAVL.map2_1 _ _;
  map2_2 := @MapAVL.map2_2 _ _
}.

Instance MapAVL_FMapSpecs `{Helt : OrderedType elt} :
  FMapSpecs MapAVL_FMap := {
  FFMapSpecs_MapsTo := MapAVL_FMapSpecs_MapsTo;
  FFMapSpecs_mem := MapAVL_FMapSpecs_mem;
  FFMapSpecs_empty := MapAVL_FMapSpecs_empty;
  FFMapSpecs_is_empty := MapAVL_FMapSpecs_is_empty;
  FFMapSpecs_add := MapAVL_FMapSpecs_add;
  FFMapSpecs_remove := MapAVL_FMapSpecs_remove;
  FFMapSpecs_find := MapAVL_FMapSpecs_find;
  FFMapSpecs_elements := MapAVL_FMapSpecs_elements;
  FFMapSpecs_cardinal := MapAVL_FMapSpecs_cardinal;
  FFMapSpecs_fold := MapAVL_FMapSpecs_fold;
  FFMapSpecs_equal := MapAVL_FMapSpecs_equal;
  FFMapSpecs_map := MapAVL_FMapSpecs_map;
  FFMapSpecs_mapi := MapAVL_FMapSpecs_mapi;
  FFMapSpecs_map2 := MapAVL_FMapSpecs_map2;
  FFMapSpecs_insert := MapAVL_FMapSpecs_insert;
  FFMapSpecs_adjust := MapAVL_FMapSpecs_adjust
}.
Instance MapAVL_FMapSpecificOT `{Hkey : OrderedType key} :
  FMapSpecs_SpecificOrderedType MapAVL_FMap := {
    FMap_SpecificOrderedType :=
    @MapAVL.map_SpecificOrderedType key Hkey
}.