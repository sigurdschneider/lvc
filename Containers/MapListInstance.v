Require Import MapInterface.
Require MapList.

Generalizable All Variables.

(** The file provides an instance of [FMap] based on sorted lists.
   It also provides the corresponding instance of [FMapSpecs], ie.
   the proofs that the map operations respect their specification.
   *)

(** * [MapList_FMap] : an instance of [FMap] based on List trees *)
Instance MapList_FMap  `{Hkey : OrderedType key} : FMap := {
  dict := @MapList.dict key Hkey;
  MapsTo := @MapList.MapsTo key Hkey;
  empty := @MapList.empty key Hkey;
  is_empty := @MapList.is_empty key Hkey;
  mem := @MapList.mem key Hkey;

  add := @MapList.add key Hkey;
  insert := @MapList.insert key Hkey;
  adjust := @MapList.adjust key Hkey;
  find := @MapList.find key Hkey;
  remove := @MapList.remove key Hkey;

  equal := @MapList.equal key Hkey;

  map := @MapList.map key Hkey;
  mapi := @MapList.mapi key Hkey;
  map2 := @MapList.map2 key Hkey;
  fold := @MapList.fold key Hkey;

  cardinal := @MapList.cardinal key Hkey;
  elements := @MapList.elements key Hkey;

  FMap_OrderedType := @MapList.map_OrderedType key Hkey
}.

(** * [MapList_FMapSpecs] : specifications for [MapList_FMap] *)
Instance MapList_FMapSpecs_MapsTo `{Hkey : OrderedType key} :
  FMapSpecs_MapsTo MapList_FMap := {
  MapsTo_1 := @MapList.MapsTo_1 _ _
}.
Instance MapList_FMapSpecs_mem `{Helt : OrderedType elt} :
  FMapSpecs_mem MapList_FMap := {
  mem_1 := @MapList.mem_1 _ _;
  mem_2 := @MapList.mem_2 _ _
}.
Instance MapList_FMapSpecs_empty `{Helt : OrderedType elt} :
  FMapSpecs_empty MapList_FMap := {
  empty_1 := @MapList.empty_1 _ _
}.
Instance MapList_FMapSpecs_is_empty `{Helt : OrderedType elt} :
  FMapSpecs_is_empty MapList_FMap := {
  is_empty_1 := @MapList.is_empty_1 _ _;
  is_empty_2 := @MapList.is_empty_2 _ _
}.
Instance MapList_FMapSpecs_add `{Helt : OrderedType elt} :
  FMapSpecs_add MapList_FMap := {
  add_1 := @MapList.add_1 _ _;
  add_2 := @MapList.add_2 _ _;
  add_3 := @MapList.add_3 _ _
}.
Instance MapList_FMapSpecs_insert `{Helt : OrderedType elt} :
  FMapSpecs_insert MapList_FMap := {
  insert_1 := @MapList.insert_1 _ _;
  insert_2 := @MapList.insert_2 _ _;
  insert_3 := @MapList.insert_3 _ _;
  insert_4 := @MapList.insert_4 _ _
}.
Instance MapList_FMapSpecs_adjust `{Helt : OrderedType elt} :
  FMapSpecs_adjust MapList_FMap := {
  adjust_1 := @MapList.adjust_1 _ _;
  adjust_2 := @MapList.adjust_2 _ _;
  adjust_3 := @MapList.adjust_3 _ _
}.
Instance MapList_FMapSpecs_remove `{Helt : OrderedType elt} :
  FMapSpecs_remove MapList_FMap := {
  remove_1 := @MapList.remove_1 _ _;
  remove_2 := @MapList.remove_2 _ _;
  remove_3 := @MapList.remove_3 _ _
}.
Instance MapList_FMapSpecs_find `{Helt : OrderedType elt} :
  FMapSpecs_find MapList_FMap := {
  find_1 := @MapList.find_1 _ _;
  find_2 := @MapList.find_2 _ _
}.
Instance MapList_FMapSpecs_elements `{Helt : OrderedType elt} :
  FMapSpecs_elements MapList_FMap := {
  elements_1 := @MapList.elements_1 _ _;
  elements_2 := @MapList.elements_2 _ _;
  elements_3 := @MapList.elements_3 _ _;
  elements_3w := @MapList.elements_3w _ _
}.
Instance MapList_FMapSpecs_cardinal `{Helt : OrderedType elt} :
  FMapSpecs_cardinal MapList_FMap := {
  cardinal_1 := @MapList.cardinal_1 _ _
}.
Instance MapList_FMapSpecs_fold `{Helt : OrderedType elt} :
  FMapSpecs_fold MapList_FMap := {
  fold_1 := @MapList.fold_1 _ _
}.
Instance MapList_FMapSpecs_equal `{Helt : OrderedType elt} :
  FMapSpecs_equal MapList_FMap := {
  equal_1 := @MapList.equal_1 _ _;
  equal_2 := @MapList.equal_2 _ _
}.
Instance MapList_FMapSpecs_map `{Helt : OrderedType elt} :
  FMapSpecs_map MapList_FMap := {
  map_1 := @MapList.map_1 _ _;
  map_2 := @MapList.map_2 _ _
}.
Instance MapList_FMapSpecs_mapi `{Helt : OrderedType elt} :
  FMapSpecs_mapi MapList_FMap := {
  mapi_1 := @MapList.mapi_1 _ _;
  mapi_2 := @MapList.mapi_2 _ _
}.
Instance MapList_FMapSpecs_map2 `{Helt : OrderedType elt} :
  FMapSpecs_map2 MapList_FMap := {
  map2_1 := @MapList.map2_1 _ _;
  map2_2 := @MapList.map2_2 _ _
}.

Instance MapList_FMapSpecs `{Helt : OrderedType elt} :
  FMapSpecs MapList_FMap := {
  FFMapSpecs_MapsTo := MapList_FMapSpecs_MapsTo;
  FFMapSpecs_mem := MapList_FMapSpecs_mem;
  FFMapSpecs_empty := MapList_FMapSpecs_empty;
  FFMapSpecs_is_empty := MapList_FMapSpecs_is_empty;
  FFMapSpecs_add := MapList_FMapSpecs_add;
  FFMapSpecs_remove := MapList_FMapSpecs_remove;
  FFMapSpecs_find := MapList_FMapSpecs_find;
  FFMapSpecs_elements := MapList_FMapSpecs_elements;
  FFMapSpecs_cardinal := MapList_FMapSpecs_cardinal;
  FFMapSpecs_fold := MapList_FMapSpecs_fold;
  FFMapSpecs_equal := MapList_FMapSpecs_equal;
  FFMapSpecs_map := MapList_FMapSpecs_map;
  FFMapSpecs_mapi := MapList_FMapSpecs_mapi;
  FFMapSpecs_map2 := MapList_FMapSpecs_map2;
  FFMapSpecs_insert := MapList_FMapSpecs_insert;
  FFMapSpecs_adjust := MapList_FMapSpecs_adjust
}.
Instance MapList_FMapSpecificOT `{Hkey : OrderedType key} :
  FMapSpecs_SpecificOrderedType MapList_FMap := {
    FMap_SpecificOrderedType :=
    @MapList.map_SpecificOrderedType key Hkey
}.