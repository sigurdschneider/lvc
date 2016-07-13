Require Import MapInterface.
Require Import CMapPositive.

Generalizable All Variables.

(** The file provides an instance of [FMap] for positives.
   It also provides the corresponding instance of [FMapSpecs], ie.
   the proofs that the map operations respect their specification.
   *)

(** * [CMapPositive_FMap] : an instance of [FMap] for positives *)
Instance CMapPositive_FMap : @FMap _
  (@SOT_as_OT _ _
    PositiveOrderedTypeBitsInstance.positive_rev_OrderedType) := {
  dict := @CPositiveMap.t;
  MapsTo := @CPositiveMap.MapsTo;
  empty := @CPositiveMap.empty;
  is_empty := @CPositiveMap.is_empty;
  mem := @CPositiveMap.mem;

  add := @CPositiveMap.add;
  insert := @CPositiveMap.insert;
  adjust := @CPositiveMap.adjust;
  find := @CPositiveMap.find;
  remove := @CPositiveMap.remove;

  equal := @CPositiveMap.equal;

  map := @CPositiveMap.map;
  mapi := @CPositiveMap.mapi;
  map2 := @CPositiveMap.map2;
  fold := @CPositiveMap.fold;

  cardinal := @CPositiveMap.cardinal;
  elements := @CPositiveMap.elements;

  FMap_OrderedType := @CPositiveMap.Map_OrderedType
}.

Local Transparent map MapsTo dict mem empty is_empty add insert
  adjust remove find elements cardinal fold equal map mapi map2.

(** * [CMapPositive_FMapSpecs] : specifications for [CMapPositive_FMap] *)
Instance CMapPositive_FMapSpecs_MapsTo : FMapSpecs_MapsTo CMapPositive_FMap := {
  MapsTo_1 := CPositiveMap.MapsTo_1
}.
Instance CMapPositive_FMapSpecs_mem : FMapSpecs_mem CMapPositive_FMap := {
  mem_1 := CPositiveMap.mem_1;
  mem_2 := CPositiveMap.mem_2
}.
Instance CMapPositive_FMapSpecs_empty : FMapSpecs_empty CMapPositive_FMap := {
  empty_1 := CPositiveMap.empty_1
}.
Instance CMapPositive_FMapSpecs_is_empty :
  FMapSpecs_is_empty CMapPositive_FMap := {
  is_empty_1 := CPositiveMap.is_empty_1;
  is_empty_2 := CPositiveMap.is_empty_2
}.
Instance CMapPositive_FMapSpecs_add : FMapSpecs_add CMapPositive_FMap := {
  add_1 := CPositiveMap.add_1;
  add_2 := CPositiveMap.add_2;
  add_3 := CPositiveMap.add_3
}.
Instance CMapPositive_FMapSpecs_insert : FMapSpecs_insert CMapPositive_FMap := {
  insert_1 := CPositiveMap.insert_1;
  insert_2 := CPositiveMap.insert_2;
  insert_3 := CPositiveMap.insert_3;
  insert_4 := CPositiveMap.insert_4
}.
Instance CMapPositive_FMapSpecs_adjust : FMapSpecs_adjust CMapPositive_FMap := {
  adjust_1 := CPositiveMap.adjust_1;
  adjust_2 := CPositiveMap.adjust_2;
  adjust_3 := CPositiveMap.adjust_3
}.
Instance CMapPositive_FMapSpecs_remove : FMapSpecs_remove CMapPositive_FMap := {
  remove_1 := CPositiveMap.remove_1;
  remove_2 := CPositiveMap.remove_2;
  remove_3 := CPositiveMap.remove_3
}.
Instance CMapPositive_FMapSpecs_find : FMapSpecs_find CMapPositive_FMap := {
  find_1 := CPositiveMap.find_1;
  find_2 := CPositiveMap.find_2
}.
Instance CMapPositive_FMapSpecs_elements :
  FMapSpecs_elements CMapPositive_FMap := {
  elements_1 := CPositiveMap.elements_1;
  elements_2 := CPositiveMap.elements_2;
  elements_3 := CPositiveMap.elements_3;
  elements_3w := CPositiveMap.elements_3w
}.
Instance CMapPositive_FMapSpecs_cardinal :
  FMapSpecs_cardinal CMapPositive_FMap := {
  cardinal_1 := CPositiveMap.cardinal_1
}.
Instance CMapPositive_FMapSpecs_fold : FMapSpecs_fold CMapPositive_FMap := {
  fold_1 := CPositiveMap.fold_1
}.
Instance CMapPositive_FMapSpecs_equal : FMapSpecs_equal CMapPositive_FMap := {
  equal_1 := CPositiveMap.equal_1;
  equal_2 := CPositiveMap.equal_2
}.
Instance CMapPositive_FMapSpecs_map : FMapSpecs_map CMapPositive_FMap := {
  map_1 := CPositiveMap.map_1;
  map_2 := CPositiveMap.map_2
}.
Instance CMapPositive_FMapSpecs_mapi : FMapSpecs_mapi CMapPositive_FMap := {
  mapi_1 := CPositiveMap.mapi_1;
  mapi_2 := CPositiveMap.mapi_2
}.
Instance CMapPositive_FMapSpecs_map2 : FMapSpecs_map2 CMapPositive_FMap := {
  map2_1 := CPositiveMap.map2_1;
  map2_2 := CPositiveMap.map2_2
}.

Instance CMapPositive_FMapSpecs : FMapSpecs CMapPositive_FMap := {
  FFMapSpecs_MapsTo := CMapPositive_FMapSpecs_MapsTo;
  FFMapSpecs_mem := CMapPositive_FMapSpecs_mem;
  FFMapSpecs_empty := CMapPositive_FMapSpecs_empty;
  FFMapSpecs_is_empty := CMapPositive_FMapSpecs_is_empty;
  FFMapSpecs_add := CMapPositive_FMapSpecs_add;
  FFMapSpecs_remove := CMapPositive_FMapSpecs_remove;
  FFMapSpecs_find := CMapPositive_FMapSpecs_find;
  FFMapSpecs_elements := CMapPositive_FMapSpecs_elements;
  FFMapSpecs_cardinal := CMapPositive_FMapSpecs_cardinal;
  FFMapSpecs_fold := CMapPositive_FMapSpecs_fold;
  FFMapSpecs_equal := CMapPositive_FMapSpecs_equal;
  FFMapSpecs_map := CMapPositive_FMapSpecs_map;
  FFMapSpecs_mapi := CMapPositive_FMapSpecs_mapi;
  FFMapSpecs_map2 := CMapPositive_FMapSpecs_map2;
  FFMapSpecs_insert := CMapPositive_FMapSpecs_insert;
  FFMapSpecs_adjust := CMapPositive_FMapSpecs_adjust
}.