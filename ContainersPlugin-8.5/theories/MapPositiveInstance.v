Require Import MapInterface.
Require Import MapPositive.

Generalizable All Variables.

(** The file provides an instance of [FMap] for positives.
   It also provides the corresponding instance of [FMapSpecs], ie.
   the proofs that the map operations respect their specification.
   *)

(** * [MapPositive_FMap] : an instance of [FMap] for positives *)
Instance MapPositive_FMap : @FMap _
  (@SOT_as_OT _ _ OrderedTypeEx.positive_l2r_OrderedType) := {
  dict := @PositiveMap.tree;
  MapsTo := @PositiveMap.MapsTo;
  empty := @PositiveMap.empty;
  is_empty := @PositiveMap.is_empty;
  mem := @PositiveMap.mem;

  add := @PositiveMap.add;
  insert := @PositiveMap.insert;
  adjust := @PositiveMap.adjust;
  find := @PositiveMap.find;
  remove := @PositiveMap.remove;

  equal := @PositiveMap.equal;

  map := @PositiveMap.map;
  mapi := @PositiveMap.mapi;
  map2 := @PositiveMap.map2;
  fold := @PositiveMap.fold;

  cardinal := @PositiveMap.cardinal;
  elements := @PositiveMap.elements;

  FMap_OrderedType := @PositiveMap.Map_OrderedType
}.

Local Transparent map MapsTo dict mem empty is_empty add insert
  adjust remove find elements cardinal fold equal map mapi map2.

(** * [MapPositive_FMapSpecs] : specifications for [MapPositive_FMap] *)
Instance MapPositive_FMapSpecs_MapsTo : FMapSpecs_MapsTo MapPositive_FMap := {
  MapsTo_1 := PositiveMap.MapsTo_1
}.
Instance MapPositive_FMapSpecs_mem : FMapSpecs_mem MapPositive_FMap := {
  mem_1 := PositiveMap.mem_1;
  mem_2 := PositiveMap.mem_2
}.
Instance MapPositive_FMapSpecs_empty : FMapSpecs_empty MapPositive_FMap := {
  empty_1 := PositiveMap.empty_1
}.
Instance MapPositive_FMapSpecs_is_empty :
  FMapSpecs_is_empty MapPositive_FMap := {
  is_empty_1 := PositiveMap.is_empty_1;
  is_empty_2 := PositiveMap.is_empty_2
}.
Instance MapPositive_FMapSpecs_add : FMapSpecs_add MapPositive_FMap := {
  add_1 := PositiveMap.add_1;
  add_2 := PositiveMap.add_2;
  add_3 := PositiveMap.add_3
}.
Instance MapPositive_FMapSpecs_insert : FMapSpecs_insert MapPositive_FMap := {
  insert_1 := PositiveMap.insert_1;
  insert_2 := PositiveMap.insert_2;
  insert_3 := PositiveMap.insert_3;
  insert_4 := PositiveMap.insert_4
}.
Instance MapPositive_FMapSpecs_adjust : FMapSpecs_adjust MapPositive_FMap := {
  adjust_1 := PositiveMap.adjust_1;
  adjust_2 := PositiveMap.adjust_2;
  adjust_3 := PositiveMap.adjust_3
}.
Instance MapPositive_FMapSpecs_remove : FMapSpecs_remove MapPositive_FMap := {
  remove_1 := PositiveMap.remove_1;
  remove_2 := PositiveMap.remove_2;
  remove_3 := PositiveMap.remove_3
}.
Instance MapPositive_FMapSpecs_find : FMapSpecs_find MapPositive_FMap := {
  find_1 := PositiveMap.find_1;
  find_2 := PositiveMap.find_2
}.
Instance MapPositive_FMapSpecs_elements :
  FMapSpecs_elements MapPositive_FMap := {
  elements_1 := PositiveMap.elements_1;
  elements_2 := PositiveMap.elements_2;
  elements_3 := PositiveMap.elements_3;
  elements_3w := PositiveMap.elements_3w
}.
Instance MapPositive_FMapSpecs_cardinal :
  FMapSpecs_cardinal MapPositive_FMap := {
  cardinal_1 := PositiveMap.cardinal_1
}.
Instance MapPositive_FMapSpecs_fold : FMapSpecs_fold MapPositive_FMap := {
  fold_1 := PositiveMap.fold_1
}.
Instance MapPositive_FMapSpecs_equal : FMapSpecs_equal MapPositive_FMap := {
  equal_1 := PositiveMap.equal_1;
  equal_2 := PositiveMap.equal_2
}.
Instance MapPositive_FMapSpecs_map : FMapSpecs_map MapPositive_FMap := {
  map_1 := PositiveMap.map_1;
  map_2 := PositiveMap.map_2
}.
Instance MapPositive_FMapSpecs_mapi : FMapSpecs_mapi MapPositive_FMap := {
  mapi_1 := PositiveMap.mapi_1;
  mapi_2 := PositiveMap.mapi_2
}.
Instance MapPositive_FMapSpecs_map2 : FMapSpecs_map2 MapPositive_FMap := {
  map2_1 := PositiveMap.map2_1;
  map2_2 := PositiveMap.map2_2
}.

Instance MapPositive_FMapSpecs : FMapSpecs MapPositive_FMap := {
  FFMapSpecs_MapsTo := MapPositive_FMapSpecs_MapsTo;
  FFMapSpecs_mem := MapPositive_FMapSpecs_mem;
  FFMapSpecs_empty := MapPositive_FMapSpecs_empty;
  FFMapSpecs_is_empty := MapPositive_FMapSpecs_is_empty;
  FFMapSpecs_add := MapPositive_FMapSpecs_add;
  FFMapSpecs_remove := MapPositive_FMapSpecs_remove;
  FFMapSpecs_find := MapPositive_FMapSpecs_find;
  FFMapSpecs_elements := MapPositive_FMapSpecs_elements;
  FFMapSpecs_cardinal := MapPositive_FMapSpecs_cardinal;
  FFMapSpecs_fold := MapPositive_FMapSpecs_fold;
  FFMapSpecs_equal := MapPositive_FMapSpecs_equal;
  FFMapSpecs_map := MapPositive_FMapSpecs_map;
  FFMapSpecs_mapi := MapPositive_FMapSpecs_mapi;
  FFMapSpecs_map2 := MapPositive_FMapSpecs_map2;
  FFMapSpecs_insert := MapPositive_FMapSpecs_insert;
  FFMapSpecs_adjust := MapPositive_FMapSpecs_adjust
}.