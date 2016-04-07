Require Import SetInterface.
Require SetList.

Generalizable All Variables.

(** The file provides an instance of [FSet] based on ordered lists.
   It also provides the corresponding instance of [FSetSpecs], ie.
   the proofs that the set operations respect their specification.
   *)

(** * [SetList_FSet] : an instance of [FSet] based on ordered lists *)
Instance SetList_FSet `{Helt : OrderedType elt} : FSet := {
  set := SetList.set elt;
  In := @SetList.In elt Helt;
  empty := @SetList.empty elt Helt;
  is_empty := @SetList.is_empty elt Helt;
  mem := @SetList.mem elt Helt;

  add := @SetList.add elt Helt;
  singleton := @SetList.singleton elt Helt;
  remove := @SetList.remove elt Helt;
  union := @SetList.union elt Helt;
  inter := @SetList.inter elt Helt;
  diff := @SetList.diff elt Helt;

  equal := @SetList.equal elt Helt;
  subset := @SetList.subset elt Helt;

  fold := @SetList.fold elt Helt;

  for_all := @SetList.for_all elt Helt;
  exists_ := @SetList.exists_ elt Helt;
  filter := @SetList.filter elt Helt;
  partition := @SetList.partition elt Helt;

  cardinal := @SetList.cardinal elt Helt;
  elements := @SetList.elements elt Helt;
  choose := @SetList.choose elt Helt;
  min_elt := @SetList.min_elt elt Helt;
  max_elt := @SetList.max_elt elt Helt;

  FSet_OrderedType := @SetList.set_OrderedType elt Helt
}.

(** * [SetList_FSetSpecs] : specifications for [SetList_FSet] *)
Instance SetList_FSetSpecs_In `{Helt : OrderedType elt} :
  FSetSpecs_In SetList_FSet := {
  In_1 := @SetList.In_1 _ _
}.
Instance SetList_FSetSpecs_mem `{Helt : OrderedType elt} :
  FSetSpecs_mem SetList_FSet := {
  mem_1 := @SetList.mem_1 _ _;
  mem_2 := @SetList.mem_2 _ _
}.
Instance SetList_FSetSpecs_equal `{Helt : OrderedType elt} :
  FSetSpecs_equal SetList_FSet := {
  equal_1 := @SetList.equal_1 _ _;
  equal_2 := @SetList.equal_2 _ _
}.
Instance SetList_FSetSpecs_subset `{Helt : OrderedType elt} :
  FSetSpecs_subset SetList_FSet := {
  subset_1 := @SetList.subset_1 _ _;
  subset_2 := @SetList.subset_2 _ _
}.
Instance SetList_FSetSpecs_empty `{Helt : OrderedType elt} :
  FSetSpecs_empty SetList_FSet := {
  empty_1 := @SetList.empty_1 _ _
}.
Instance SetList_FSetSpecs_is_empty `{Helt : OrderedType elt} :
  FSetSpecs_is_empty SetList_FSet := {
  is_empty_1 := @SetList.is_empty_1 _ _;
  is_empty_2 := @SetList.is_empty_2 _ _
}.
Instance SetList_FSetSpecs_add `{Helt : OrderedType elt} :
  FSetSpecs_add SetList_FSet := {
  add_1 := @SetList.add_1 _ _;
  add_2 := @SetList.add_2 _ _;
  add_3 := @SetList.add_3 _ _
}.
Instance SetList_FSetSpecs_remove `{Helt : OrderedType elt} :
  FSetSpecs_remove SetList_FSet := {
  remove_1 := @SetList.remove_1 _ _;
  remove_2 := @SetList.remove_2 _ _;
  remove_3 := @SetList.remove_3 _ _
}.
Instance SetList_FSetSpecs_singleton `{Helt : OrderedType elt} :
  FSetSpecs_singleton SetList_FSet := {
  singleton_1 := @SetList.singleton_1 _ _;
  singleton_2 := @SetList.singleton_2 _ _
}.
Instance SetList_FSetSpecs_union `{Helt : OrderedType elt} :
  FSetSpecs_union SetList_FSet := {
  union_1 := @SetList.union_1 _ _;
  union_2 := @SetList.union_2 _ _;
  union_3 := @SetList.union_3 _ _
}.
Instance SetList_FSetSpecs_inter `{Helt : OrderedType elt} :
  FSetSpecs_inter SetList_FSet := {
  inter_1 := @SetList.inter_1 _ _;
  inter_2 := @SetList.inter_2 _ _;
  inter_3 := @SetList.inter_3 _ _
}.
Instance SetList_FSetSpecs_diff `{Helt : OrderedType elt} :
  FSetSpecs_diff SetList_FSet := {
  diff_1 := @SetList.diff_1 _ _;
  diff_2 := @SetList.diff_2 _ _;
  diff_3 := @SetList.diff_3 _ _
}.
Instance SetList_FSetSpecs_fold `{Helt : OrderedType elt} :
  FSetSpecs_fold SetList_FSet := {
  fold_1 := @SetList.fold_1 _ _
}.
Instance SetList_FSetSpecs_cardinal `{Helt : OrderedType elt} :
  FSetSpecs_cardinal SetList_FSet := {
  cardinal_1 := @SetList.cardinal_1 _ _
}.
Instance SetList_FSetSpecs_filter `{Helt : OrderedType elt} :
  FSetSpecs_filter SetList_FSet := {
  filter_1 := @SetList.filter_1 _ _;
  filter_2 := @SetList.filter_2 _ _;
  filter_3 := @SetList.filter_3 _ _
}.
Instance SetList_FSetSpecs_for_all `{Helt : OrderedType elt} :
  FSetSpecs_for_all SetList_FSet := {
  for_all_1 := @SetList.for_all_1 _ _;
  for_all_2 := @SetList.for_all_2 _ _
}.
Instance SetList_FSetSpecs_exists `{Helt : OrderedType elt} :
  FSetSpecs_exists SetList_FSet := {
  exists_1 := @SetList.exists_1 _ _;
  exists_2 := @SetList.exists_2 _ _
}.
Instance SetList_FSetSpecs_partition `{Helt : OrderedType elt} :
  FSetSpecs_partition SetList_FSet := {
  partition_1 := @SetList.partition_1 _ _;
  partition_2 := @SetList.partition_2 _ _
}.
Instance SetList_FSetSpecs_elements `{Helt : OrderedType elt} :
  FSetSpecs_elements SetList_FSet := {
  elements_1 := @SetList.elements_1 _ _;
  elements_2 := @SetList.elements_2 _ _;
  elements_3 := @SetList.elements_3 _ _;
  elements_3w := @SetList.elements_3w _ _
}.
Instance SetList_FSetSpecs_choose `{Helt : OrderedType elt} :
  FSetSpecs_choose SetList_FSet := {
  choose_1 := @SetList.choose_1 _ _;
  choose_2 := @SetList.choose_2 _ _;
  choose_3 := @SetList.choose_3 _ _
}.
Instance SetList_FSetSpecs_min_elt `{Helt : OrderedType elt} :
  FSetSpecs_min_elt SetList_FSet := {
  min_elt_1 := @SetList.min_elt_1 _ _;
  min_elt_2 := @SetList.min_elt_2 _ _;
  min_elt_3 := @SetList.min_elt_3 _ _
}.
Instance SetList_FSetSpecs_max_elt `{Helt : OrderedType elt} :
  FSetSpecs_max_elt SetList_FSet := {
  max_elt_1 := @SetList.max_elt_1 _ _;
  max_elt_2 := @SetList.max_elt_2 _ _;
  max_elt_3 := @SetList.max_elt_3 _ _
}.
Instance SetList_FSetSpecs `{Helt : OrderedType elt} :
  FSetSpecs SetList_FSet := {
  FFSetSpecs_In := SetList_FSetSpecs_In;
  FFSetSpecs_mem := SetList_FSetSpecs_mem;
  FFSetSpecs_equal := SetList_FSetSpecs_equal;
  FFSetSpecs_subset := SetList_FSetSpecs_subset;
  FFSetSpecs_empty := SetList_FSetSpecs_empty;
  FFSetSpecs_is_empty := SetList_FSetSpecs_is_empty;
  FFSetSpecs_add := SetList_FSetSpecs_add;
  FFSetSpecs_remove := SetList_FSetSpecs_remove;
  FFSetSpecs_singleton := SetList_FSetSpecs_singleton;
  FFSetSpecs_union := SetList_FSetSpecs_union;
  FFSetSpecs_inter := SetList_FSetSpecs_inter;
  FFSetSpecs_diff := SetList_FSetSpecs_diff;
  FFSetSpecs_fold := SetList_FSetSpecs_fold;
  FFSetSpecs_cardinal := SetList_FSetSpecs_cardinal;
  FFSetSpecs_filter := SetList_FSetSpecs_filter;
  FFSetSpecs_for_all := SetList_FSetSpecs_for_all;
  FFSetSpecs_exists := SetList_FSetSpecs_exists;
  FFSetSpecs_partition := SetList_FSetSpecs_partition;
  FFSetSpecs_elements := SetList_FSetSpecs_elements;
  FFSetSpecs_choose := SetList_FSetSpecs_choose;
  FFSetSpecs_min_elt := SetList_FSetSpecs_min_elt;
  FFSetSpecs_max_elt := SetList_FSetSpecs_max_elt
}.