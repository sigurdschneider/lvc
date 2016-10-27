Require Import SetInterface.
Require SetAVL.

Generalizable All Variables.

(** The file provides an instance of [FSet] based on AVL trees.
   It also provides the corresponding instance of [FSetSpecs], ie.
   the proofs that the set operations respect their specification.
   *)

(** * [SetAVL_FSet] : an instance of [FSet] based on AVL trees *)
Instance SetAVL_FSet `{Helt : OrderedType elt} : FSet := {
  set := @SetAVL.set elt Helt;
  In := @SetAVL.In elt Helt;
  empty := @SetAVL.empty elt Helt;
  is_empty := @SetAVL.is_empty elt Helt;
  mem := @SetAVL.mem elt Helt;

  add := @SetAVL.add elt Helt;
  singleton := @SetAVL.singleton elt Helt;
  remove := @SetAVL.remove elt Helt;
  union := @SetAVL.union elt Helt;
  inter := @SetAVL.inter elt Helt;
  diff := @SetAVL.diff elt Helt;

  equal := @SetAVL.equal elt Helt;
  subset := @SetAVL.subset elt Helt;

  fold := @SetAVL.fold elt Helt;

  for_all := @SetAVL.for_all elt Helt;
  exists_ := @SetAVL.exists_ elt Helt;
  filter := @SetAVL.filter elt Helt;
  partition := @SetAVL.partition elt Helt;

  cardinal := @SetAVL.cardinal elt Helt;
  elements := @SetAVL.elements elt Helt;
  choose := @SetAVL.choose elt Helt;
  min_elt := @SetAVL.min_elt elt Helt;
  max_elt := @SetAVL.max_elt elt Helt;

  FSet_OrderedType := @SetAVL.set_OrderedType elt Helt
}.

Local Transparent set In mem equal subset is_empty empty add remove
  singleton union inter diff elements fold cardinal filter for_all
  exists_ partition choose.

(** * [SetAVL_FSetSpecs] : specifications for [SetAVL_FSet] *)
Instance SetAVL_FSetSpecs_In `{Helt : OrderedType elt} :
  FSetSpecs_In SetAVL_FSet := {
  In_1 := @SetAVL.In_1 _ _
}.
Instance SetAVL_FSetSpecs_mem `{Helt : OrderedType elt} :
  FSetSpecs_mem SetAVL_FSet := {
  mem_1 := @SetAVL.mem_1 _ _;
  mem_2 := @SetAVL.mem_2 _ _
}.
Instance SetAVL_FSetSpecs_equal `{Helt : OrderedType elt} :
  FSetSpecs_equal SetAVL_FSet := {
  equal_1 := @SetAVL.equal_1 _ _;
  equal_2 := @SetAVL.equal_2 _ _
}.
Instance SetAVL_FSetSpecs_subset `{Helt : OrderedType elt} :
  FSetSpecs_subset SetAVL_FSet := {
  subset_1 := @SetAVL.subset_1 _ _;
  subset_2 := @SetAVL.subset_2 _ _
}.
Instance SetAVL_FSetSpecs_empty `{Helt : OrderedType elt} :
  FSetSpecs_empty SetAVL_FSet := {
  empty_1 := @SetAVL.empty_1 _ _
}.
Instance SetAVL_FSetSpecs_is_empty `{Helt : OrderedType elt} :
  FSetSpecs_is_empty SetAVL_FSet := {
  is_empty_1 := @SetAVL.is_empty_1 _ _;
  is_empty_2 := @SetAVL.is_empty_2 _ _
}.
Instance SetAVL_FSetSpecs_add `{Helt : OrderedType elt} :
  FSetSpecs_add SetAVL_FSet := {
  add_1 := @SetAVL.add_1 _ _;
  add_2 := @SetAVL.add_2 _ _;
  add_3 := @SetAVL.add_3 _ _
}.
Instance SetAVL_FSetSpecs_remove `{Helt : OrderedType elt} :
  FSetSpecs_remove SetAVL_FSet := {
  remove_1 := @SetAVL.remove_1 _ _;
  remove_2 := @SetAVL.remove_2 _ _;
  remove_3 := @SetAVL.remove_3 _ _
}.
Instance SetAVL_FSetSpecs_singleton `{Helt : OrderedType elt} :
  FSetSpecs_singleton SetAVL_FSet := {
  singleton_1 := @SetAVL.singleton_1 _ _;
  singleton_2 := @SetAVL.singleton_2 _ _
}.
Instance SetAVL_FSetSpecs_union `{Helt : OrderedType elt} :
  FSetSpecs_union SetAVL_FSet := {
  union_1 := @SetAVL.union_1 _ _;
  union_2 := @SetAVL.union_2 _ _;
  union_3 := @SetAVL.union_3 _ _
}.
Instance SetAVL_FSetSpecs_inter `{Helt : OrderedType elt} :
  FSetSpecs_inter SetAVL_FSet := {
  inter_1 := @SetAVL.inter_1 _ _;
  inter_2 := @SetAVL.inter_2 _ _;
  inter_3 := @SetAVL.inter_3 _ _
}.
Instance SetAVL_FSetSpecs_diff `{Helt : OrderedType elt} :
  FSetSpecs_diff SetAVL_FSet := {
  diff_1 := @SetAVL.diff_1 _ _;
  diff_2 := @SetAVL.diff_2 _ _;
  diff_3 := @SetAVL.diff_3 _ _
}.
Instance SetAVL_FSetSpecs_fold `{Helt : OrderedType elt} :
  FSetSpecs_fold SetAVL_FSet := {
  fold_1 := @SetAVL.fold_1 _ _
}.
Instance SetAVL_FSetSpecs_cardinal `{Helt : OrderedType elt} :
  FSetSpecs_cardinal SetAVL_FSet := {
  cardinal_1 := @SetAVL.cardinal_1 _ _
}.
Instance SetAVL_FSetSpecs_filter `{Helt : OrderedType elt} :
  FSetSpecs_filter SetAVL_FSet := {
  filter_1 := @SetAVL.filter_1 _ _;
  filter_2 := @SetAVL.filter_2 _ _;
  filter_3 := @SetAVL.filter_3 _ _
}.
Instance SetAVL_FSetSpecs_for_all `{Helt : OrderedType elt} :
  FSetSpecs_for_all SetAVL_FSet := {
  for_all_1 := @SetAVL.for_all_1 _ _;
  for_all_2 := @SetAVL.for_all_2 _ _
}.
Instance SetAVL_FSetSpecs_exists `{Helt : OrderedType elt} :
  FSetSpecs_exists SetAVL_FSet := {
  exists_1 := @SetAVL.exists_1 _ _;
  exists_2 := @SetAVL.exists_2 _ _
}.
Instance SetAVL_FSetSpecs_partition `{Helt : OrderedType elt} :
  FSetSpecs_partition SetAVL_FSet := {
  partition_1 := @SetAVL.partition_1 _ _;
  partition_2 := @SetAVL.partition_2 _ _
}.
Instance SetAVL_FSetSpecs_elements `{Helt : OrderedType elt} :
  FSetSpecs_elements SetAVL_FSet := {
  elements_1 := @SetAVL.elements_1 _ _;
  elements_2 := @SetAVL.elements_2 _ _;
  elements_3 := @SetAVL.elements_3 _ _;
  elements_3w := @SetAVL.elements_3w _ _
}.
Instance SetAVL_FSetSpecs_choose `{Helt : OrderedType elt} :
  FSetSpecs_choose SetAVL_FSet := {
  choose_1 := @SetAVL.choose_1 _ _;
  choose_2 := @SetAVL.choose_2 _ _;
  choose_3 := @SetAVL.choose_3 _ _
}.
Instance SetAVL_FSetSpecs_min_elt `{Helt : OrderedType elt} :
  FSetSpecs_min_elt SetAVL_FSet := {
  min_elt_1 := @SetAVL.min_elt_1 _ _;
  min_elt_2 := @SetAVL.min_elt_2 _ _;
  min_elt_3 := @SetAVL.min_elt_3 _ _
}.
Instance SetAVL_FSetSpecs_max_elt `{Helt : OrderedType elt} :
  FSetSpecs_max_elt SetAVL_FSet := {
  max_elt_1 := @SetAVL.max_elt_1 _ _;
  max_elt_2 := @SetAVL.max_elt_2 _ _;
  max_elt_3 := @SetAVL.max_elt_3 _ _
}.
Instance SetAVL_FSetSpecs `{Helt : OrderedType elt} :
  FSetSpecs SetAVL_FSet := {
  FFSetSpecs_In := SetAVL_FSetSpecs_In;
  FFSetSpecs_mem := SetAVL_FSetSpecs_mem;
  FFSetSpecs_equal := SetAVL_FSetSpecs_equal;
  FFSetSpecs_subset := SetAVL_FSetSpecs_subset;
  FFSetSpecs_empty := SetAVL_FSetSpecs_empty;
  FFSetSpecs_is_empty := SetAVL_FSetSpecs_is_empty;
  FFSetSpecs_add := SetAVL_FSetSpecs_add;
  FFSetSpecs_remove := SetAVL_FSetSpecs_remove;
  FFSetSpecs_singleton := SetAVL_FSetSpecs_singleton;
  FFSetSpecs_union := SetAVL_FSetSpecs_union;
  FFSetSpecs_inter := SetAVL_FSetSpecs_inter;
  FFSetSpecs_diff := SetAVL_FSetSpecs_diff;
  FFSetSpecs_fold := SetAVL_FSetSpecs_fold;
  FFSetSpecs_cardinal := SetAVL_FSetSpecs_cardinal;
  FFSetSpecs_filter := SetAVL_FSetSpecs_filter;
  FFSetSpecs_for_all := SetAVL_FSetSpecs_for_all;
  FFSetSpecs_exists := SetAVL_FSetSpecs_exists;
  FFSetSpecs_partition := SetAVL_FSetSpecs_partition;
  FFSetSpecs_elements := SetAVL_FSetSpecs_elements;
  FFSetSpecs_choose := SetAVL_FSetSpecs_choose;
  FFSetSpecs_min_elt := SetAVL_FSetSpecs_min_elt;
  FFSetSpecs_max_elt := SetAVL_FSetSpecs_max_elt
}.