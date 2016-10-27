Require Import SetInterface.
Require SetPatricia.

(* The [FSet] instance for Patricia sets. It is specific
   to positive integers and the unnatural left-to-right ordering. *)
Instance PSet_FSet : @FSet BinPos.positive
  (@SOT_as_OT BinPos.positive _ _ OrderedTypeEx.positive_l2r_OrderedType) := {
  set := SetPatricia.tree;
  In := SetPatricia.In;
  empty := SetPatricia.empty;
  is_empty := SetPatricia.is_empty;
  mem := SetPatricia.mem;

  add := SetPatricia.add;
  singleton := SetPatricia.singleton;
  remove := SetPatricia.remove;
  union := SetPatricia.union';
  inter := SetPatricia.inter';
  diff := SetPatricia.diff';

  equal := SetPatricia.equal;
  subset := SetPatricia.subset;

  fold := SetPatricia.fold;

  for_all := SetPatricia.for_all;
  exists_ := SetPatricia.exists_;
  filter := SetPatricia.filter;
  partition := SetPatricia.partition;

  cardinal := SetPatricia.cardinal;
  elements := SetPatricia.elements;
  choose := SetPatricia.choose;
  min_elt := SetPatricia.min_elt;
  max_elt := SetPatricia.max_elt
}.
admit. (* OrderedType for In :
          requires invariant that branches are not empty *)
Defined.