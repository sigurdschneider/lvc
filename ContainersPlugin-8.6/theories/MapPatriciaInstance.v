Require Import MapInterface.
Require MapPatricia.

(** The file provides an instance of [FMap] for positives implemented
   as patricia trees.
   *)

(** * [MapPatricia_FMap] : an instance of [FMap] for positives *)
Instance MapPatricia_FMap : @FMap _
  (@SOT_as_OT _ _ _ OrderedTypeEx.positive_l2r_OrderedType) := {
  dict := @MapPatricia.tree;
  MapsTo := @MapPatricia.MapsTo;
  empty := @MapPatricia.empty;
  is_empty := @MapPatricia.is_empty;
  mem := @MapPatricia.mem;

  add := @MapPatricia.add;
  insert := @MapPatricia.insert;
  adjust := @MapPatricia.adjust;
  find := @MapPatricia.find;
  remove := @MapPatricia.remove;

  equal := @MapPatricia.equal;

  map := @MapPatricia.map;
  mapi := @MapPatricia.mapi;
  map2 := @MapPatricia.map2;
  fold := @MapPatricia.fold;

  cardinal := @MapPatricia.cardinal;
  elements := @MapPatricia.elements
}.
admit.
Defined.
