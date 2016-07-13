Require Import BagInterface Containers.Maps BagMap.

Instance Map_FBag `{OrderedType A} : FBag := {
  bag := bag;
  Mult := Mult;

  empty := empty;
  is_empty := is_empty;
  mem := mem;

  add := add;
  singleton := singleton;
  remove := remove;
  union := union;
  inter := inter;
  diff := diff;

  equal := equal;
  subbag := subbag;

  fold := @fold A _ _;
  for_all := for_all;
  exists_ := exists_;
  filter := filter;
  partition := partition;

  cardinal := cardinal;
  elements := elements;
  choose := choose;
  min_elt := min_elt;
  max_elt := max_elt
}.
Proof.
  admit.
Defined.

Instance Map_FBag_FBagSpecs `{Helt : OrderedType elt} : FBagSpecs Map_FBag.
admit.
Qed.