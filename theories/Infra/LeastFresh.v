Require Import CSet Le Arith.Compare_dec.
Require Import Plus Util Map Get Take LengthEq SafeFirst.
Require Export PidgeonHole StableFresh OrderedTypeMax.

Set Implicit Arguments.


Class LeastFresh V `{NaturalRepresentation V} :=
  {
    least_fresh :> set V -> V;
    least_fresh_spec : forall G, least_fresh G ∉ G;
    least_fresh_least : forall G y, _lt y (least_fresh G) -> y ∈ G;
    least_fresh_ext : forall G G', G [=] G' -> least_fresh G = least_fresh G'
  }.

Arguments LeastFresh V {H} {H0}.
