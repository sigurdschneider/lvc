Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Computable Util.
Require Export CSet.

Require Export OrderedTypeEx.
Require Export MapInterface.
Open Scope map_scope.

Require MapFacts.
Module MF := MapFacts.

Require MapAVLInstance.

Notation "'[]'" := (empty _)(at level 0, no associativity) : map_scope.
Notation "M '[' key ']' " :=
  (find key M)(at level 31, left associativity) : map_scope.
Notation "M '[' key '<-' v ']' " :=
  (add key v M)(at level 29, left associativity) : map_scope.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
