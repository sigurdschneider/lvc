Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import SetDecide.

(* Infix "∪" := (union) (at level 60) : set_scope. *)
Notation "S '∩' T" := (inter S T) (left associativity, at level 61) : set_scope.
Notation "x '∉' s" := (~In x s) (at level 70, no associativity) : set_scope.
Notation "x '∈' s" := (In x s) (at level 70, no associativity) : set_scope.
Notation "∅" := empty : set_scope.
Notation "s '⊆' t" := (Subset s t) (at level 70, no associativity) : set_scope.
Notation "{{ x , .. , y }}" := (add x .. (add y empty) .. ) : set_scope.
Notation "⦃ X ⦄" := (set X) (format "'⦃' X '⦄'") : type_scope.
