Require Import List.
Require Export Util EqDec Map Var Val.
Export BMap.

(** *  Environments for Types and Values **)

(** ** Type Environments *)
(** Value environments are functions from var to a value type X. *)
Definition onv (X:Type) := map (@None X).
Definition ompty X : onv X := @empty _ (@None X).

(** ** Value Environments *)
(** Type environments are functions from var to option X for some type type X *)
Definition env (X:Type) `{Defaulted X} := map default_el.
Definition empty (V:Type) `{Defaulted V} : env _ := empty _.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr") ***
*** End: ***
*)
