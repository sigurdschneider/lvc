Require Import List.
Require Export Util EqDec Map Var Val.

(** *  Environments for Types and Values **)

(** ** Type Environments *)
(** Type environments are functions from var to option X for some type type X *)
Definition onv (X:Type) := var -> option X.

(** ** Value Environments *)
(** Value environments are functions from var to a value type X. *)
Definition env (X:Type) := var -> X.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa") ***
*** End: ***
*)
