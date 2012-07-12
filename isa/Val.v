Require Import Util EqDec.

Set Implicit Arguments.

(** * More or less abstract values *)
(** A file that abstacts over values and (should) provide all necessary operations. Although we concretely instantiate val to int, we maintain this file as interface between our proofs and Integer library. *)

Variable val : Type.
Variable default_val : val.

Global Instance inst_val_defaulted : Defaulted val := {
  default_el := default_val
}.

Hypothesis val_eq_dec : EqDec val eq.
(** ** There must be an injection into the booleans *)
Hypothesis val2bool : val -> bool.


Hypothesis ty : Type.

Global Instance inst_eq_dec_ty : EqDec ty eq.
Admitted.


Hypothesis valOfType : val -> ty -> Prop.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr") ***
*** End: ***
*)
