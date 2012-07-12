Require Import Util Val Env.

Set Implicit Arguments.

(** * Expressions *)

(* Module Type Expressions. *)
(** Assume expressions. We could pack them into a module type, but at the moment 
   this would not buy as anything. Packing things in module types only is interesting
   if the module types are instantiated; and expression are not in this development *)

  Variable exp : Type.
  Hypothesis exp_eval : env val -> exp -> option val .
  Hypothesis expOfType : onv ty -> exp -> ty -> Prop.

  Hypothesis var_to_exp : forall x:var, exp.
  Hypothesis var_to_exp_correct : forall M x,
     exp_eval M (var_to_exp x) = Some (M [x]).


(* End Expressions. *)

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)
