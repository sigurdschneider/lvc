Require Import Util Val Env EnvTy liveness_fwd.

Set Implicit Arguments.

(** * Expressions *)

(* Module Type Expressions. *)
(** Assume expressions. We could pack them into a module type, but at the moment 
   this would not buy as anything. Packing things in module types only is interesting
   if the module types are instantiated; and expression are not in this development *)

  Variable exp : Type.
  Hypothesis exp_eval : env val -> exp -> option val .
  Hypothesis expOfType : onv ty -> exp -> ty -> Prop.
  Hypothesis expOfType_subEnv 
    : forall ET ET' e t, subEnv ET' ET -> expOfType ET' e t -> expOfType ET e t.
  Hypothesis exp_type_soundness : forall ET E e t, expOfType ET e t -> envOfType E ET ->
    { v : val & ((exp_eval E e = Some v) * valOfType v t)%type }.
  Hypothesis exp_eval_typed_eq 
    : forall ET E E' e t, typed_eq ET E E' -> expOfType ET e t 
      -> exp_eval E e = exp_eval E' e.

  Hypothesis live_exp_sound : exp -> live -> Type.
  Hypothesis live_exp_sound_incl 
    : forall e lv lv', lv' ⊆ lv -> live_exp_sound e lv' -> live_exp_sound e lv.

  Hypothesis exp_eval_live 
    : forall e lv E E', live_exp_sound e lv -> agree_on lv E E' -> 
      exp_eval E e = exp_eval E' e.

  Hypothesis var_to_exp : forall x:var, exp.
  Hypothesis var_to_exp_correct : forall M x,
     exp_eval M (var_to_exp x) = Some (M [x]).


(* End Expressions. *)

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)
