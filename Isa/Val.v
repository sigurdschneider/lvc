Require Import Util EqDec. 
Require Import OrderedTypeEx.

Set Implicit Arguments.

(** * More or less abstract values *)
(** A file that abstacts over values and (should) provide all necessary operations. Although we concretely instantiate val to int, we maintain this file as interface between our proofs and Integer library. *)

Definition val := nat.
Definition default_val : val := 0.

Opaque val.
Opaque default_val.

Global Instance inst_val_defaulted : Defaulted val := {
  default_el := default_val
}.

Global Instance inst_eq_dec_val : EqDec val eq.
hnf; intros. change ({x = y} + {x <> y}).
eapply nat_eq_eqdec.
Defined.

(** ** There must be an injection into the booleans *)
Definition val2bool : val -> bool := fun v => match v with 0 => false | _ => true end.

Opaque val2bool.

Inductive ty : Set :=
  Natural : ty.

Global Instance inst_eq_dec_ty : EqDec ty eq.
hnf; intros. change ({x = y} + {x <> y}).
decide equality.
Defined.


Inductive valOfType : val -> ty -> Prop :=
  naturalOfType n : valOfType n Natural.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr") ***
*** End: ***
*)
