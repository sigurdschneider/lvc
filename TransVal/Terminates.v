Require Import IL smt.

Set Implicit Arguments.

Inductive Terminates :F.state -> F.state -> Prop :=
|TerminatesReturn L E e v:
(*   translateExp e = ⎣b⎦  *)
   exp_eval E e = ⎣v⎦
   -> Terminates (L, E, stmtReturn e)   (L  , E , stmtReturn e)
|TerminatesStep sigma sigma' sigma'' a:
   F.step sigma a sigma'
   -> Terminates sigma' sigma''
   -> Terminates sigma sigma''.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
