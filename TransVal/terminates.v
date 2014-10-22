Require Import IL smt.

Set Implicit Arguments.

Inductive terminates :F.state -> F.state -> Prop :=
|terminatesReturn L E e b v:
   translateExp e = ⎣b⎦ 
   -> exp_eval E e = ⎣v⎦
   -> terminates (L, E, stmtReturn e)   (L  , E , stmtReturn e)
|terminatesStep sigma sigma' sigma'' a:
   F.step sigma a sigma'
   -> terminates sigma' sigma''
   -> terminates sigma sigma''.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)