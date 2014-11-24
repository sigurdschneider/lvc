Require Import IL StateType.

Inductive Crash : F.state -> F.state -> Prop :=
|CrashBase L E s :
 (forall a σ, ~ F.step (L, E, s) a σ)
-> state_result (L,E,s) = None
-> Crash (L, E,s) (L,E,s)
|CrashStep sigma sigma' sigma'' a:
   F.step sigma a sigma'
   -> Crash sigma' sigma''
   -> Crash sigma sigma''.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)