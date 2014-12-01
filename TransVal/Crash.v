Require Import IL StateType.

Inductive Crash : F.state -> F.state -> Prop :=
(*|CrashReturn L E e:
exp_eval E e = None
-> state_result (L,E, stmtReturn e) = None
-> Crash (L,E,stmtReturn e) (L, E, stmtReturn e) *)
|CrashBase L E s :
(* forall e, s <> stmtReturn e) *)
(*->*)  normal2 F.step (L, E, s)
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