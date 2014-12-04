Require Import IL StateType.

Inductive Crash : F.state -> F.state -> Prop :=
(*|CrashReturn L E e:
exp_eval E e = None
-> state_result (L,E, stmtReturn e) = None
-> Crash (L,E,stmtReturn e) (L, E, stmtReturn e) *)
|CrashGoto L E f Y:
omap (exp_eval E) Y = None
-> Crash (L, E, stmtGoto f Y) (L, E, stmtGoto f Y)
|CrashBase L E s :
( forall f el, s <> stmtGoto f el)
->  normal2 F.step (L, E, s)
-> state_result (L,E,s) = None
-> Crash (L, E,s) (L,E,s)
|CrashStep L E s sigma' sigma'' a:
   F.step (L, E, s) a sigma'
   ->  (forall f xl, s <> stmtGoto f xl)
   -> Crash sigma' sigma''
   -> Crash (L,E,s) sigma''.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)