Require Import IL StateType.
Require Import smt.

Set Implicit Arguments.

Inductive Terminates :F.state -> F.state -> Prop :=
|TerminatesReturn L E e v:
   exp_eval E e = ⎣v⎦
   -> Terminates (L, E, stmtReturn e)   (L  , E , stmtReturn e)
|TerminatesApp L E f x vl:
   omap (exp_eval E) x = ⎣vl⎦
   -> Terminates (L, E, stmtApp f x) (L, E, stmtApp f x)
|TerminatesStep L E s L'  E' s'  L'' E'' s''  a:
   F.step (L, E, s) a (L', E', s')
   -> Terminates (L', E', s') (L'', E'', s'')
   ->  (forall f xl, s <> stmtApp f xl)
   -> Terminates (L,E,s) (L'', E'', s'') .

Inductive Crash : F.state -> F.state -> Prop :=
|CrashApp L E f Y:
omap (exp_eval E) Y = None
-> Crash (L, E, stmtApp f Y) (L, E, stmtApp f Y)
|CrashBase L E s :
( forall f el, s <> stmtApp f el)
->  normal2 F.step (L, E, s)
-> state_result (L,E,s) = None
-> Crash (L, E,s) (L,E,s)
|CrashStep L E s sigma' sigma'' a:
   F.step (L, E, s) a sigma'
   ->  (forall f xl, s <> stmtApp f xl)
   -> Crash sigma' sigma''
   -> Crash (L,E,s) sigma''.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)