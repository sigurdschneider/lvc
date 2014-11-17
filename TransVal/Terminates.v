Require Import IL smt noGoto.

Set Implicit Arguments.

Inductive Terminates :F.state -> F.state -> Prop :=
|TerminatesReturn L E e v:
   exp_eval E e = ⎣v⎦
   -> Terminates (L, E, stmtReturn e)   (L  , E , stmtReturn e)
|TerminatesGoto L E f x vl:
   omap (exp_eval E) x = ⎣vl⎦
   -> Terminates (L, E, stmtGoto f x) (L, E, stmtGoto f x)
|TerminatesStep L E s L'  E' s'  L'' E'' s''  a:
  noGoto s
  -> F.step (L, E, s) a (L', E', s')
   -> Terminates (L', E', s') (L'', E'', s'')
   -> Terminates (L,E,s) (L'', E'', s'') .

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
