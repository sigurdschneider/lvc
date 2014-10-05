Require Import List.
Require Import IL Exp Coherence sexp smt.

Lemma models_if_eval :
forall s D E s' E', 
ssa  s D
-> ((nil, E,s) -> (nil, E',s'))
-> forall p, models E'  (translateStmt s p).
(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)