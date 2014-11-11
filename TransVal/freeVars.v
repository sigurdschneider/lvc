Require Import List smt Exp Util CSet.

Fixpoint freeVars (s:smt) :=
match s with
| smtReturn e => Exp.freeVars e
| funcApp f x => list_union (List.map (Exp.freeVars) x)
| smtAnd a b => freeVars a ∪ freeVars b
| smtOr a b => freeVars a ∪ freeVars b
| smtNeg a => freeVars a
| ite c t f => freeVars t ∪ freeVars f ∪ Exp.freeVars c
| smtImp a b => freeVars a ∪ freeVars b
| smtFalse => {}
|constr e1 e2 => Exp.freeVars e1 ∪ Exp.freeVars e2
end.

Definition freeVarsList el :=
list_union (List.map freeVars el).

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
