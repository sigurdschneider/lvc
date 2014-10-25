Require Import List.
Require Import IL Val sexp.

(** Inductive Predicate that is true if and only if the given list is a list of the output expressions of the
IL/F program 
The output expressions of a return statement is the list containing the expression that is returned.
The output expressions of a function call is the list containing the expression in the call. **)
Inductive OutVars: list exp -> stmt -> Prop :=
| OutVarsRet e:  OutVars (e::nil) (stmtReturn e)
| OutVarsFCall f e: OutVars e (stmtGoto f e)
|OutVarsLet l x e s: OutVars l s -> OutVars l (stmtExp x e s)
|OutVarsIf l1 l2 c t f : OutVars l1 t -> OutVars l2 f -> OutVars (List.app l1 l2) (stmtIf c t f)
|OutVarsFun l Z s t: OutVars l  s -> OutVars l (stmtLet Z s t)
|OutVarsExtern l x f Y s: OutVars l s -> OutVars l (stmtExtern x f Y s).

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)