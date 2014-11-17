Require Import IL.

Inductive noGoto : stmt->Prop :=
|noGotoLet x e s :
 noGoto s
 -> noGoto (stmtExp x e s)
|noGotoIf e s t :
 noGoto s
 -> noGoto t
 -> noGoto (stmtIf e s t)
|noGotoFun  x s t :
noGoto s
-> noGoto t
-> noGoto (stmtLet x s t)
|noGotoExp e :
 noGoto (stmtReturn e).

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)