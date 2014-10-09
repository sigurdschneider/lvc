Require Import IL.

Inductive noFun : stmt->Prop :=
|noFunLet x e s :
 noFun s
 -> noFun (stmtExp x e s)
|noFunIf e s t :
 noFun s
 -> noFun t
 -> noFun (stmtIf e s t)
|noFunCall l Y :
 noFun (stmtGoto l Y)
|noFunExp e :
 noFun (stmtReturn e).

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)