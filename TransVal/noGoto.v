Require Import IL.

Inductive noGoto : stmt->Prop :=
|noGotoLet x e s :
 noGoto s
 -> noGoto (stmtLet x e s)
|noGotoIf e s t :
 noGoto s
 -> noGoto t
 -> noGoto (stmtIf e s t)
|noGotoFun F t :
   (forall n Zs, get F n Zs -> noGoto (snd Zs))
   -> noGoto t
   -> noGoto (stmtFun F t)
|noGotoExp e :
 noGoto (stmtReturn e).
