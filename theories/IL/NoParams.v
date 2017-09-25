Require Import IL.

Inductive noParams : stmt->Prop :=
| NoParamsLet
    x e s
    (NoParamsIH:noParams s)
    : noParams (stmtLet x e s)
| NoParamsIf
    e s t
    (NoParamsIH1:noParams s)
    (NoParamsIH2:noParams t)
  : noParams (stmtIf e s t)
| NoParamsApp l :
   noParams (stmtApp l nil)
| NoParamsExp e :
    noParams (stmtReturn e)
| NoParamsCall F t
  (NoParamsIHF:forall n Zs, get F n Zs -> noParams (snd Zs))
  (NoParamsF:forall n Zs, get F n Zs -> fst Zs = nil)
  (NoParamsIHt:noParams t)
  : noParams (stmtFun F t).
