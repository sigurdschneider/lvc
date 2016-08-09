Require Import List Exp IL.

Inductive app_expfree : stmt -> Prop :=
| ExpFreeLet x e s
: app_expfree s
  -> app_expfree (stmtLet x e s)

| ExpFreeReturn e
: app_expfree (stmtReturn e)

| ExpFreeIf e s t
:  app_expfree s
-> app_expfree t
  -> app_expfree (stmtIf e s t)

| ExpFreeApp f Y
: (forall n y, get Y n y -> isVar y)
  -> app_expfree (stmtApp f Y)

| ExpFreeFun F t
: (forall n Zs, get F n Zs -> app_expfree (snd Zs))
-> app_expfree t
   -> app_expfree (stmtFun F t)
.