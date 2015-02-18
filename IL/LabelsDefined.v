Require Import List.
Require Import Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL DecSolve.

Set Implicit Arguments.

Inductive labelsDefined : stmt -> nat -> Prop :=
  | labelsDefinedExp x e s L
    : labelsDefined s L
      -> labelsDefined (stmtExp x e s) L
  | labelsDefinedIf e s t L
    : labelsDefined s L
      -> labelsDefined t L
      -> labelsDefined (stmtIf e s t) L
  | labelsDefinedRet e L
    : labelsDefined (stmtReturn e) L
  | labelsDefinedGoto f Y L
    : L > counted f
      -> labelsDefined (stmtApp f Y) L
  | labelsDefinedExtern x f Y s L
    : labelsDefined s L
      -> labelsDefined (stmtExtern x f Y s) L
  | labelsDefinedLet s t Z L
    :  labelsDefined s (S L)
      -> labelsDefined t (S L)
      -> labelsDefined (stmtFun Z s t) L.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
