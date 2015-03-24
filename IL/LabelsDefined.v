Require Import List.
Require Import Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL DecSolve.

Set Implicit Arguments.


Inductive labelsDefined : stmt -> nat -> Prop :=
  | labelsDefinedExp x e s L
    : labelsDefined s L
      -> labelsDefined (stmtLet x e s) L
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


Inductive paramsMatch : stmt -> list nat -> Prop :=
  | paramsMatchExp x e s L
    : paramsMatch s L
      -> paramsMatch (stmtLet x e s) L
  | paramsMatchIf e s t L
    : paramsMatch s L
      -> paramsMatch t L
      -> paramsMatch (stmtIf e s t) L
  | paramsMatchRet e L
    : paramsMatch (stmtReturn e) L
  | paramsMatchGoto f Y L n
    : get L (counted f) n
      -> length Y = n
      -> paramsMatch (stmtApp f Y) L
  | paramsMatchExtern x f Y s L
    : paramsMatch s L
      -> paramsMatch (stmtExtern x f Y s) L
  | paramsMatchLet s t Z L
    :  paramsMatch s (length Z::L)
      -> paramsMatch t (length Z::L)
      -> paramsMatch (stmtFun Z s t) L.


Inductive isCalled : stmt -> lab -> Prop :=
  | IsCalledExp x e s l
    : isCalled s l
      -> isCalled (stmtLet x e s) l
  | IsCalledIf1 e s t l
    : isCalled s l
      -> isCalled (stmtIf e s t) l
  | IsCalledIf2 e s t l
    : isCalled t l
      -> isCalled (stmtIf e s t) l
  | IsCalledGoto f Y
    : isCalled (stmtApp f Y) f
  | IsCalledExtern x f Y s l
    : isCalled s l
      -> isCalled (stmtExtern x f Y s) l
  | IsCalledLet1 s t Z l
    : isCalled s (incc l 1)
      -> isCalled t (LabI 0)
      -> isCalled (stmtFun Z s t) l
  | IsCalledLet s t Z l
    : isCalled t (incc l 1)
      -> isCalled (stmtFun Z s t) l.


Inductive noUnreachableCode : stmt -> Prop :=
  | NoUnrechableCodeExp x e s
    : noUnreachableCode s
      -> noUnreachableCode (stmtLet x e s)
  | NoUnrechableCodeIf1 e s t
    : noUnreachableCode s
      -> noUnreachableCode t
      -> noUnreachableCode (stmtIf e s t)
  | NoUnrechableCodeGoto f Y
    : noUnreachableCode (stmtApp f Y)
  | NoUnrechableCodeReturn e
    : noUnreachableCode (stmtReturn e)
  | NoUnrechableCodeExtern x f Y s
    : noUnreachableCode s
      -> noUnreachableCode (stmtExtern x f Y s)
  | NoUnrechableCodeLet1 s t Z
    : noUnreachableCode s
      -> noUnreachableCode t
      -> isCalled t (LabI 0)
      -> noUnreachableCode (stmtFun Z s t).


Inductive isFreeLab : stmt -> lab -> Prop :=
  | IsFreeLabExp x e s l
    : isFreeLab s l
      -> isFreeLab (stmtLet x e s) l
  | IsFreeLabIf1 e s t l
    : isFreeLab s l
      -> isFreeLab (stmtIf e s t) l
  | IsFreeLabIf2 e s t l
    : isFreeLab t l
      -> isFreeLab (stmtIf e s t) l
  | IsFreeLabGoto f Y
    : isFreeLab (stmtApp f Y) f
  | IsFreeLabExtern x f Y s l
    : isFreeLab s l
      -> isFreeLab (stmtExtern x f Y s) l
  | IsFreeLabLet1 s t Z l
    : isFreeLab s (incc l 1)
      -> isFreeLab (stmtFun Z s t) l
  | IsFreeLabLet s t Z l
    : isFreeLab t (incc l 1)
      -> isFreeLab (stmtFun Z s t) l.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
