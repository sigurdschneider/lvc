Require Import Util Get Drop MoreList.
Require Import Exp MoreExp IL.

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
  | labelsDefinedLet F t L
    :  (forall n Zs, get F n Zs -> labelsDefined (snd Zs) (length F + L))
      -> labelsDefined t (length F + L)
      -> labelsDefined (stmtFun F t) L.

Local Arguments length {A} L.

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
  | paramsMatchLet F t L
    :  (forall n Zs, get F n Zs -> paramsMatch (snd Zs) (length ⊝ fst ⊝ F ++ L))
      -> paramsMatch t (length ⊝ fst ⊝ F ++ L)
      -> paramsMatch (stmtFun F t) L.


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
  | IsCalledLet1 F t k Zs l
    : k < length F
      -> get F k Zs
      -> isCalled (snd Zs) (labInc l (length F))
      -> isCalled t (LabI k)
      -> isCalled (stmtFun F t) l
  | IsCalledLet F t l
    : isCalled t (incc l (length F))
      -> isCalled (stmtFun F t) l.


Inductive trueIsCalled : stmt -> lab -> Prop :=
  | TrueIsCalledExp x e s l
    : trueIsCalled s l
      -> trueIsCalled (stmtLet x e s) l
  | TrueIsCalledIf1 e s t l
    : trueIsCalled s l
      -> exp2bool e <> Some false
      -> trueIsCalled (stmtIf e s t) l
  | TrueIsCalledIf2 e s t l
    : trueIsCalled t l
      -> exp2bool e <> Some true
      -> trueIsCalled (stmtIf e s t) l
  | TrueIsCalledGoto f Y
    : trueIsCalled (stmtApp f Y) f
  | TrueIsCalledExtern x f Y s l
    : trueIsCalled s l
      -> trueIsCalled (stmtExtern x f Y s) l
  | TrueIsCalledLet1 F t k Zs l
    : k < length F
      -> get F k Zs
      -> trueIsCalled (snd Zs) (labInc l (length F))
      -> trueIsCalled t (LabI k)
      -> trueIsCalled (stmtFun F t) l
  | TrueIsCalledLet F t l
    : trueIsCalled t (incc l (length F))
      -> trueIsCalled (stmtFun F t) l.

Lemma trueIsCalled_isCalled s l
  : trueIsCalled s l -> isCalled s l.
Proof.
  intro IC.
  general induction IC; eauto using isCalled.
Qed.

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
  | NoUnrechableCodeLet1 F t
    : (forall n Zs, get F n Zs -> noUnreachableCode (snd Zs))
      -> noUnreachableCode t
      -> (forall n, n < length F -> isCalled t (LabI n))
      -> noUnreachableCode (stmtFun F t).
