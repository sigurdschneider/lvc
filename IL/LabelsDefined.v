Require Import Util Get Drop MoreList DecSolve Indexwise.
Require Import Exp MoreExp IL.

Set Implicit Arguments.

Local Arguments length {A} L.

Instance list_get_computable' X (L:list X) (R:X->Prop) `{forall n (x:X), get L n x -> Computable (R x)}
: Computable (forall n x, get L n x -> R x).
Proof.
  hnf. general induction L.
  - left; isabsurd.
  - edestruct H; eauto using get.
    + edestruct IHL; eauto using get.
      * left; intros. inv H0; eauto using get.
      * right; intros; eauto using get.
Defined.


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

Lemma labelsDefined_app A B (f:A->B) (L:list A) (L':list B) k t
  : labelsDefined t (k + ❬L'❭)
    -> length L = k
    -> labelsDefined t ❬f ⊝ L ++ L'❭.
Proof.
  rewrite app_length, map_length. intros; subst; eauto.
Qed.

Hint Resolve labelsDefined_app.

Lemma labelsDefined_dec s n : Computable (labelsDefined s n).
Proof.
  hnf. revert n. sind s; destruct s; simpl; intros.
  - edestruct (IH s); eauto; dec_solve.
  - edestruct (IH s1); [ eauto | | dec_right].
    edestruct (IH s2); [ eauto | dec_solve | dec_right].
  - ensure (n > counted l). dec_solve.
  - dec_solve.
  - edestruct (IH s); eauto; dec_solve.
  - edestruct (IH s); [ eauto | | dec_right].
    exploit (@list_get_computable' _ F
                                   (fun Zs => labelsDefined (snd Zs) (❬F❭ + n))).
    intros. eapply IH; eauto.
    destruct H; [| dec_right].
    dec_solve.
Qed.


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

Lemma paramsMatch_app A B C (f:list A * B -> list C) (L:list (list A * B))
      (L':list (list C)) t
  : paramsMatch t (length ⊝ (f ⊝ L) ++ length ⊝ L')
    -> paramsMatch t (length ⊝ (f ⊝ L ++ L')).
Proof.
  rewrite map_app. eauto.
Qed.

Hint Resolve paramsMatch_app.

Lemma paramsMatch_dec s L : Computable (paramsMatch s L).
Proof.
  hnf. revert L. sind s; destruct s; simpl; intros.
  - edestruct (IH s); eauto; dec_solve.
  - edestruct (IH s1); [ eauto | | dec_right].
    edestruct (IH s2); [ eauto | dec_solve | dec_right].
  - destruct (get_dec L (counted l)) as [[? ?]|]; [| dec_right].
    ensure (length Y = x). dec_solve.
  - dec_solve.
  - edestruct (IH s); eauto; dec_solve.
  - edestruct (IH s); [ eauto | | dec_right].
    exploit (@list_get_computable' _ F
                                   (fun Zs => paramsMatch (snd Zs) (length ⊝ fst ⊝ F ++ L))).
    intros. eapply IH; eauto.
    destruct H; [| dec_right].
    dec_solve.
Qed.

(*
Inductive isCalledIn (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕)
  : stmt -> lab -> Prop :=
| IsCalledIn s l
  : isCalled s l -> isCalledIn isCalled F s l
| IsCalledInNext k s Zs l
  : isCalled s (LabI k)
    -> get F k Zs
    -> isCalledIn isCalled F (snd Zs) l -> isCalledIn isCalled F s l.
*)

Inductive callChain (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕)
  : lab -> lab -> Prop :=
| CallChain_refl l
  : callChain isCalled F l l
| CallChain_step k k' Zs l
  : get F k Zs
    -> isCalled (snd Zs) (LabI k')
    -> callChain isCalled F (LabI k') l -> callChain isCalled F (LabI k) l.

Definition isCalledFrom (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕)
           (t:stmt) (l:lab) :=
  exists l', isCalled t l' /\ callChain isCalled F l' l.

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
  | IsCalledLet F t l l'
    : callChain isCalled F l' (incc l (length F))
      -> isCalled t l'
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
  | TrueIsCalledLet F t l l'
    : callChain trueIsCalled F l' (incc l (length F))
      -> trueIsCalled t l'
      -> trueIsCalled (stmtFun F t) l.

Lemma trueIsCalled_isCalled s l
  : trueIsCalled s l -> isCalled s l.
Proof.
  revert l; sind s; destruct s; intros; invt trueIsCalled; eauto using isCalled.
  - econstructor; eauto.
    clear H4 H.
    general induction H2; eauto using callChain.
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
