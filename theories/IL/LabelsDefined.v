Require Import Util Get Drop MoreList DecSolve Indexwise.
Require Import Exp IL.

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
  | paramsMatchLet F t L
    :  (forall n Zs, get F n Zs -> paramsMatch (snd Zs) (length ⊝ fst ⊝ F ++ L))
      -> paramsMatch t (length ⊝ fst ⊝ F ++ L)
      -> paramsMatch (stmtFun F t) L.

Lemma paramsMatch_app A B C (f:list A * B -> list C) (L:list (list A * B))
      (L':list (list C)) t
  : paramsMatch t (length ⊝ (f ⊝ L) ++ length ⊝ L')
    -> paramsMatch t (length ⊝ (f ⊝ L ++ L')).
Proof.
  rewrite List.map_app. eauto.
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
  - edestruct (IH s); [ eauto | | dec_right].
    exploit (@list_get_computable' _ F
                                   (fun Zs => paramsMatch (snd Zs) (length ⊝ fst ⊝ F ++ L))).
    intros. eapply IH; eauto.
    destruct H; [| dec_right].
    dec_solve.
Qed.

Lemma paramsMatch_labelsDefined s (L:list nat)
  : paramsMatch s L -> labelsDefined s ❬L❭.
Proof.
  intros PM.
  general induction PM; eauto using labelsDefined, get_range.
  - econstructor.
    + intros. exploit H0; eauto. rewrite app_length, !map_length in H2. eauto.
    + rewrite app_length, !map_length in IHPM. eauto.
Qed.

Lemma paramsMatch_labelsDefined_nil s
  : paramsMatch s nil -> labelsDefined s 0.
Proof.
  intros PM. eapply (paramsMatch_labelsDefined PM).
Qed.

Hint Resolve paramsMatch_labelsDefined paramsMatch_labelsDefined_nil.


Inductive callChain (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕)
  : lab -> lab -> Prop :=
| CallChain_refl l
  : callChain isCalled F l l
| CallChain_step k k' Zs l
  : get F k Zs
    -> isCalled (snd Zs) (LabI k')
    -> callChain isCalled F (LabI k') l -> callChain isCalled F (LabI k) l.

Lemma callChain_mono (isCalled isCalled' : stmt -> lab -> Prop) F l l'
  : callChain isCalled F l l'
    -> (forall s l, isCalled s l -> isCalled' s l)
    -> callChain isCalled' F l l'.
Proof.
  intros CC LE.
  general induction CC; eauto using callChain.
Qed.

Definition isCalledFrom (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕)
           (t:stmt) (l:lab) :=
  exists l', isCalled t l' /\ callChain isCalled F l' l.

Lemma isCalledFrom_mono (isCalled isCalled' : stmt -> lab -> Prop) F t l
  : isCalledFrom isCalled F t l
    -> (forall s l, isCalled s l -> isCalled' s l)
    -> isCalledFrom isCalled' F t l.
Proof.
  intros [l' [IC CC]] LE.
  exists l'; split; eauto using callChain_mono.
Qed.

Lemma isCalledFrom_extend (isCalled : stmt -> lab -> Prop) (F:list (params * stmt)) k t f Zs
  : isCalledFrom isCalled F t (LabI k)
    -> get F k Zs
    -> isCalled (snd Zs) f
    -> isCalledFrom isCalled F t f.
Proof.
  intros. destruct H; dcr. hnf.
  eexists; split; eauto. clear H2. destruct f as [f].
  general induction H3; eauto using callChain, get_range.
Qed.

Lemma callChain_cases  (isCalled : stmt -> lab -> Prop) (F:〔params * stmt〕) l l'
  : callChain isCalled F l l'
    -> l = l' \/
      counted l < ❬F❭ /\
      exists k Zs, callChain isCalled F l (LabI k)
              /\ get F k Zs
              /\ isCalled (snd Zs) l'.
Proof.
  intros.
  general induction H.
  - left. eauto.
  - right; simpl. split; [ eauto using get_range | ].
    destruct IHcallChain as [| [? [? [? ?]]]]; dcr; subst.
    + eauto using callChain.
    + eexists x, x0; eauto using callChain.
Qed.

Inductive isCalled (b:bool) : stmt -> lab -> Prop :=
  | IsCalledExp x e s l
    : isCalled b s l
      -> isCalled b (stmtLet x e s) l
  | IsCalledIf1 e s t l
    : isCalled b s l
      -> (if b then op2bool e <> Some false else True)
      -> isCalled b (stmtIf e s t) l
  | IsCalledIf2 e s t l
    : isCalled b t l
      -> (if b then op2bool e <> Some true else True)
      -> isCalled b (stmtIf e s t) l
  | IsCalledGoto f Y
    : isCalled b (stmtApp f Y) f
  | IsCalledLet F t l l'
    : callChain (isCalled b) F l' (incc l (length F))
      -> isCalled b t l'
      -> isCalled b (stmtFun F t) l.

Lemma trueIsCalled_isCalled s l b
  : isCalled true s l -> isCalled b s l.
Proof.
  revert l; sind s; destruct s; intros; invt isCalled;
    try destruct b; simpl in *; eauto using isCalled.
  - econstructor; eauto.
    clear H4 H.
    general induction H2; eauto using callChain.
Qed.

Inductive noUnreachableCode (isCalled : stmt -> lab -> Prop) : stmt -> Prop :=
  | NoUnrechableCodeExp x e s
    : noUnreachableCode isCalled s
      -> noUnreachableCode isCalled (stmtLet x e s)
  | NoUnrechableCodeIf1 e s t
    : noUnreachableCode isCalled s
      -> noUnreachableCode isCalled t
      -> noUnreachableCode isCalled (stmtIf e s t)
  | NoUnrechableCodeGoto f Y
    : noUnreachableCode isCalled (stmtApp f Y)
  | NoUnrechableCodeReturn e
    : noUnreachableCode isCalled (stmtReturn e)
  | NoUnrechableCodeLet1 F t
    : (forall n Zs, get F n Zs -> noUnreachableCode isCalled (snd Zs))
      -> noUnreachableCode isCalled t
      -> (forall n, n < length F -> isCalledFrom isCalled F t (LabI n))
      -> noUnreachableCode isCalled (stmtFun F t).

Lemma noUnreachableCode_mono (isCalled isCalled' : stmt -> lab -> Prop) s
  : noUnreachableCode isCalled s
    -> (forall s l, isCalled s l -> isCalled' s l)
    -> noUnreachableCode isCalled' s.
Proof.
  intros NOC LE.
  general induction NOC; eauto 20 using noUnreachableCode, isCalledFrom_mono.
Qed.

Lemma noUnreachableCode_trueIsCalled_isCalled s b
  : noUnreachableCode (isCalled true) s
    -> noUnreachableCode (isCalled b) s.
Proof.
  intros. eapply noUnreachableCode_mono; eauto.
  eauto using trueIsCalled_isCalled.
Qed.

Hint Resolve noUnreachableCode_trueIsCalled_isCalled.