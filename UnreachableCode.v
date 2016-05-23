Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp SetOperations.
Require Export Filter LabelsDefined OUnion.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

Inductive unreachable_code_precise
  : list params -> list bool -> stmt -> ann bool -> Prop :=
| UCPOpr ZL Lv x b lv e al
  :  unreachable_code_precise ZL Lv b al
     -> unreachable_code_precise ZL Lv (stmtLet x e b) (ann1 lv al)
| UCPIf ZL Lv e b1 b2 lv al1 al2
  :  (exp2bool e <> Some false -> unreachable_code_precise ZL Lv b1 al1)
     -> (exp2bool e <> Some true -> unreachable_code_precise ZL Lv b2 al2)
     -> unreachable_code_precise ZL Lv (stmtIf e b1 b2) (ann2 lv al1 al2)
| UCPGoto ZL Lv l Y lv Z
  : get ZL (counted l) Z
    -> get Lv (counted l) true
    -> length Y = length Z
    -> unreachable_code_precise ZL Lv (stmtApp l Y) (ann0 lv)
| UCReturn ZL Lv e lv
  : unreachable_code_precise ZL Lv (stmtReturn e) (ann0 lv)
| UCExtern ZL Lv x b lv Y al f
  : unreachable_code_precise ZL Lv b al
    -> unreachable_code_precise ZL Lv (stmtExtern x f Y b) (ann1 lv al)
| UCLet ZL Lv F t lv als alt
  : unreachable_code_precise (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t alt
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code_precise (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 getAnn a ->
                 trueIsCalled t (LabI n))
    -> unreachable_code_precise ZL Lv (stmtFun F t) (annF lv als alt).


Lemma unreachable_code_precise_trueIsCalled i Lv s slv l
  : unreachable_code_precise i Lv s slv
    -> trueIsCalled s l
    -> get Lv (counted l) true.
Proof.
  intros Live IC. destruct l; simpl in *.
  general induction IC; invt unreachable_code_precise; eauto.
  - exploit IHIC2; eauto; simpl in *.
    rewrite get_app_lt in H1; eauto with len. inv_get.
    exploit IHIC1; eauto.
    rewrite get_app_ge in H2; eauto with len.
    rewrite map_length in H2; eauto with len.
    orewrite (❬F❭ + n - ❬als❭ = n) in H2. eauto.
  - exploit IHIC; eauto; try reflexivity.
    rewrite get_app_ge in H; eauto with len.
    rewrite map_length in H.
    orewrite (❬F❭ + n - ❬als❭ = n) in H. eauto.
Qed.
