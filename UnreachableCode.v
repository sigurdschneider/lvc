Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Exp MoreExp SetOperations.
Require Export Filter LabelsDefined OUnion.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

Inductive unreachable_code
  : list params -> list bool -> stmt -> ann bool -> Prop :=
| UCPOpr ZL BL x s b e al
  :  unreachable_code ZL BL s al
     -> getAnn al = b
     -> unreachable_code ZL BL (stmtLet x e s) (ann1 b al)
| UCPIf ZL BL e b1 b2 b al1 al2
  :  (exp2bool e <> Some false -> getAnn al1 = b)
     -> (exp2bool e <> Some true -> getAnn al2 = b)
     -> unreachable_code ZL BL b1 al1
     -> unreachable_code ZL BL b2 al2
     -> unreachable_code ZL BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto ZL BL l Y Z b a
  : get ZL (counted l) Z
    -> get BL (counted l) b
    -> impb a b
    -> length Y = length Z
    -> unreachable_code ZL BL (stmtApp l Y) (ann0 a)
| UCReturn ZL BL e b
  : unreachable_code ZL BL (stmtReturn e) (ann0 b)
| UCExtern ZL BL x s b Y al f
  : unreachable_code ZL BL s al
    -> getAnn al = b
    -> unreachable_code ZL BL (stmtExtern x f Y s) (ann1 b al)
| UCLet ZL BL F t b als alt
  : unreachable_code (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> getAnn alt = b
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 getAnn a ->
                 trueIsCalled t (LabI n))
    -> unreachable_code ZL BL (stmtFun F t) (annF b als alt).

Local Hint Extern 0 =>
match goal with
| [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H); subst
end.

Lemma unreachable_code_trueIsCalled i Lv s slv l
  : unreachable_code i Lv s slv
    -> trueIsCalled s l
    -> exists b, get Lv (counted l) b /\ impb (getAnn slv) b.
Proof.
  intros Live IC. destruct l; simpl in *.
  general induction IC; invt unreachable_code; subst; simpl in *; eauto.
  - exploit IHIC2; eauto; simpl in *; dcr.
    rewrite get_app_lt in H5; eauto with len. inv_get.
    exploit IHIC1; eauto; dcr.
    rewrite get_app_ge in H7; eauto with len.
    rewrite map_length in H7; eauto with len.
    orewrite (❬F❭ + n - ❬als❭ = n) in H7.
    eexists; split; eauto. etransitivity; eauto.
  - exploit IHIC; eauto; try reflexivity; dcr.
    rewrite get_app_ge in H3; eauto with len.
    rewrite map_length in H3.
    orewrite (❬F❭ + n - ❬als❭ = n) in H3. eauto.
Qed.
