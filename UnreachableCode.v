Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Exp MoreExp SetOperations.
Require Export Filter LabelsDefined OUnion.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

Inductive sc := Sound | SoundAndComplete.

Definition isComplete (s:sc) :=
  match s with
  | SoundAndComplete => true
  | _ => false
  end.

Inductive unreachable_code (i:sc)
  : list params -> list bool -> stmt -> ann bool -> Prop :=
| UCPOpr ZL BL x s b e al
  :  unreachable_code i ZL BL s al
     -> getAnn al = b
     -> unreachable_code i ZL BL (stmtLet x e s) (ann1 b al)
| UCPIf ZL BL e b1 b2 b al1 al2
  :  (exp2bool e <> Some false -> getAnn al1 = b)
     -> (exp2bool e <> Some true -> getAnn al2 = b)
     -> unreachable_code i ZL BL b1 al1
     -> unreachable_code i ZL BL b2 al2
     -> unreachable_code i ZL BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto ZL BL l Y Z b a
  : get ZL (counted l) Z
    -> get BL (counted l) b
    -> impb a b
    -> length Y = length Z
    -> unreachable_code i ZL BL (stmtApp l Y) (ann0 a)
| UCReturn ZL BL e b
  : unreachable_code i ZL BL (stmtReturn e) (ann0 b)
| UCExtern ZL BL x s b Y al f
  : unreachable_code i ZL BL s al
    -> getAnn al = b
    -> unreachable_code i ZL BL (stmtExtern x f Y s) (ann1 b al)
| UCLet ZL BL F t b als alt
  : unreachable_code i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> getAnn alt = b
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code i (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (if isComplete i then (forall n Zs a, get F n Zs ->
                                      get als n a ->
                                      getAnn a ->
                                      trueIsCalled t (LabI n)) else True)
    -> unreachable_code i ZL BL (stmtFun F t) (annF b als alt).

Local Hint Extern 0 =>
match goal with
| [ H : ?A, H' : ?A -> _ |- _ ] => specialize (H' H); subst
end.

Lemma unreachable_code_trueIsCalled i ZL Lv s slv l
  : unreachable_code i ZL Lv s slv
    -> trueIsCalled s l
    -> exists b, get Lv (counted l) b /\ impb (getAnn slv) b.
Proof.
  destruct l; simpl.
  revert ZL Lv slv n.
  sind s; destruct s; intros ZL Lv slv n UC IC; inv UC; inv IC;
    simpl in *; subst; simpl in *; eauto.
  - specialize (H2 H6); subst.
    exploit (IH s1); eauto.
  - clear H8.
    exploit (IH s); eauto; simpl in *; dcr.
    rewrite get_app_lt in H5; eauto with len. inv_get.
    clear H7.
    cut (exists b : bool, get Lv n b /\ impb (getAnn x0) b).
    intros; dcr; eexists; split; eauto. etransitivity; eauto.
    clear H8. clear H1. clear IC UC alt.
    general induction H4.
    + exploit (IH (snd Zs)); eauto; dcr.
      inv_get. eexists; split; eauto.
    + destruct (get_in_range _ H0). inv_get.
      exploit (IHcallChain i s eq_refl IH). eauto.
      eauto. eauto. eauto. eauto. eauto.
      dcr. eexists; split; eauto.
      exploit (IH (snd Zs)); eauto. dcr. inv_get.
      etransitivity; eauto.
  - exploit (IH s); eauto; try reflexivity; dcr.
    rewrite get_app_ge in H3; eauto with len.
    rewrite map_length in H3.
    orewrite (❬F❭ + n - ❬als❭ = n) in H3. eauto.
Qed.
