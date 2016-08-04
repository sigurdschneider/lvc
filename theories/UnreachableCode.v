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
  : list bool -> stmt -> ann bool -> Prop :=
| UCPOpr BL x s b e al
  :  unreachable_code i BL s al
     -> getAnn al = b
     -> unreachable_code i BL (stmtLet x e s) (ann1 b al)
| UCPIf BL e b1 b2 b al1 al2
  :  (exp2bool e <> Some false -> getAnn al1 = b)
     -> (exp2bool e <> Some true -> getAnn al2 = b)
     -> unreachable_code i BL b1 al1
     -> unreachable_code i BL b2 al2
     -> unreachable_code i BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto BL l Y b a
  : get BL (counted l) b
    -> impb a b
    -> unreachable_code i BL (stmtApp l Y) (ann0 a)
| UCReturn BL e b
  : unreachable_code i BL (stmtReturn e) (ann0 b)
| UCExtern BL x s b Y al f
  : unreachable_code i BL s al
    -> getAnn al = b
    -> unreachable_code i BL (stmtExtern x f Y s) (ann1 b al)
| UCLet BL F t b als alt
  : unreachable_code i (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> getAnn alt = b
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code i (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (if isComplete i then (forall n a,
                                get als n a ->
                                getAnn a ->
                                isCalledFrom trueIsCalled F t (LabI n)) else True)
    -> unreachable_code i BL (stmtFun F t) (annF b als alt).

Local Hint Extern 0 =>
match goal with
| [ H : exp2bool ?e <> Some ?t , H' : exp2bool ?e <> Some ?t -> ?B = ?C |- _ ] =>
  specialize (H' H); subst
end.

Lemma unreachable_code_trueIsCalled i Lv s slv l
  : unreachable_code i Lv s slv
    -> trueIsCalled s l
    -> exists b, get Lv (counted l) b /\ impb (getAnn slv) b.
Proof.
  destruct l; simpl.
  revert Lv slv n.
  sind s; destruct s; intros Lv slv n UC IC; inv UC; inv IC;
    simpl in *; subst; simpl in *; eauto 20.
  - (* If I admit this here, then eauto does the job:
    assert (forall y, size s < size (stmtLet x e s) -> forall Lv slv n,
                 unreachable_code i Lv y slv ->
                 trueIsCalled y (LabI n) ->
                 exists b : bool,
                   get Lv n b /\ impb (getAnn slv) b) by admit.
     *)
    (* However, it refuses to apply IH. *)
    eapply (IH s); eauto.
  - exploit (IH s1); eauto.
  - exploit (IH s2); eauto.
  - eapply (IH s); eauto.
  - destruct l'.
    exploit (IH s); eauto; dcr.
    setoid_rewrite H8.
    clear H7 H6 UC H8 H1 alt.
    general induction H3.
    + inv_get. eexists; split; eauto.
    + inv_get.
      exploit H5; eauto.
      eapply IH in H4; eauto.
      dcr. inv_get.
      edestruct IHcallChain; try eapply H8; eauto; dcr.
      eexists x1; split; eauto.
Qed.
