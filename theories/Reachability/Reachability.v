Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Exp SetOperations.
Require Export Filter LabelsDefined OUnion.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

(** * Rechability Specification *)
(** The reachability predicate is parameterized by a value of type [sc],
    which indicates whether soundness, completeness, or both are desired. *)

Inductive sc := Sound | Complete | SoundAndComplete.

Definition isComplete (s:sc) :=
  match s with
  | SoundAndComplete => true
  | Complete => true
  | _ => false
  end.

Definition isSound (s:sc) :=
  match s with
  | SoundAndComplete => true
  | Sound => true
  | _ => false
  end.

(** Depending on whether soundness, completeness or both are desiered,
    the relation [uceq] is instantiated differently. *)

Definition uceq (i:sc) (a b:bool) :=
  match i with
  | Sound => impb a b
  | Complete => impb b a
  | SoundAndComplete => a = b
  end.

Hint Extern 0 (uceq _ _ _) => simpl.

Lemma uceq_refl i a
  : uceq i a a.
Proof.
  destruct i; simpl; eauto.
Qed.

Lemma eq_uceq i (a b:bool)
  : a = b -> uceq i a b.
Proof.
  intros; subst. eauto using uceq_refl.
Qed.

Lemma eq_uceq_sym i (a b:bool)
  : b = a -> uceq i a b.
Proof.
  intros; subst. eauto using uceq_refl.
Qed.

Hint Resolve uceq_refl eq_uceq eq_uceq_sym.

(** ** The inductive predicate *)

Inductive reachability (i:sc)
  : list bool -> stmt -> ann bool -> Prop :=
| UCPOpr BL x s b e al
  :  reachability i BL s al
     -> uceq i b (getAnn al)
     -> reachability i BL (stmtLet x e s) (ann1 b al)
| UCPIf BL e b1 b2 b al1 al2
  :  (op2bool e <> Some false -> uceq i b (getAnn al1))
     -> (op2bool e <> Some true -> uceq i b (getAnn al2))
     -> reachability i BL b1 al1
     -> reachability i BL b2 al2
     -> (if isComplete i then op2bool e = ⎣ false ⎦ -> getAnn al1 = false else True)
     -> (if isComplete i then op2bool e = ⎣ true ⎦ -> getAnn al2 = false else True)
     -> reachability i BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto BL l Y b a
  : get BL (counted l) b
    -> (if isSound i then impb a b else True)
    -> reachability i BL (stmtApp l Y) (ann0 a)
| UCReturn BL e b
  : reachability i BL (stmtReturn e) (ann0 b)
| UCLet BL F t b als alt
  : reachability i (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> uceq i b (getAnn alt)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 reachability i (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (if isComplete i then (forall n a,
                                get als n a ->
                                getAnn a ->
                                isCalledFrom (isCalled true) F t (LabI n)) else True)
    -> (if isComplete i then forall n a, get als n a -> impb (getAnn a) b else True)
    -> reachability i BL (stmtFun F t) (annF b als alt).

(** ** Some Properties of the Predicate *)

Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> _ |- _ ] =>
  specialize (H' H); subst
end.

Lemma reachability_SC_S Lv s slv
  : reachability SoundAndComplete Lv s slv
    -> reachability Sound Lv s slv.
Proof.
  intros UC.
  general induction UC; simpl in *; subst; eauto 20 using reachability, uceq_refl.
  - econstructor; simpl; eauto using uceq_refl.
  - econstructor; simpl; eauto using uceq_refl.
Qed.

Hint Resolve reachability_SC_S.

Lemma reachability_sound_and_complete BL s a
  : reachability Complete BL s a
    -> reachability Sound BL s a
    -> reachability SoundAndComplete BL s a.
Proof.
  intros RCH UCS.
  general induction UCS; inv RCH; simpl in *; eauto 20 using reachability, impb_eq.
Qed.

Lemma reachability_trueIsCalled Lv s slv l
  : reachability Sound Lv s slv
    -> isCalled true s l
    -> exists b, get Lv (counted l) b /\ impb (getAnn slv) b.
Proof.
  destruct l; simpl.
  revert Lv slv n.
  sind s; destruct s; intros Lv slv n UC IC; inv UC; inv IC;
    simpl in *; subst; simpl in *; eauto 20.
  - edestruct (IH s); dcr; eauto.
  - edestruct (IH s1); dcr; eauto.
  - edestruct (IH s2); dcr; eauto.
  - destruct l'.
    exploit (IH s); eauto; dcr.
    setoid_rewrite H3. setoid_rewrite H10.
    clear H3 H10 UC H9 H1 alt.
    general induction H5.
    + inv_get. eexists; split; eauto.
    + inv_get.
      exploit H4; eauto.
      eapply IH in H3; eauto.
      dcr. inv_get.
      edestruct IHcallChain; try eapply H8; eauto; dcr.
      eexists x1; split; eauto.
Qed.
