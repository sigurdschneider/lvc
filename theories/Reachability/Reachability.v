Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Exp SetOperations.
Require Export Filter LabelsDefined OUnion Infra.PartialOrder WithTop.

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
  | Sound => poLe a b
  | Complete => poLe b a
  | SoundAndComplete => a = b
  end.

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

Lemma uceq_trans i (a b c:bool)
  : uceq i a b -> uceq i b c -> uceq i a c.
Proof.
  destruct i; simpl; firstorder.
Qed.

Hint Resolve uceq_refl.

Hint Immediate eq_uceq_sym eq_uceq.

Lemma uceq_soundandcomplete_sound a b
  :  uceq SoundAndComplete a b
     -> uceq Sound a b.
Proof.
  destruct a, b; firstorder.
Qed.

Lemma uceq_soundandcomplete_complete a b
  :  uceq SoundAndComplete a b
     -> uceq Complete a b.
Proof.
  destruct a, b; firstorder.
Qed.

Lemma uceq_sound_complete_soundandcomplete a b
  : uceq Sound a b
    -> uceq Complete a b
    -> uceq SoundAndComplete a b.
Proof.
  destruct a, b; firstorder.
Qed.

Hint Immediate uceq_soundandcomplete_sound
     uceq_soundandcomplete_complete
     uceq_sound_complete_soundandcomplete.

(** ** The inductive predicate *)

Inductive reachability (ceval:op -> option (withTop bool)) (i:sc)
  : list bool -> stmt -> ann bool -> Prop :=
| UCPOpr BL x s b e al
  :  reachability ceval i BL s al
     -> uceq i b (getAnn al)
     -> reachability ceval i BL (stmtLet x e s) (ann1 b al)
| UCPIf BL e b1 b2 b al1 al2
  :  (~ poLe (ceval e) (Some (wTA false)) -> uceq i b (getAnn al1))
     -> (~ poLe (ceval e) (Some (wTA true)) -> uceq i b (getAnn al2))
     -> reachability ceval i BL b1 al1
     -> reachability ceval i BL b2 al2
     -> (if isComplete i then poLe (ceval e) (Some (wTA false)) -> getAnn al1 = false else True)
     -> (if isComplete i then poLe (ceval e) (Some (wTA true)) -> getAnn al2 = false else True)
     -> reachability ceval i BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto BL l Y b a
  : get BL (counted l) b
    -> (if isSound i then poLe a b else True)
    -> reachability ceval i BL (stmtApp l Y) (ann0 a)
| UCReturn BL e b
  : reachability ceval i BL (stmtReturn e) (ann0 b)
| UCLet BL F t b als alt
  : reachability ceval i (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> uceq i b (getAnn alt)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 reachability ceval i (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (if isComplete i then (forall n a,
                                get als n a ->
                                getAnn a ->
                                isCalledFrom (isCalled true) F t (LabI n)) else True)
    -> (if isComplete i then forall n a, get als n a -> poLe (getAnn a) b else True)
    -> reachability ceval i BL (stmtFun F t) (annF b als alt).

Ltac simpl_isComplete :=
  match goal with
  | [ |- context f [ if isComplete Sound then ?A else ?B ] ] =>
    let x := context f[B] in change x
  | [ |- context f [ if isComplete Complete then ?A else ?B ] ] =>
    let x := context f[A] in change x
  | [ |- context f [ if isComplete SoundAndComplete then ?A else ?B ] ] =>
    let x := context f[A] in change x
  | [ H : context f [ if isComplete Sound then ?A else ?B ] |- _ ] =>
    let x := context f[B] in change x in H
  | [ H : context f [ if isComplete Complete then ?A else ?B ] |- _ ] =>
    let x := context f[A] in change x in H
  | [ H : context f [ if isComplete SoundAndComplete then ?A else ?B ] |- _ ] =>
    let x := context f[A] in change x in H
  end.


Hint Extern 0 => simpl_isComplete.
(** ** Some Properties of the Predicate *)

Opaque uceq.

Lemma reachability_SC_S ceval Lv s slv
  : reachability ceval SoundAndComplete Lv s slv
    -> reachability ceval Sound Lv s slv.
Proof.
  intros UC.
  general induction UC; subst; eauto 10 using reachability, uceq_soundandcomplete_sound.
Qed.

Hint Resolve reachability_SC_S.

Lemma reachability_sound_and_complete ceval BL s a
  : reachability ceval Complete BL s a
    -> reachability ceval Sound BL s a
    -> reachability ceval SoundAndComplete BL s a.
Proof.
  intros RCH UCS.
  general induction UCS; inv RCH; simpl in *;
    eauto 10 using reachability, uceq_sound_complete_soundandcomplete.
Qed.

Definition cop2bool e :=
  match op_eval (fun _ : _ => ⎣⎦) e with
  | Some v => ⎣ wTA (val2bool v) ⎦
  | None => Some Top
  end.

Lemma op2bool_not_none e
  : cop2bool e <> ⎣⎦.
Proof.
  unfold cop2bool; cases; congruence.
Qed.

Hint Resolve op2bool_not_none.

Lemma op2bool_cop2bool_not_some e b
  : op2bool e <> ⎣ b ⎦
    -> ~ cop2bool e ⊑ ⎣ wTA b ⎦.
Proof.
  unfold op2bool, cop2bool; intros.
  cases; simpl in *; intro; clear_trivial_eqs.
  eapply H; f_equal; eauto.
Qed.

Lemma op2bool_cop2bool e b
  : op2bool e = ⎣ b ⎦
    <-> cop2bool e = ⎣ wTA b ⎦.
Proof.
  unfold op2bool, cop2bool; intros; cases; simpl in *;
    split; intros; congruence.
Qed.

Lemma op2bool_cop2bool_not_some' e
  : op2bool e = ⎣ true ⎦
    -> ~ cop2bool e ⊑ ⎣ wTA false ⎦.
Proof.
  intros A B.
  eapply op2bool_cop2bool_not_some; eauto. congruence.
Qed.

Lemma op2bool_cop2bool_not_some'' e
  : op2bool e = ⎣ false ⎦
    -> ~ cop2bool e ⊑ ⎣ wTA true ⎦.
Proof.
  intros A B.
  eapply op2bool_cop2bool_not_some; eauto. congruence.
Qed.

Hint Resolve op2bool_cop2bool_not_some
     op2bool_cop2bool_not_some' op2bool_cop2bool_not_some''.

Transparent uceq.

Ltac std_ind_inst :=
  match goal with
    [ H : forall y : stmt, size y < size (stmtLet _ _ ?s) -> _ |- _ ] =>
    specialize (H s ltac:(eauto))
  end.

Ltac std_ind_dcr :=
  match goal with
  | [ H : forall y : stmt, size y < size (stmtLet _ _ ?s) -> _ |- _ ] =>
    edestruct (H s ltac:(eauto)); eauto; dcr
  end.

Opaque poLe.

Lemma reachability_trueIsCalled Lv s slv l
  : reachability cop2bool Sound Lv s slv
    -> isCalled true s l
    -> exists b, get Lv (counted l) b /\ (poLe (getAnn slv) b).
Proof.
  destruct l; simpl.
  revert Lv slv n.
  sind s; destruct s; intros Lv slv n UC IC; inv UC; inv IC;
    simpl in *; subst; simpl in *; try std_ind_dcr;
      eauto 20 using op2bool_cop2bool_not_some.
  - edestruct (IH s1); dcr; eauto 20.
    setoid_rewrite H2; eauto using op2bool_cop2bool_not_some.
  - edestruct (IH s2); dcr; eauto 20.
    setoid_rewrite H3; eauto using op2bool_cop2bool_not_some.
  - destruct l'.
    clear_trivial_eqs.
    exploit (IH s); eauto; dcr.
    setoid_rewrite H3. setoid_rewrite H7.
    clear H3 H7 UC H9 H1 alt b.
    general induction H5.
    + inv_get. eexists; split; eauto.
    + inv_get.
      exploit H4; try eassumption.
      eapply IH in H3; [|eauto|eauto].
      dcr. inv_get.
      edestruct IHcallChain; clear IHcallChain; try eapply H8; dcr; eauto.
Qed.

Lemma reachability_analysis_complete_setTopAnn ceval BL s a b
      (LE:poLe (getAnn a) b)
  : reachability ceval Complete BL s a
    -> reachability ceval Complete BL s (setTopAnn a b).
Proof.
  intros RCH; general induction RCH; simpl in *;
    eauto using reachability.
  - econstructor; intros; eauto. simpl.
    + intros. destruct b, b0; eauto.
  - econstructor; simpl; intros; eauto.
    + exploit H; eauto.
    + exploit H0; eauto.
  - econstructor; simpl; intros; eauto.
    + exploit H4; eauto.
Qed.


Lemma reachability_sTA_inv (BL : 〔bool〕)
         (s : stmt) (a : ann bool)
  : reachability cop2bool Complete BL s (setTopAnn a (getAnn a)) ->
    reachability cop2bool Complete BL s a.
Proof.
  intros. rewrite setTopAnn_eta in H; eauto.
Qed.
