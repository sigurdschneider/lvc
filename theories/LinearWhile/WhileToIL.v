Require Import List.
Require Export Util Get Drop Var Val Isa.Op IL.Exp
        Env Map CSet AutoIndTac MoreList OptionMap.
Require Export IL.Events SizeInduction SmallStepRelations StateType.
Require Import SetOperations While IL.
Require Import Sim SimTactics SimI Infra.Status Position ILN Sawtooth Program.Tactics.


Program Fixpoint whileToILI (s:list statement) (cont:nat) {measure (size s)} : stmt :=
  match s with
  | WhileLet x e::p =>
    stmtLet x e (whileToILI p cont)
  | WhileCond e s t::p =>
    stmtFun ((nil, whileToILI p (S cont))::nil)
            (stmtIf e (whileToILI s 0) (whileToILI t 0))
  | WhileWhile e s::p =>
    stmtFun ((nil, (stmtIf e
                           (whileToILI s 0)
                           (whileToILI p (S cont))))::nil)
            (stmtApp (LabI 0) nil)
  | WhileReturn e::p => stmtReturn e
  | nil => stmtApp (LabI cont) nil
  end.


Require Import Program.Equality Program.Wf.

Lemma whileToILI_nil cont
  :  whileToILI nil cont = stmtApp (LabI cont) nil.
Proof.
  unfold whileToILI at 1. unfold whileToILI_func.
  WfExtensionality.unfold_sub whileToILI (whileToILI nil cont).
  reflexivity.
Qed.

Lemma whileToILI_let x e p cont
  :  whileToILI (WhileLet x e::p) cont = stmtLet x e (whileToILI p cont).
Proof.
  unfold whileToILI at 1. unfold whileToILI_func.
  WfExtensionality.unfold_sub whileToILI (whileToILI (WhileLet x e::p) cont).
  reflexivity.
Qed.

Lemma whileToILI_return e p cont
  :  whileToILI (WhileReturn e::p) cont = stmtReturn e.
Proof.
  unfold whileToILI at 1. unfold whileToILI_func.
  WfExtensionality.unfold_sub whileToILI (whileToILI (WhileReturn e::p) cont).
  reflexivity.
Qed.

Lemma whileToILI_cond e s t p cont
  :  whileToILI (WhileCond e s t :: p) cont
     = stmtFun ((nil, whileToILI p (S cont))::nil)
               (stmtIf e (whileToILI s 0) (whileToILI t 0)).
Proof.
  unfold whileToILI at 1. unfold whileToILI_func.
  WfExtensionality.unfold_sub whileToILI (whileToILI (WhileCond e s t :: p) cont).
  reflexivity.
Qed.

Lemma whileToILI_while e s p cont
  :  whileToILI (WhileWhile e s:: p) cont
     =  stmtFun ((nil, (stmtIf e
                           (whileToILI s 0)
                           (whileToILI p (S cont))))::nil)
                (stmtApp (LabI 0) nil).
Proof.
  unfold whileToILI at 1. unfold whileToILI_func.
  WfExtensionality.unfold_sub whileToILI (whileToILI (WhileWhile e s::p) cont).
   reflexivity.
Qed.

Lemma whileToILI_correct_while' r (L:list IL.I.block) E e s p (t:stmt)
      (IH:forall q (L:IL.I.labenv) E r,
          (exists v, op_eval E e = Some v /\ val2bool v = true) ->
          sawtooth L ->
          (forall E, sim r Bisim
                      (E, q) (L, E, stmtApp (LabI 0) nil))
          -> sim r Bisim (E, s ++ q) (L, E, whileToILI s 0))
      (SM:sawtooth L)
      v (EV:op_eval E e = Some v)
      (TR:val2bool v = true)
      (CONT:forall E0,
          sim r Bisim
                   (E0, p) (IL.I.mkBlock 0 (nil, stmtIf e (whileToILI s 0) t) :: L, E0, t))
  :  sim r Bisim (E, s ++ WhileWhile e s :: p)
         (IL.I.mkBlock 0 (nil, stmtIf e (whileToILI s 0) t) :: L, E,
          whileToILI s 0).
Proof.
  revert_all. pcofix CIH. intros.
  eapply (IH (WhileWhile e s :: p)); eauto.
  - intros.
    eapply (sawtooth_I_mkBlocks ((nil, stmtIf e (whileToILI s 0) t)::nil)); eauto.
  - intros. dcr.
    + case_eq (op_eval E0 e); intros.
      * case_eq (val2bool v0); intros.
        -- pone_step_right; simpl; eauto using get. simpl.
           pfold; eapply SimSilent; [ eapply plus2O; try eapply StepWhileT; eauto
                                    | eapply plus2O; single_step; eauto using get
                                    | ].
           right. eapply CIH; eauto.
        -- pone_step_right; simpl; eauto using get. simpl.
           pone_step; simpl; eauto using get.
           left. eapply paco3_mon. eapply CONT. eauto.
      * pone_step_right; simpl; eauto using get; simpl.
        pno_step.
Qed.

Lemma whileToILI_correct r (L:IL.I.labenv) E p q cont
      (SM:sawtooth L)
  :  (forall E, sim r Bisim
               (E, q) (L, E, stmtApp (LabI cont) nil))
    -> sim r Bisim (E, p ++ q) (L, E, whileToILI p cont).
Proof.
  revert_except p.
  sind p; destruct p; simpl; intros.
  { rewrite whileToILI_nil. simpl. eauto. }
  destruct s; simpl.
  - rewrite whileToILI_cond.
    pone_step_right.
    case_eq (op_eval E e); intros.
    + case_eq (val2bool v); intros.
      * pfold; eapply SimSilent; [ eapply plus2O; econstructor; eauto
                                 | eapply plus2O; econstructor; eauto
                                 | ].
        left. eapply IH; eauto; intros.
        pone_step_right; [ | econstructor | reflexivity| reflexivity].
        eapply IH; eauto. eapply sawtooth_I_mkBlocks; eauto.
        intros.
        eapply stmtApp_sim_tl; eauto.
        eapply sawtooth_smaller; eauto.
      * pfold; eapply SimSilent; [ eapply plus2O; try eapply StepIfF; eauto
                                 | eapply plus2O; single_step; eauto
                                 | ].
        left. eapply IH; eauto. intros.
        pone_step_right; [ | econstructor | reflexivity| reflexivity].
        eapply IH; eauto. eapply sawtooth_I_mkBlocks; eauto.
        intros.
        eapply stmtApp_sim_tl; eauto.
        eapply sawtooth_smaller; eauto.
    + clear IH.
      pno_step.
  - rewrite whileToILI_while.
    pone_step_right.
    + case_eq (op_eval E e); intros.
      * case_eq (val2bool v); intros.
        -- pone_step_right; simpl; eauto using get. simpl.
           pfold; eapply SimSilent;
             [ eapply plus2O; try eapply StepWhileT; eauto
             | eapply plus2O; single_step; simpl; eauto using get
             | ]. simpl.
           left.
           eapply whileToILI_correct_while'; eauto.
           ++ intros. eapply IH; eauto.
             eapply (sawtooth_I_mkBlocks ((nil, stmtIf e (whileToILI s 0) _)::nil)); eauto.
             intros.
             eapply stmtApp_sim_tl; eauto.
             eapply sawtooth_smaller; eauto.
        -- intros.
           pone_step_right; simpl; eauto using get. simpl.
           pone_step; simpl; eauto using get.
           left. eapply IH; eauto.
           eapply (sawtooth_I_mkBlocks ((nil, stmtIf e (whileToILI s 0) _)::nil)); eauto.
           intros. eapply stmtApp_sim_tl; eauto.
           eapply sawtooth_smaller; eauto.
      * pone_step_right; simpl; eauto using get. simpl.
        pno_step.
  - rewrite whileToILI_let.
    destruct e.
    + case_eq (op_eval E e); intros.
      * pfold; eapply SimSilent; [ eapply plus2O; econstructor
                                 | eapply plus2O; econstructor
                                 | ]; eauto.
        left. eapply IH; eauto.
      * pno_step.
    + case_eq (omap (op_eval E) Y); intros.
      * pextern_step.
        -- econstructor; eauto. eexists. econstructor; eauto.
        -- left. eapply IH; eauto.
        -- assert (l = vl) by congruence; subst.
           left. eapply IH; eauto.
      * pno_step.
  - rewrite whileToILI_return.
    pfold; eapply SimTerm; [
    | eapply star2_refl
    | eapply star2_refl
    | stuck
    | stuck ]. reflexivity.
    Grab Existential Variables.
    eapply default_val.
Qed.
