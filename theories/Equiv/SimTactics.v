Require NonParametricBiSim.
Require Import Sim IL paco3.
Require Export ILStateType.

(** * Admissible Rules and Tactics *)

(** ** Tactics *)

Ltac pone_step := pfold; eapply SimSilent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac pone_step_left :=
  eapply sim_expansion_closed; [ | eapply star2_silent; single_step | eapply star2_refl ].

Ltac pone_step_right :=
  eapply sim_expansion_closed; [ | eapply star2_refl | eapply star2_silent; single_step ].

Ltac pno_step :=
  pfold; eapply SimTerm;
  [ | eapply star2_refl | eapply star2_refl | | ];
  [ repeat get_functional; try reflexivity
  | repeat get_functional; stuck2
  | repeat get_functional; stuck2 ].

Ltac step_activated :=
  match goal with
  | [ H : omap (op_eval ?E) ?Y = Some ?vl
      |- activated (_, ?E, stmtLet ?x (Call ?f ?Y) ?s) ] =>
    eexists (ExternI f vl default_val); eexists; try (now (econstructor; eauto))
  end.

Ltac pextern_step :=
  let STEP := fresh "STEP" in
  pfold; eapply SimExtern;
  [ eapply star2_refl
  | eapply star2_refl
  | try step_activated
  | try step_activated
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  ].

Ltac pno_step_left :=
  pfold; econstructor 3; [ | eapply star2_refl|]; [ reflexivity | ]; stuck2.


Ltac perr :=
  pfold; eapply SimErr;
  [ | eapply star2_refl | ];
  [ repeat get_functional; try reflexivity
  | repeat get_functional; stuck2 ].

Set Implicit Arguments.

(** ** Admissible Rules *)

Lemma sim_let_op X (IST:ILStateType X) i r (L L':X) V V' x x' e e' s s'
      (EQ:op_eval V e = op_eval V' e')
      (SIM: forall v, op_eval V e = Some v
                 -> (sim r \3/ r) i (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim r i (L, V, stmtLet x (Operation e) s) (L', V', stmtLet x' (Operation e') s').
Proof.
  case_eq (op_eval V e); intros.
  * pfold; eapply SimSilent; [ eapply plus2O
                              | eapply plus2O
                              | ].
    eapply step_let_op; eauto. eauto.
    eapply step_let_op. rewrite <- EQ. eauto. eauto.
    eapply SIM; eauto.
  * pfold. eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply let_op_normal; eauto.
    eapply let_op_normal; rewrite <- EQ; eauto.
Qed.

Lemma sim_let_call X (IST:ILStateType X) i r (L L':X) V V' x x' f Y Y' s s'
      (EQ: omap (op_eval V) Y = omap (op_eval V') Y')
      (SIM: forall v, (sim r \3/ r) i (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim r i (L, V, stmtLet x (Call f Y) s) (L', V', stmtLet x' (Call f Y') s').
Proof.
  case_eq (omap (op_eval V) Y); intros.
  * pose proof H as H'. rewrite EQ in H'.
    pfold; eapply SimExtern;
      [ eapply star2_refl
      | eapply star2_refl
      | step_activated; eauto using step_let_call
      | step_activated; eauto using step_let_call | |];
      intros ? ? STEP; eapply let_call_inversion in STEP; dcr; subst; eexists; split; try eapply step_let_call; eauto.
    rewrite <- EQ; eauto.
    rewrite EQ; eauto.
  * pfold. eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply let_call_normal; eauto.
    eapply let_call_normal; rewrite <- EQ; eauto.
Qed.

Lemma sim_cond X (IST:ILStateType X) i r (L L':X) V V' e e' s1 s1' s2 s2'
      (EQ: op_eval V e = op_eval V' e')
      (SIM1: forall v, op_eval V e = Some v -> val2bool v = true ->
                  (sim r \3/ r) i (L, V, s1) (L', V', s1'))
      (SIM2: forall v, op_eval V e = Some v -> val2bool v = false ->
                 (sim r \3/ r) i (L, V, s2) (L', V', s2'))
  : sim r i (L, V, stmtIf e s1 s2) (L', V', stmtIf e' s1' s2').
Proof.
  case_eq (op_eval V e); intros.
  - case_eq (val2bool v); intros.
    + pfold; eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply SIM1; eauto];
      eapply step_cond_true; eauto. rewrite <- EQ; eauto.
    + pfold; eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply plus2O; [|eapply filter_tau_nil_eq]
                                | eapply SIM2; eauto];
      eapply step_cond_false; eauto. rewrite <- EQ; eauto.
  - pfold. eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply cond_normal; eauto.
    eapply cond_normal; eauto. rewrite <- EQ; eauto.
Qed.

Lemma sim_cond_left_true X (IST:ILStateType X) i r (L L':X) V V' e s1 s2 s1' v
      (EQ: op_eval V e = Some v) (vt:val2bool v = true)
      (SIM1: sim r i (L, V, s1) (L', V', s1'))
  : sim r i (L, V, stmtIf e s1 s2) (L', V', s1').
Proof.
  eapply sim_expansion_closed; [ eapply SIM1
                                | eapply star2_silent; [| eapply star2_refl]
                                | eapply star2_refl].
  eapply step_cond_true; eauto.
Qed.

Lemma sim_cond_left_false X (IST:ILStateType X) i r (L L':X) V V' e s1 s2 s2' v
      (EQ: op_eval V e = Some v) (vt:val2bool v = false)
      (SIM1: sim r i (L, V, s2) (L', V', s2'))
  : sim r i (L, V, stmtIf e s1 s2) (L', V', s2').
Proof.
  eapply sim_expansion_closed; [ eapply SIM1
                                | eapply star2_silent; [| eapply star2_refl]
                                | eapply star2_refl].
  eapply step_cond_false; eauto.
Qed.

(** *** Conditional Elimination *)

Lemma sim_if_elim X (IST:ILStateType X) i r (L L':X) V V' e s1 s1' s2 s2'
      (EQ: op2bool e = None -> op_eval V e = op_eval V' e)
      (SIM1: forall v, op_eval V e = Some v -> val2bool v = true -> op2bool e <> Some false ->
                  (sim r) i (L, V, s1) (L', V', s1'))
      (SIM2: forall v, op_eval V e = Some v -> val2bool v = false -> op2bool e <> Some true ->
                  (sim r) i (L, V, s2) (L', V', s2'))
  : sim r i (L, V, stmtIf e s1 s2)
    (L', V',
    if [op2bool e = ⎣ true ⎦] then s1' else if [
    op2bool e = ⎣ false ⎦] then s2' else
    stmtIf e s1' s2').
Proof.
  repeat cases.
    + edestruct (op2bool_val2bool V); eauto; dcr.
      eapply sim_expansion_closed; [ eapply SIM1; eauto
                                    | eapply star2_silent; [| eapply star2_refl]
                                    | eapply star2_refl].
      eapply step_cond_true; eauto.
    + edestruct (op2bool_val2bool V); eauto; dcr.
      eapply sim_expansion_closed; [ eapply SIM2; eauto
                                    | eapply star2_silent; [| eapply star2_refl]
                                    | eapply star2_refl].
      eapply step_cond_false; eauto.
    + eapply (sim_cond IST); intros; try left; eauto.
Qed.
