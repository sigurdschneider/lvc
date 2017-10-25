Require Import SimTactics SimCompanion IL paco3 OptionR.
Require Export ILStateType.

Set Implicit Arguments.

Lemma sim_let_op X (IST:ILStateType X) X' (IST':ILStateType X')
      i r (L:X) (L':X') V V' x x' e e' s s'
      (EQ:op_eval V e = op_eval V' e')
      (SIM: forall v, op_eval V e = Some v
                 -> Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r i
                                     (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim_gen (Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r)
            i (L, V, stmtLet x (Operation e) s) (L', V', stmtLet x' (Operation e') s').
Proof.
  case_eq (op_eval V e); intros.
  * eapply SimSilent; [ eapply plus2O
                      | eapply plus2O
                      | ].
    eapply step_let_op; eauto. eauto.
    eapply step_let_op. rewrite <- EQ. eauto. eauto.
    eapply SIM; eauto.
  * eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
      [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply let_op_normal; eauto.
    eapply let_op_normal; rewrite <- EQ; eauto.
Qed.

Lemma sim_let_call X (IST:ILStateType X) X' (IST':ILStateType X')
      i r (L:X) (L':X') V V' x x' f Y Y' s s'
      (EQ: omap (op_eval V) Y = omap (op_eval V') Y')
      (SIM: forall v,  Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r i
                                    (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim_gen (Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r) i
            (L, V, stmtLet x (Call f Y) s) (L', V', stmtLet x' (Call f Y') s').
Proof.
  case_eq (omap (op_eval V) Y); intros.
  * pose proof H as H'. rewrite EQ in H'.
    eapply SimExtern;
      [ eapply star2_refl
      | eapply star2_refl
      | step_activated; eauto 20 using step_let_call
      | step_activated; eauto 20 using step_let_call | |].
    eapply step_let_call; eauto.
    intros ? ? STEP; eapply let_call_inversion in STEP; dcr; subst; eexists; split; try eapply step_let_call; eauto.
    rewrite <- EQ; eauto.
    intros ? ? STEP; eapply let_call_inversion in STEP; dcr; subst; eexists; split; try eapply step_let_call; eauto.
    rewrite EQ; eauto.
  * eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply let_call_normal; eauto.
    eapply let_call_normal; rewrite <- EQ; eauto.
Qed.

Lemma sim_cond X (IST:ILStateType X) X' (IST':ILStateType X')
      i r (L:X) (L':X') V V' e e' s1 s1' s2 s2'
      (EQ: op_eval V e = op_eval V' e')
      (SIM1: forall v, op_eval V e = Some v -> val2bool v = true ->
                  Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r i
                                    (L, V, s1) (L', V', s1'))
      (SIM2: forall v, op_eval V e = Some v -> val2bool v = false ->
                  Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r i
                                    (L, V, s2) (L', V', s2'))
  : sim_gen (Tower3.companion3 (sim_gen (S':=X' * onv val * stmt)) r) i
            (L, V, stmtIf e s1 s2) (L', V', stmtIf e' s1' s2').
Proof.
  case_eq (op_eval V e); intros.
  - case_eq (val2bool v); intros.
    + eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                        | eapply plus2O; [|eapply filter_tau_nil_eq]
                        | eapply SIM1; eauto];
      eapply step_cond_true; eauto. rewrite <- EQ; eauto.
    + eapply SimSilent; [ eapply plus2O; [|eapply filter_tau_nil_eq]
                        | eapply plus2O; [|eapply filter_tau_nil_eq]
                        | eapply SIM2; eauto];
      eapply step_cond_false; eauto. rewrite <- EQ; eauto.
  - eapply SimTerm; [| eapply star2_refl | eapply star2_refl | | ];
      [ simpl | | ].
    rewrite !result_none; isabsurd; eauto.
    eapply cond_normal; eauto.
    eapply cond_normal; eauto. rewrite <- EQ; eauto.
Qed.
