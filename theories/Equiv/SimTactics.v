Require Import Sim IL paco3.
Require Export ILStateType.

Ltac one_step := eapply simSilent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac no_step := eapply simTerm;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2
                | stuck2  ].

Ltac err_step := eapply simErr;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2  ].

Ltac step_activated :=
  match goal with
    | [ H : omap (op_eval ?E) ?Y = Some ?vl
        |- activated (_, ?E, stmtLet ?x (Call ?f ?Y) ?s) ] =>
      eexists (ExternI f vl default_val); eexists; try (now (econstructor; eauto))
  end.

Ltac extern_step :=
  let STEP := fresh "STEP" in
  eapply simExtern;
    [ eapply star2_refl
    | eapply star2_refl
    | try step_activated
    | try step_activated
    | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
    | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
    ].


Ltac pone_step := pfold; eapply sim'Silent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac pone_step_left :=
  eapply sim'_expansion_closed; [ | eapply star2_silent; single_step | eapply star2_refl ].

Ltac pone_step_right :=
  eapply sim'_expansion_closed; [ | eapply star2_refl | eapply star2_silent; single_step ].

Ltac pno_step :=
  pfold; eapply sim'Term;
  [ | eapply star2_refl | eapply star2_refl | | ];
  [ repeat get_functional; try reflexivity
  | repeat get_functional; stuck2
  | repeat get_functional; stuck2 ].

Ltac pextern_step :=
  let STEP := fresh "STEP" in
  pfold; eapply sim'Extern;
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
  pfold; eapply sim'Err;
  [ | eapply star2_refl | ];
  [ repeat get_functional; try reflexivity
  | repeat get_functional; stuck2 ].

Set Implicit Arguments.

Lemma sim_let_op X (IST:ILStateType X) i r (L L':X) V V' x x' e e' s s'
      (EQ:op_eval V e = op_eval V' e')
      (SIM: forall v, op_eval V e = Some v
                 -> (sim'r r \3/ r) i (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim'r r i (L, V, stmtLet x (Operation e) s) (L', V', stmtLet x' (Operation e') s').
Proof.
  case_eq (op_eval V e); intros.
  * pfold; eapply sim'Silent; [ eapply plus2O
                              | eapply plus2O
                              | ].
    eapply step_let_op; eauto. eauto.
    eapply step_let_op. rewrite <- EQ. eauto. eauto.
    eapply SIM; eauto.
  * pfold. eapply sim'Term; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !let_result; eauto.
    eapply let_op_normal; eauto.
    eapply let_op_normal; rewrite <- EQ; eauto.
Qed.

Lemma sim_let_call X (IST:ILStateType X) i r (L L':X) V V' x x' f Y Y' s s'
      (EQ: omap (op_eval V) Y = omap (op_eval V') Y')
      (SIM: forall v, (sim'r r \3/ r) i (L, V [x <- ⎣ v ⎦], s) (L', V' [x' <- ⎣ v ⎦], s'))
  : sim'r r i (L, V, stmtLet x (Call f Y) s) (L', V', stmtLet x' (Call f Y') s').
Proof.
  case_eq (omap (op_eval V) Y); intros.
  * pose proof H as H'. rewrite EQ in H'.
    pfold; eapply sim'Extern;
      [ eapply star2_refl
      | eapply star2_refl
      | step_activated; eauto using step_let_call
      | step_activated; eauto using step_let_call | |];
      intros ? ? STEP; eapply let_call_inversion in STEP; dcr; subst; eexists; split; try eapply step_let_call; eauto.
    rewrite <- EQ; eauto.
    rewrite EQ; eauto.
  * pfold. eapply sim'Term; [| eapply star2_refl | eapply star2_refl | | ];
             [ simpl | | ].
    rewrite !let_result; eauto.
    eapply let_call_normal; eauto.
    eapply let_call_normal; rewrite <- EQ; eauto.
Qed.
