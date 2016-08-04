Require Import Sim IL paco3.

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
    | [ H : omap (exp_eval ?E) ?Y = Some ?vl
        |- activated (_, ?E, stmtExtern ?x ?f ?Y ?s) ] =>
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
