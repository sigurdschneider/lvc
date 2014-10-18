Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export EventsActivated StateType paco Equiv Bisim Sim.

Set Implicit Arguments.
Unset Printing Records.

Inductive extevent :=
  | EEvt (evt:event)
  | EvtTerminate (res:option val).


Inductive produces {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> produces σ' L
      -> produces σ  L
  | producesExtern (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> produces σ' L
      -> produces σ (EEvt evt::L)
  | producesTerm (σ:S) (σ':S) r
    : result σ' = r
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces σ (EvtTerminate r::nil).


Lemma produces_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces σ' L -> produces σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma no_activated_tau_step {S} `{StateType S} (σ σ':S)
 :  activated σ
  -> step σ EvtTau σ'
  -> False.
Proof.
  intros. destruct H0 as [? [? ?]].
  eapply step_internally_deterministic in H0; eauto.
  dcr; congruence.
Qed.

Lemma bisim_produces {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, produces sigma L -> produces σ' L.
Proof.
  intros. general induction H2.
  - eapply bisim_bisim' in H3.
    eapply IHproduces; eauto.
    eapply bisim'_bisim. eapply bisim'_reduction_closed_1; eauto.
    eapply (S_star2 _ _ H0). eapply star2_refl.
  - eapply bisim_bisim' in H4.
    eapply bisim'_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    destruct evt.
    + eapply produces_star2_silent; eauto.
      edestruct H6; eauto. destruct H8.
      econstructor 2. eauto. eapply H8.
      eapply IHproduces; eauto.
      eapply bisim'_bisim. eapply H9.
    + exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply bisim_bisim' in H4. eapply bisim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 3; [ | eauto | eauto]. congruence.
Qed.

Lemma bisim_trace_eq {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, produces sigma L <-> produces σ' L.
Proof.
  split; eapply bisim_produces; eauto.
  eapply bisim_sym; eauto.
Qed.

(*
Lemma sim_produces {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim σ σ' -> forall L, produces σ' L -> produces σ L.
Proof.
  intros. general induction H2.
  - eapply sim_sim' in H3.
    eapply IHproduces; eauto.
    eapply sim'_sim. eapply sim'_reduction_closed_2; eauto.
    eapply (S_star2 _ _ H). eapply star2_refl.
  - eapply sim_sim' in H4.
    exploit (sim'_activated_2 H H4); eauto.
    destruct X as [? [? [[? []]|]]].
    + destruct evt.
      * eapply produces_star2_silent; eauto.
        edestruct H7; eauto. destruct H9.
        econstructor 2. eauto. eapply H9.
        eapply IHproduces; eauto.
        eapply sim'_sim. eapply H10.
      * exfalso; eapply (no_activated_tau_step _ H H1); eauto.
    +
  - eapply sim_sim' in H4. eapply sim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 3; [ | eauto | eauto].
    rewrite <- H6; eauto.
Qed.
*)




(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
