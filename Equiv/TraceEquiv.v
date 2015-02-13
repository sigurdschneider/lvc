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

Inductive produces_prefix {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesPrefixSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> produces_prefix σ' L
      -> produces_prefix σ  L
  | producesPrefixExtern (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> produces_prefix σ' L
      -> produces_prefix σ (EEvt evt::L)
  | producesPrefixTerm (σ:S) (σ':S) v
    : result σ' = Some v
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces_prefix σ (EvtTerminate (Some v)::nil)
  | producesPrefixPrefix (σ:S)
    : produces_prefix σ nil.

Inductive produces_nondet {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesNondetSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> produces_nondet σ' L
      -> produces_nondet σ  L
  | producesNondetExtern (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> produces_nondet σ' L
      -> produces_nondet σ (EEvt evt::L)
  | producesNondetTerm (σ:S) (σ':S) v
    : result σ' = Some v
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces_nondet σ (EvtTerminate (Some v)::nil)
  | producesNondetPrefix (σ:S) (σ':S) L
    : result σ' = None
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces_nondet σ L.

Lemma produces_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces σ' L -> produces σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma produces_prefix_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces_prefix σ' L -> produces_prefix σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma produces_nondet_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces_nondet σ' L -> produces_nondet σ L.
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


Lemma sim_produces {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim σ σ' -> forall L, produces_prefix σ L -> produces_prefix σ' L.
Proof.
  intros. general induction H2.
  - eapply sim_sim' in H3.
    eapply IHproduces_prefix; eauto.
    eapply sim'_sim. eapply sim'_reduction_closed_1; eauto.
    eapply (S_star2 _ _ H0). eapply star2_refl.
  - eapply sim_sim' in H4.
    exploit (sim'_activated H0 H4); eauto.
    destruct X as [? [? [? [?]]]].
    + destruct evt.
      * eapply produces_prefix_star2_silent; eauto.
        edestruct H7; eauto. destruct H9.
        econstructor 2. eauto. eapply H9.
        eapply IHproduces_prefix; eauto.
        eapply sim'_sim. eapply H10.
      * exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply sim_sim' in H4. eapply sim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. rewrite H0. econstructor 3; [ | eauto | eauto]. congruence.
    congruence.
  - eapply producesPrefixPrefix.
Qed.


Lemma sim_produces' {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim σ σ' -> forall L, produces σ' L -> produces_nondet σ L.
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
      * eapply produces_nondet_star2_silent; eauto.
        edestruct H7; eauto. destruct H9.
        econstructor 2. eauto. eapply H9.
        eapply IHproduces; eauto.
        eapply sim'_sim. eapply H10.
      * exfalso; eapply (no_activated_tau_step _ H H1); eauto.
    + dcr. econstructor 4; eauto.
  - eapply sim_sim' in H4. eapply sim'_terminate_2 in H4; eauto; try congruence.
    destruct H4 as [? [? [? [|]]]].
    + case_eq (result σ'); intros.
      * econstructor 3; [ | eauto | eauto]. congruence.
      * eapply producesNondetPrefix; eauto. congruence.
    + eapply producesNondetPrefix; eauto.
Qed.

CoInductive diverges S `{StateType S} : S -> Prop :=
| DivergesI σ σ'
  : step σ EvtTau σ'
    -> diverges σ'
    -> diverges σ.

CoInductive diverges_gen S `{StateType S} (r:S -> Prop) : S -> Prop :=
| DivergesGenI σ σ'
  : step σ EvtTau σ'
    -> r σ'
    -> diverges_gen r σ.

Hint Constructors diverges_gen.

Definition diverges' S `{StateType S} : S -> Prop :=
  paco1 (@diverges_gen S _) bot1.

Hint Unfold diverges'.

Lemma diverges_gen_mon S `{StateType S}
: monotone1 (@diverges_gen S _).
Proof.
  hnf; intros. inv IN.
  - econstructor 1; eauto.
Qed.

Hint Resolve diverges_gen_mon : paco.

Lemma diverges_diverges' S `{StateType S} (σ:S)
: diverges σ -> diverges' σ.
Proof.
  revert σ. pcofix CIH.
  intros. pfold.
  inv H1.
  econstructor; eauto.
Qed.

Lemma diverges'_diverges S `{StateType S} (σ:S)
  : diverges' σ -> diverges σ.
Proof.
  revert σ.
  cofix COH; intros.
  assert (diverges_gen (paco1 (diverges_gen (S:=S)) bot1 \1/ bot1) σ).
  punfold H0.
  inv H1.
  econstructor; eauto.
  destruct H3; eauto. inv H3.
Qed.

Lemma diverges_reduction_closed S `{StateType S} (σ σ':S)
: diverges σ -> star2 step σ nil σ'  -> diverges σ'.
Proof.
  intros. general induction H1; eauto using diverges.
  destruct yl, y; simpl in *; try congruence.
  inv H2.
  exploit step_internally_deterministic.
  eapply H. eapply H3. dcr; subst.
  eapply IHstar2; eauto.
Qed.

Lemma diverges_never_activated S `{StateType S} (σ:S)
: activated σ -> diverges σ -> False.
Proof.
  intros. inv H0. inv H1. dcr.
  exploit step_internally_deterministic.
  eapply H3. eapply H5. dcr; congruence.
Qed.

Lemma diverges_never_terminates S `{StateType S} (σ:S)
: normal2 step σ -> diverges σ -> False.
Proof.
  intros. inv H1. eapply H0. firstorder.
Qed.

Lemma bisim_sound_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: bisim σ σ' -> diverges σ -> diverges σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1.
  - eapply plus2_destr_nil in H4. dcr.
    econstructor. eauto.
    eapply COH; eauto.
    eapply bisim'_bisim.
    eapply bisim'_reduction_closed.
    eapply bisim_bisim'. eapply H1. econstructor.
    eapply (S_star2 EvtTau); eauto. econstructor.
  - eapply diverges_reduction_closed in H3.
    + exfalso. eapply (diverges_never_activated H5); eauto.
    + eapply H2.
  - eapply diverges_reduction_closed in H4.
    + exfalso. eapply (diverges_never_terminates H6); eauto.
    + eapply H2.
Qed.

CoInductive stream (A : Type) : Type :=
| sil : stream A
| sons : A -> stream A -> stream A.

Arguments sil [A].

CoInductive coproduces {S} `{StateType S} : S -> stream extevent -> Prop :=
| CoProducesExtern (σ σ' σ'':S) evt L :
    star2 step σ nil σ'
      -> activated σ'
      -> step σ' evt σ''
      -> coproduces σ' L
      -> coproduces σ (sons (EEvt evt) L)
| CoProducesSilent (σ:S) :
    diverges σ
    -> coproduces σ sil
| CoProducesTerm (σ:S) (σ':S) r
  : result σ' = r
    -> star2 step σ nil σ'
    -> normal2 step σ'
    -> coproduces σ (sons (EvtTerminate r) sil).

Lemma coproduces_reduction_closed_step S `{StateType S} (σ σ':S) L
: coproduces σ L -> step σ EvtTau σ'  -> coproduces σ' L.
Proof.
  intros. inv H0.
  - exploit activated_star_reach. eapply H3. eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
    econstructor. eapply X. eauto. eauto. eauto.
  - econstructor. eapply diverges_reduction_closed; eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
  - exploit star2_reach_normal. eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
    eapply H. eauto.
    econstructor; try eapply X. eauto. eauto.
Qed.

Lemma coproduces_reduction_closed S `{StateType S} (σ σ':S) L
: coproduces σ L -> star2 step σ nil σ'  -> coproduces σ' L.
Proof.
  intros. general induction H1; eauto using coproduces. eauto.
  destruct yl, y; simpl in *; try congruence.
  eapply IHstar2; eauto.
  eapply coproduces_reduction_closed_step; eauto.
Qed.

Lemma bisim_coproduces {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, coproduces sigma L -> coproduces σ' L.
Proof.
  revert sigma σ'. cofix COH; intros.
  inv H2.
  - assert (bisim' σ'0 σ').
    eapply bisim'_reduction_closed. eapply (bisim_bisim' H1).
    eauto. econstructor.
    exploit (bisim'_activated H4 H7). dcr.
    edestruct H10. eauto. dcr.
    econstructor; try eapply H8. eauto. eapply H11.
    eapply COH; eauto.
    eapply bisim'_bisim. eapply (bisim'_reduction_closed H7); eauto.
    econstructor.
  - econstructor. eapply (bisim_sound_diverges H1); eauto.
  - exploit (bisim'_terminate H4 H5 (bisim_bisim' H1)).
    dcr.
    econstructor; eauto.
Qed.




(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
