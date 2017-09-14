Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType StateTypeProperties.
Require Import Sim Divergence TraceEquiv.

Set Implicit Arguments.
Unset Printing Records.

Lemma sim_terminate {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2:S2) v
: star2 step σ1 nil σ1'
  -> normal2 step σ1'
  -> sim bot3 Sim σ1 σ2
  -> result σ1' = Some v
  -> exists σ2', star2 step σ2 nil σ2' /\ normal2 step σ2' /\ result σ2' = Some v.
Proof.
  intros. general induction H1.
  - pinversion H3; subst.
    + exfalso. eapply H2. inv H1; do 2 eexists; eauto.
    + exfalso. eapply star2_normal in H1; eauto. subst.
      eapply (activated_normal _ H6); eauto.
    + eapply star2_normal in H5; eauto; subst.
      eexists; repeat split; eauto; congruence.
    + eapply normal_star_eq in H2; eauto. subst.
      eexists σ2'.
      eexists; repeat split; eauto. congruence.
  - destruct y; isabsurd. simpl.
    eapply IHstar2; eauto.
    eapply sim_reduction_closed_1; eauto using star2, star2_silent.
    Grab Existential Variables. eauto.
Qed.

Inductive prefixSpec (b:bool) {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesPrefixSpecSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> prefixSpec b σ' L
      -> prefixSpec b σ  L
  | producesPrefixSpecExtern (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> prefixSpec b σ' L
      -> prefixSpec b σ (EEvtExtern evt::L)
  | producesPrefixSpecTerm (σ:S) (σ':S) r
    : result σ' = Some r
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> prefixSpec b σ (EEvtTerminate (Some r)::nil)
  | producesPrefixSpecStuck (σ:S) (σ':S) L
    : result σ' = None
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> b
      -> prefixSpec b σ L
  | producesPrefixSpecPrefixSpec (σ:S)
    : prefixSpec b σ nil.

Lemma prefixSpec_star2_silent b {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   prefixSpec b σ' L -> prefixSpec b σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma prefixSpec_star2_silent' b {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   prefixSpec b σ L -> prefixSpec b σ' L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    eapply IHstar2; eauto.
    inv H2.
    + relsimpl; eauto.
    + relsimpl.
    + exploit star2_reach_silent_step; eauto. eapply H.
      destruct H6; subst.
      * exfalso. eapply H5; firstorder.
      * econstructor 3; eauto.
    + econstructor 4; eauto. relsimpl. eauto.
    + econstructor 5.
Qed.

Lemma bisim_prefixSpec_maintain {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
: sim bot3 Sim σ σ' -> forall L, prefixSpec false σ L -> prefixSpec false σ' L.
Proof.
  intros. general induction H2.
  - eapply IHprefixSpec.
    eapply sim_reduction_closed; eauto.
    eapply star2_silent; eauto. eapply star2_refl.
    eapply star2_refl.
  - eapply sim_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    destruct evt.
    + edestruct H6 as [? [? ?]]; eauto.
      eapply prefixSpec_star2_silent; eauto.
      econstructor 2; eauto.
    + exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply sim_terminate in H4; eauto.
    destruct H4 as [? [? []]].
    econstructor 3; [ | eauto | eauto]. congruence.
  - isabsurd.
  - econstructor 5.
Qed.

Lemma bisim_prefixSpec_refine {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
: sim bot3 Sim σ σ' -> forall L, prefixSpec true σ' L -> prefixSpec true σ L.
Proof.
  intros. general induction H2.
  - eapply IHprefixSpec.
    eapply sim_reduction_closed; eauto.
    eapply star2_refl.
    eapply star2_silent; eauto. eapply star2_refl.
  - destruct evt; [|exfalso; eapply (no_activated_tau_step _ H H1); eauto].
    eapply sim_activated_2 in H4; eauto.
    destruct H4 as [? [? [[? [? ?]]|[? ?]]]].
    + edestruct H6 as [? [? ?]]; eauto.
      eapply prefixSpec_star2_silent; eauto.
      econstructor 2; eauto.
    + econstructor 4; eauto.
  - eapply sim_terminate_2 in H4; eauto.
    destruct H4 as [? [? []]]. destruct H6.
    + econstructor 3; [ | eauto | eauto]. congruence.
    + econstructor 4; eauto.
  - eapply sim_terminate_2 in H5; eauto.
    destruct H5 as [? [? []]]. destruct H7.
    + econstructor 4; eauto. congruence.
    + econstructor 4; eauto.
  - econstructor 5.
Qed.


Lemma prefixSpec_terminates S `{StateType S} (σ:S) r L
:  prefixSpec false σ (EEvtTerminate r::L)
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = r /\ L = nil.
Proof.
  intros. general induction H0.
  - edestruct IHprefixSpec. reflexivity.
    eexists x; dcr; subst. eauto using star2_silent.
  - eexists; intuition; eauto.
  - isabsurd.
Qed.

Lemma prefixSpec_nil_div S `{StateType S} σ
  : (forall L, prefixSpec true σ L -> L = nil) -> diverges σ.
Proof.
  revert σ.
  cofix f. intros.
  destruct (@step_dec _ H σ).
  - destruct H1; dcr. destruct x.
    + exfalso. exploit H0. econstructor 2; try eapply H2.
      eexists; eauto.
      econstructor 5. congruence.
    + econstructor. eauto. eapply f.
      intros. eapply H0.
      eapply prefixSpec_star2_silent.
      eapply star2_silent; eauto. econstructor. eauto.
  - exfalso.
    case_eq (result σ); intros.
    + exploit H0. econstructor 3; eauto.
      eapply star2_refl. congruence.
    + exploit H0. econstructor 4; eauto.
      eapply star2_refl. instantiate (1:=EEvtTerminate None::nil) in H3.
      congruence.
Qed.

Lemma div_prefixSpec_nil S `{StateType S} σ
  : diverges σ -> forall L, prefixSpec true σ L -> L = nil.
Proof.
  intros. general induction H1; eauto.
  - eapply IHprefixSpec.
    eapply diverges_reduction_closed; eauto.
    eapply star2_silent; eauto. eapply star2_refl.
  - exfalso.
    eapply diverges_never_activated; eauto.
  - exfalso.
    eapply diverges_never_terminates; eauto.
    eapply diverges_reduction_closed; eauto.
  - exfalso.
    eapply diverges_never_terminates; eauto.
    eapply diverges_reduction_closed; eauto.
Qed.

Lemma produces_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefixSpec true σ' L -> prefixSpec true σ L)
  -> diverges σ -> diverges σ'.
Proof.
  intros.
  pose proof (div_prefixSpec_nil H2).
  eapply prefixSpec_nil_div.
  intros. eapply H3. eauto.
Qed.

Lemma sim_complete_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S') p r
: diverges σ -> diverges σ' -> sim r p σ σ'.
Proof.
  revert σ σ'. pcofix COH; intros.
  inv H2; inv H3.
  pfold.
  econstructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - right. eapply COH; eauto.
Qed.

Lemma prefixSpec_star_activated S `{StateType S} b (σ1 σ1' σ1'':S) evt L
: star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' evt σ1''
  -> prefixSpec b σ1'' L
  -> prefixSpec b σ1 (EEvtExtern evt::L).
Proof.
  intros. general induction H0.
  - econstructor 2; eauto.
  - relsimpl.
    econstructor; eauto.
Qed.

Lemma prefixSpec_extevent S `{StateType S} (σ:S) evt L
: prefixSpec false σ (EEvtExtern evt::L)
  -> exists σ', star2 step σ nil σ'
          /\ activated σ'
          /\ exists σ'', step σ' evt σ'' /\ prefixSpec false σ'' L.
Proof.
  intros. general induction H0.
  - edestruct IHprefixSpec. reflexivity. dcr.
    eexists x; split; eauto using star2_silent.
  - eexists σ; eauto using star2.
  - isabsurd.
Qed.

Lemma prefixSpec_extevent' S `{StateType S} (σ:S) evt L
  : prefixSpec true σ (EEvtExtern evt::L)
    -> activated σ
  -> exists σ', step σ evt σ' /\ prefixSpec true σ' L.
Proof.
  intros.
  inv H1; dcr.
  inv H0; dcr.
  - exfalso. eapply step_internally_deterministic in H3; eauto; dcr.
    isabsurd.
  - do 2 eexists; eauto.
  - edestruct activated_normal_star; try eapply H1; eauto using star2.
Qed.

Lemma prefixSpec_silent_closed {S} `{StateType S}  S' `{StateType S'}
      b (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, prefixSpec b σ1 L -> prefixSpec b σ2 L)
  -> (forall L, prefixSpec b σ1' L -> prefixSpec b σ2' L).
Proof.
  intros.
  - eapply prefixSpec_star2_silent'; eauto. eapply H3.
    eapply prefixSpec_star2_silent; eauto.
Qed.

Lemma prefixSpec_event_closed {S} `{StateType S}  S' `{StateType S'}
      b (σ1 σ1':S) (σ2 σ2':S') evt
: step σ1 evt σ1'
  ->  step σ2 evt σ2'
  -> (forall L, prefixSpec b σ1 L -> prefixSpec b σ2 L)
  -> (forall L, prefixSpec b σ1' L -> prefixSpec b σ2' L).
Proof.
  intros Step1 Step2 EQ.
  destruct evt.
  - intros.
    assert (prefixSpec b σ1 (EEvtExtern (EvtExtern call)::L)). {
      econstructor 2. hnf; eauto 20. eauto. eauto.
    }
    eapply EQ in H2. inv H2.
    + exfalso; eapply no_activated_tau_step; try eapply H3.
      hnf; eauto 20.
    + exploit (@step_externally_determined _ H0 _ _ _ _ Step2 H7); eauto.
      subst. eauto.
    + assert (activated σ2) by (hnf; eauto).
      relsimpl.
  - eapply prefixSpec_silent_closed; try eapply EQ;
      eauto using star2_silent, star2.
Qed.

Lemma prefixSpec_activated {S} `{StateType S}  S' `{StateType S'}
      b (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, prefixSpec b σ1 L -> prefixSpec b σ2 L)
  -> (forall L, prefixSpec b σ1' L -> prefixSpec b σ2' L).
Proof.
  intros.
  - eapply prefixSpec_star2_silent'; eauto. eapply H3.
    eapply prefixSpec_star2_silent; eauto.
Qed.

Lemma prefix_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : (forall L, prefixSpec false σ L -> prefixSpec false σ' L)
    -> (forall L, prefixSpec true σ' L -> prefixSpec true σ L)
  -> sim bot3 Sim σ σ'.
Proof.
  revert σ σ'.
  pcofix CIH.
  intros σ σ' LIncl UIncl.
  destruct (three_possibilities σ) as [A|[A|A]].
  - dcr.
    case_eq (result x); intros.
    + assert (prefixSpec false σ (EEvtTerminate (Some v)::nil))
             by (econstructor 3; eauto).
      eapply LIncl in H4.
      eapply prefixSpec_terminates in H4. dcr.
      pfold.
      econstructor 4; eauto. congruence.
    + pfold. econstructor 3; eauto.
  - dcr. inv H3; dcr.
    assert (prefixSpec false x1 nil) by econstructor 5.
    assert (prefixSpec false σ (EEvtExtern (EvtExtern x0)::nil)). {
      eapply prefixSpec_star_activated; eauto.
    }
    eapply LIncl in H5.
    eapply prefixSpec_extevent in H5; dcr.
    pose proof (prefixSpec_silent_closed H2 H7 LIncl).
    pose proof (prefixSpec_silent_closed H7 H2 UIncl).
    pfold. econstructor 2; eauto.
    + intros.
      assert (prefixSpec false x (EEvtExtern evt::nil)). {
        eapply prefixSpec_star_activated; eauto using star2, prefixSpec.
      }
      eapply H5 in H12.
      eapply prefixSpec_extevent in H12; dcr.
      relsimpl.
      eexists; split. eauto.
      right. eapply CIH.
      eapply prefixSpec_event_closed; eauto.
      eapply prefixSpec_event_closed; eauto.
    + intros.
      assert (prefixSpec true x2 (EEvtExtern evt::nil)). {
        eapply prefixSpec_star_activated; eauto using star2, prefixSpec.
      }
      eapply H8 in H12.
      eapply prefixSpec_extevent' in H12; dcr; eauto.
      eexists; split. eauto.
      right. eapply CIH.
      eapply prefixSpec_event_closed; eauto.
      eapply prefixSpec_event_closed; eauto.
  - assert (diverges σ').
    eapply (produces_diverges UIncl); eauto.
    eapply sim_complete_diverges; eauto.
Qed.
