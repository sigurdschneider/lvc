Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType StateTypeProperties.
Require Import Sim Divergence TraceEquiv CoTraces.

Set Implicit Arguments.
Unset Printing Records.

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
      -> (~ b -> L = (EEvtTerminate None::nil))
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


Definition maximal (L:list extevent) :=
  match L with
  | EEvtTerminate None::nil => true
  | _ => false
  end.


(*
Lemma bisim_prefixSpec_maintain {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
: sim bot3 Sim σ σ' -> forall n, exists L, (❬L❭=n \/ maximal L) /\ prefixSpec false σ L /\ prefixSpec false σ' L.
Proof.
  intros. general induction H2.
  - eapply IHprefixSpec.
    eapply sim_reduction_closed; eauto.
    eapply star2_silent; eauto. eapply star2_refl.
    eapply star2_refl.
  - eapply sim_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    destruct evt.
    + edestruct H5. dcr.
      eapply prefixSpec_star2_silent; eauto.
      exploit H7; eauto; dcr.
      eapply step_internally_deterministic in H11; eauto.
      econstructor 2; eauto.
    + exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply sim_terminate in H4; eauto.
    destruct H4 as [? [? []]].
    econstructor 3; [ | eauto | eauto]. congruence.
  - isabsurd.
  - econstructor 5.
Qed.
*)

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
    destruct H4 as [? [? [[? [? ?]]|[? [? ?]]]]].
    + edestruct H6 as [? [? ?]]; eauto.
      eapply prefixSpec_star2_silent; eauto.
      econstructor 2; eauto.
    + econstructor 4; eauto. isabsurd.
  - eapply sim_terminate_2 in H4; eauto.
    destruct H4 as [? [? []]]. destruct H6.
    + econstructor 3; [ | eauto | eauto]. congruence.
    + econstructor 4; eauto. isabsurd.
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
  - exploit H3; eauto. clear_trivial_eqs.
    eauto.
Qed.

Lemma prefixSpec_terminates2 S `{StateType S} (σ:S) r L
:  prefixSpec true σ (EEvtTerminate r::L)
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ'
           /\ ((result σ' = r /\ L = nil) \/ result σ' = None).
Proof.
  intros. general induction H0.
  - edestruct IHprefixSpec. reflexivity.
    eexists x; dcr; subst. eauto using star2_silent.
  - eexists; intuition; eauto.
  - eexists; split; eauto.
Qed.

Lemma prefixSpec_nil_div S `{StateType S} σ b
  : (forall L, prefixSpec b σ L -> L = nil) -> diverges σ.
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
      eapply star2_refl.
      congruence.
Qed.

Lemma div_prefixSpec_nil S `{StateType S} σ
  : diverges σ -> forall L b, prefixSpec b σ L -> L = nil.
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
  - exploit H3; eauto; clear_trivial_eqs.
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

Lemma prefixSpec_extevent2 S `{StateType S} (σ:S) evt L
  : prefixSpec true σ (EEvtExtern evt::L)
    -> exists σ', star2 step σ nil σ'
            /\ ((activated σ' /\ exists σ'', step σ' evt σ'' /\ prefixSpec true σ'' L)
               \/ normal2 step σ' /\ result σ' = None).
Proof.
  intros.
  general induction H0.
  - edestruct IHprefixSpec as [? [? [|]]]; dcr; eauto.
    + eexists; split; eauto using star2_silent.
    + eexists; split; eauto using star2_silent.
  - eexists; split; eauto using star2_refl.
  - eexists; split; eauto using star2_refl.
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

Lemma produces_diverges2 S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
      (DIV:diverges σ)
  : (forall L, prefixSpec false σ' L -> prefixSpec false σ L)
    -> (forall L, prefixSpec true σ L -> prefixSpec true σ' L)
  -> diverges σ'.
Proof.
  revert_all. cofix CIH.
  intros. destruct DIV.
  destruct (step_dec σ').
  - destruct H4; dcr.
    destruct x.
    + exfalso.
      exploit H1.
      econstructor 2; eauto. eexists; eauto.
      econstructor 5.
      eapply prefixSpec_star2_silent' in H4;
        try eapply star2_silent; eauto using star2_refl.
      eapply div_prefixSpec_nil in DIV; eauto. congruence.
    + econstructor. eauto.
      eapply (CIH _ _ _ _ σ'0 x0 DIV).
      eapply prefixSpec_silent_closed; eauto;
        eapply star2_silent; eauto using star2_refl.
      eapply prefixSpec_silent_closed; eauto;
        eapply star2_silent; eauto using star2_refl.
  - exfalso.
    assert (prefixSpec false σ' (EEvtTerminate (result σ')::nil)). {
      case_eq (result σ'); intros.
      econstructor 3; eauto using star2_refl.
      econstructor 4; eauto using star2_refl.
    }
    eapply H1 in H5.
    eapply prefixSpec_star2_silent' in H5;
      try eapply star2_silent; eauto using star2_refl.
    eapply div_prefixSpec_nil in DIV; eauto. congruence.
Qed.


Lemma coprod_incl_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : (forall T, coproduces σ' T -> coproduces σ T)
    -> sim bot3 Sim σ σ'.
Proof.
  revert σ σ'.
  pcofix CIH.
  intros σ σ' UIncl.
  exploit (coproduces_total σ').
  destruct H1; swap 1 3; swap 2 3.
  - subst r0.
    + assert (PS:coproduces σ0 (EEvtTerminate (result σ') :+: sil)). {
        - econstructor 3; eauto using star2_refl.
      }
      eapply UIncl in PS.
      eapply coproduces_terminates in PS as [? [? [? [? ?]]]].
      * pfold.
        econstructor 4; eauto.
  - dcr. inv H2; dcr.
    assert (coproduces σ0 (EEvtExtern (EvtExtern x):+:(tr x0))). {
      econstructor 1; eauto.
      eapply coproduces_total.
    }
    exploit UIncl; eauto. inv H7.
    pfold. econstructor 2; eauto.
    + intros. congruence.
    + intros.
      assert (coproduces σ0 (EEvtExtern evt0:+:(tr σ2'))). {
        econstructor 1; eauto.
        eapply coproduces_total.
      }
      exploit UIncl; eauto.
      inv H12. relsimpl.
      eexists; split. eauto.
      right. eapply CIH.
      * intros.
        assert (coproduces σ0 (EEvtExtern evt0:+:T)). {
          econstructor 1; eauto.
        }
        eapply UIncl in H15. inv H15. relsimpl.
        eapply step_externally_determined in H20.
        rewrite H20. eauto. eauto.
  - assert (diverges σ). {
      eapply coproduces_sil_diverges; eauto.
      eapply UIncl. econstructor 2; eauto.
    }
    eapply sim_complete_diverges; eauto.
Qed.

CoInductive cospecifies {S} `{StateType S} : S -> stream extevent -> Prop :=
| CospecifiesExtern (σ σ' σ'':S) evt L :
    star2 step σ nil σ'
      -> activated σ'
      -> step σ' evt σ''
      -> cospecifies σ'' L
      -> cospecifies σ (sons (EEvtExtern evt) L)
| CospecifiesSilent (σ:S) :
    diverges σ
    -> cospecifies σ sil
| CospecifiesTerm (σ:S) (σ':S) r
  : result σ' = Some r
    -> star2 step σ nil σ'
    -> normal2 step σ'
    -> cospecifies σ (sons (EEvtTerminate (Some r)) sil)
| CospecifiesUndef (σ:S) (σ':S) T
  : result σ' = None
    -> star2 step σ nil σ'
    -> normal2 step σ'
    -> cospecifies σ T.

Lemma cospec_incl_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : (forall T, coproduces σ' T -> cospecifies σ T)
    -> sim bot3 Sim σ σ'.
Proof.
  revert σ σ'.
  pcofix CIH.
  intros σ σ' UIncl.
  exploit (coproduces_total σ').
  destruct H1; swap 1 3; swap 2 3.
  - subst r0.
    + assert (PS:coproduces σ0 (EEvtTerminate (result σ') :+: sil)). {
        - econstructor 3; eauto using star2_refl.
      }
      eapply UIncl in PS.
      inv PS.
      * pfold.
        econstructor 4; eauto. congruence.
      * pfold.
        econstructor 3; eauto.
  - dcr. inv H2; dcr.
    assert (coproduces σ0 (EEvtExtern (EvtExtern x):+:(tr x0))). {
      econstructor 1; eauto.
      eapply coproduces_total.
    }
    exploit UIncl; eauto. inv H7.
    pfold. econstructor 2; eauto.
    + intros. congruence.
    + intros.
      assert (coproduces σ0 (EEvtExtern evt0:+:(tr σ2'))). {
        econstructor 1; eauto.
        eapply coproduces_total.
      }
      exploit UIncl; eauto.
      inv H12.
      * relsimpl.
        eexists; split. eauto.
        right. eapply CIH.
        -- intros.
           assert (coproduces σ0 (EEvtExtern evt0:+:T)). {
             econstructor 1; eauto.
           }
           eapply UIncl in H15. inv H15.
           ++ relsimpl.
             eapply step_externally_determined in H20.
             rewrite H20. eauto. eauto.
           ++ relsimpl.
      * relsimpl.
    + pfold.
      econstructor 3; eauto.
  - exploit CoProducesSilent; eauto.
    eapply UIncl in H2. inv H2.
    + eapply sim_complete_diverges; eauto.
    + pfold. econstructor 3; eauto.
Qed.


Require Import paco1.

Inductive div_gen S `{StateType S} (r:S -> Prop) : S -> Prop :=
| DivergesI σ σ'
  : step σ EvtTau σ'
    -> r σ'
    -> div_gen r σ.


Definition div {S} `{StateType S} r (σ1:S)
  := paco1 (@div_gen S _ ) r σ1.

Hint Unfold div.

Lemma div_diverges {S} `{StateType S} (σ:S)
  : div bot1 σ <-> diverges σ.
Proof.
  split; intros.
  - revert σ H0. cofix CIH. intros.
    destruct H0. destruct SIM.
    econstructor; eauto.
    eapply CIH. edestruct LE; eauto. isabsurd.
  - revert σ H0. pcofix CIH; intros.
    destruct H1. pfold. econstructor; eauto.
Qed.

Lemma sim_diverge {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim bot3 Sim σ σ'
    -> div bot1 σ'
    -> ~ (exists σ'', star2 step σ nil σ'' /\ normal2 step σ'' /\ result σ'' = None)
    -> div bot1 σ.
Proof.
  revert σ σ'. pcofix CIH; intros.
  pinversion H2; subst.
  - eapply plus2_destr_nil in H1; dcr.
    pfold. econstructor; eauto.
    right. eapply CIH; eauto.
    eapply sim_expansion_closed; eauto using plus2_star2.
    intro; eapply H4; dcr; eexists; split; eauto.
    eapply (star2_step EvtTau); eauto.
  - eapply div_diverges in H3.
    exfalso.
    eapply diverges_never_activated in H7; eauto.
    eapply diverges_reduction_closed; eauto using plus2_star2.
  - exfalso. eapply H4.
    eauto.
  - eapply div_diverges in H3.
    exfalso. eapply diverges_never_terminates; eauto.
    eapply diverges_reduction_closed; eauto using plus2_star2.
Qed.


Require Import Classical_Prop.

Lemma bisim_prefixSpec_maintain {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim bot3 Sim σ σ'
    -> (forall T, coproduces σ' T -> cospecifies σ T).
Proof.
  revert σ σ'. cofix CIH; intros.
  destruct H2.
  - eapply sim_reduction_closed in H1; eauto using star2_refl.
    eapply sim_activated_2 in H1 as [? [? [?|?]]]; eauto; dcr.
    + exploit H9; eauto; dcr.
      econstructor 1; eauto.
    + econstructor 4; eauto.
  - destruct (classic (exists σ'', star2 step σ nil σ'' /\ normal2 step σ'' /\ result σ'' = None)).
    + dcr. econstructor 4; eauto.
    + econstructor 2. eapply div_diverges. eapply sim_diverge; eauto.
      eapply div_diverges. eauto.
  - eapply sim_terminate_2 in H1; eauto; dcr.
    destruct r; destruct H8; try now congruence.
    + econstructor 3; eauto. congruence.
    + econstructor 4; eauto.
    + econstructor 4; eauto. congruence.
    + econstructor 4; eauto.
Qed.
