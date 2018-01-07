Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType StateTypeProperties.
Require Import Sim Divergence TraceEquiv CoTraces SimDivergence.

Set Implicit Arguments.
Unset Printing Records.

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

Lemma coproduces_cospecidies_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
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
    + intros. exfalso; eauto.
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

Require Import Classical_Prop.

Lemma bisim_coproduces_cospecifies {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
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

Lemma bisim_coproduces_cospecifies_iff {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim bot3 Sim σ σ'
    <-> (forall T, coproduces σ' T -> cospecifies σ T).
Proof.
  split.
  - eapply bisim_coproduces_cospecifies.
  - eapply coproduces_cospecidies_sim.
Qed.
