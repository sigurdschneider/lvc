Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType Sim Divergence.

Set Implicit Arguments.
Unset Printing Records.

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
