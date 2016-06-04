Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export SmallStepRelations StateType Bisim Sim.

Set Implicit Arguments.
Unset Printing Records.

Lemma bisim_sim t {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2)
  : Bisim.bisim σ1 σ2 -> Sim.sim t σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1.
  - econstructor; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr. eexists; eauto.
    + intros. edestruct H7; eauto; dcr. eexists; eauto.
  - econstructor 4; eauto.
Qed.

Lemma sim_bisim {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2)
  : Sim.sim Bisim σ1 σ2 -> Bisim.bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1.
  - econstructor; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr. eexists; eauto.
    + intros. edestruct H7; eauto; dcr. eexists; eauto.
  - econstructor 3; eauto.
Qed.
