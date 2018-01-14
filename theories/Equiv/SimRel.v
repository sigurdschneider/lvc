Require NonParametricBiSim.
Require Import Sim SimLockStep IL paco3 OptionR.
Require Export ILStateType BlockType ILProperties.

Lemma bisim_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : sim bot3 Bisim σ σ'
    -> sim bot3 SimExt σ σ'.
Proof.
  revert σ σ'.
  pcofix CIH.
  intros. pinversion H2; subst; pfold.
  - econstructor; try eassumption.
    right. eapply CIH. eauto.
  - econstructor 2; try eassumption.
    + intros. edestruct H6; eauto; dcr; pclearbot.
      eexists; split; eauto.
    + intros. edestruct H7; eauto; dcr; pclearbot.
      eexists; split; eauto.
  - econstructor 3; try eassumption. eauto.
  - econstructor 4; try eassumption.
Qed.

Lemma sim_ext_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : sim bot3 SimExt σ σ'
    -> sim bot3 Sim σ σ'.
Proof.
  revert σ σ'.
  pcofix CIH.
  intros. pinversion H2; subst; pfold.
  - econstructor; try eassumption.
    right. eapply CIH. eauto.
  - econstructor 2; try eassumption.
    + intros. edestruct H6; eauto; dcr; pclearbot.
      eexists; split; eauto.
    + intros. edestruct H7; eauto; dcr; pclearbot.
      eexists; split; eauto.
  - econstructor 3; try eassumption.
  - econstructor 4; try eassumption.
Qed.
