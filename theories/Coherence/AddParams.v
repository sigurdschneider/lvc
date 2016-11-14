Require Import Util CSet IL Annotation MapDefined.
Require Import Sim.
Require Import Invariance Delocation DelocationAlgo DelocationCorrect.
Require Import Liveness LabelsDefined.

Arguments sim S {H} S' {H0} r t _ _.

Definition addParams (s:IL.stmt) (lv:ann (set var)) : IL.stmt :=
  let additional_params := fst (computeParameters nil nil nil s lv) in
  compile nil s additional_params.

Lemma addParams_correct (E:onv val) (ili:IL.stmt) lv
  : defined_on (getAnn lv) E
    -> live_sound Liveness.Imperative nil nil ili lv
    -> noUnreachableCode LabelsDefined.isCalled ili
    -> sim I.state F.state bot3 Sim
          (nil, E, ili)
          (nil:list F.block, E, addParams ili lv).
Proof with eauto.
  intros. subst. unfold addParams.
  eapply sim_trans with (S2:=I.state).
  - eapply bisim_sim.
    eapply correct; eauto.
    + eapply is_trs; eauto...
    + eapply (@live_sound_compile nil)...
      eapply is_trs...
      eapply is_live...
  - eapply bisim_sim.
    eapply bisim_sym.
    eapply (@srdSim_sim nil nil nil nil nil);
      [ | isabsurd | econstructor | reflexivity | | econstructor ].
    + eapply trs_srd; eauto.
      eapply is_trs...
    + eapply (@live_sound_compile nil nil nil)...
      eapply is_trs...
      eapply is_live...
Qed.
