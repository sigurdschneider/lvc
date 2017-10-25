Require Import Util CSet IL Annotation MapDefined AllInRel.
Require Import Sim LabelsDefined Liveness.Liveness AppExpFree.
Require Import Coherence Coherence_Liveness.
Require Import Invariance Delocation DelocationCorrect.
Require Import DelocationAlgo DelocationAlgoCorrect DelocationAlgoLive.
Require Import LabelsDefined.

Arguments sim S {H} S' {H0} r t _ _.

Definition addParams (s:IL.stmt) (lv:ann (set var)) : IL.stmt :=
  let additional_params := fst (computeParameters nil nil s lv) in
  compile nil s additional_params.

Lemma addParams_correct b (E:onv val) (ili:IL.stmt) lv
  : defined_on (getAnn lv) E
    -> live_sound Imperative nil nil ili lv
    -> noUnreachableCode (isCalled b) ili
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
      eapply is_live...
  - eapply bisim_sim.
    eapply bisim_sym.
    eapply SimCompanion.simc_sim.
    eapply (@srdSim_sim nil nil nil);
      [ | isabsurd | econstructor | isabsurd | | econstructor | reflexivity ].
    + eapply trs_srd; eauto.
      eapply is_trs...
    + eapply (@live_sound_compile nil nil nil)...
      eapply is_live...
Qed.

Lemma addParams_live b ili lv
  (LS:live_sound Imperative nil nil ili lv)
  (NUC:noUnreachableCode (isCalled b) ili)
  : live_sound FunctionalAndImperative nil nil
               (addParams ili lv) lv.
Proof.
  unfold addParams.
  eapply srd_live_functional; eauto using PIR2; eauto.
  - eapply (@live_sound_compile nil nil nil);
      eauto using is_trs, is_live.
  - eauto using trs_srd, is_trs.
  - exploit compile_noUnreachableCode; eauto using is_trs.
Qed.

Lemma addParams_srd b s lv
      (LV:Liveness.live_sound Liveness.Imperative nil nil s lv)
      (NUC:noUnreachableCode (isCalled b) s)
  : srd nil (addParams s lv) lv.
Proof.
  unfold addParams; simpl.
  eapply trs_srd.
  exploit (@computeParameters_trs b nil nil nil); eauto.
  exploit computeParameters_length; eauto.
  simpl in *.
  destruct (snd (computeParameters nil nil s lv)); isabsurd.
  eauto.
Qed.

Lemma addParams_paramsMatch b s lv
      (PM:paramsMatch s nil)
      (LS:live_sound Imperative nil nil s lv)
      (NUC:noUnreachableCode (isCalled b) s)
  : paramsMatch (addParams s lv) nil.
Proof.
  unfold addParams.
  eapply (@compile_paramsMatch nil nil); eauto using is_trs.
Qed.

Lemma addParams_noUnreachableCode b s lv
      (PM:paramsMatch s nil)
      (LS:live_sound Imperative nil nil s lv)
      (NUC:noUnreachableCode (isCalled b) s)
  : noUnreachableCode (isCalled b) (addParams s lv).
Proof.
  unfold addParams.
  eapply compile_noUnreachableCode; eauto using is_trs.
Qed.


Lemma addParams_app_expfree s lv
      (AEF:app_expfree s)
  : app_expfree (addParams s lv).
Proof.
  unfold addParams.
  eapply compile_app_expfree; eauto.
Qed.
