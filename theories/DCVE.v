Require Import Util AllInRel MapDefined IL Rename RenameApart Sim Status Annotation.
Require UCE DVE.
Require ReachabilityAnalysis ReachabilityAnalysisCorrect.
Require TrueLiveness LivenessAnalysis LivenessAnalysisCorrect.

Arguments sim S {H} S' {H0} r t _ _.

Definition DCVE i (s:IL.stmt) : stmt * ann (set var) :=
  let uc := ReachabilityAnalysis.reachabilityAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let tlv := LivenessAnalysis.livenessAnalysis i s_uce in
  let s_dve := DVE.compile nil s_uce tlv in
  (s_dve, DVE.compile_live s_uce tlv ∅).

Lemma DCVE_live i (ili:IL.stmt) (PM:LabelsDefined.paramsMatch ili nil)
  : Liveness.live_sound i nil nil (fst (DCVE i ili)) (snd (DCVE i ili)).
Proof.
  unfold DCVE. simpl.
  eapply (@DVE.dve_live _ nil nil).
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  eapply Reachability.reachability_SC_S, ReachabilityAnalysisCorrect.correct; eauto.
  eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
Qed.

Lemma DCVE_noUC i ili (PM:LabelsDefined.paramsMatch ili nil)
  : LabelsDefined.noUnreachableCode LabelsDefined.isCalled (fst (DCVE i ili)).
Proof.
  intros. subst. simpl.
  eapply LabelsDefined.noUnreachableCode_mono.
  - eapply (@DVE.DVE_noUnreachableCode _ nil nil).
    + eapply @LivenessAnalysisCorrect.correct; eauto.
      eapply (@UCE.UCE_paramsMatch nil nil); eauto.
      * eapply Reachability.reachability_SC_S, ReachabilityAnalysisCorrect.correct; eauto.
      * eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
    + eapply UCE.UCE_noUnreachableCode.
      * eapply ReachabilityAnalysisCorrect.correct; eauto.
      * eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
  - eapply LabelsDefined.trueIsCalled_isCalled.
Qed.

Lemma DCVE_occurVars i s (PM:LabelsDefined.paramsMatch s nil)
  : getAnn (snd (DCVE i s)) ⊆ occurVars s.
Proof.
  simpl.
  rewrite DVE.compile_live_incl_empty; eauto.
  rewrite LivenessAnalysisCorrect.livenessAnalysis_getAnn.
  eapply UCE.compile_occurVars.
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  * eapply Reachability.reachability_SC_S, ReachabilityAnalysisCorrect.correct; eauto.
  * eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
Qed.

Lemma DCVE_correct_I (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state I.state bot3 Sim (nil, E, ili) (nil, E, fst (DCVE Liveness.Imperative ili)).
Proof.
  intros. subst. unfold DCVE.
  simpl in *.
  assert (Reachability.reachability Reachability.SoundAndComplete nil ili
                                           (ReachabilityAnalysis.reachabilityAnalysis ili)). {
    eapply ReachabilityAnalysisCorrect.correct; eauto.
  }
  assert (getAnn (ReachabilityAnalysis.reachabilityAnalysis ili)). {
    eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
  }
  assert (LabelsDefined.paramsMatch
            (UCE.compile nil ili (ReachabilityAnalysis.reachabilityAnalysis ili)) nil). {
    eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ili (ReachabilityAnalysis.reachabilityAnalysis ili))
   (LivenessAnalysis.livenessAnalysis Liveness.Imperative
      (UCE.compile nil ili (ReachabilityAnalysis.reachabilityAnalysis ili)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=I.state).
  eapply bisim_sim.
  eapply UCE.I.sim_UCE.
  eapply Reachability.reachability_SC_S, ReachabilityAnalysisCorrect.correct; eauto.
  eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
  eapply DVE.I.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.


Lemma DCVE_correct_F (ilf:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ilf nil)
  : defined_on (IL.occurVars ilf) E
    -> sim F.state F.state bot3 Sim (nil, E, ilf) (nil, E, fst (DCVE Liveness.Functional ilf)).
Proof.
  intros. subst. unfold DCVE.
  simpl in *.
  assert (Reachability.reachability Reachability.SoundAndComplete nil ilf
                                           (ReachabilityAnalysis.reachabilityAnalysis ilf)). {
    eapply ReachabilityAnalysisCorrect.correct; eauto.
  }
  assert (getAnn (ReachabilityAnalysis.reachabilityAnalysis ilf)). {
    eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
  }
  assert (LabelsDefined.paramsMatch
            (UCE.compile nil ilf (ReachabilityAnalysis.reachabilityAnalysis ilf)) nil). {
    eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ilf (ReachabilityAnalysis.reachabilityAnalysis ilf))
   (LivenessAnalysis.livenessAnalysis Liveness.Imperative
      (UCE.compile nil ilf (ReachabilityAnalysis.reachabilityAnalysis ilf)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=F.state).
  eapply bisim_sim.
  eapply UCE.F.sim_UCE.
  eapply Reachability.reachability_SC_S, ReachabilityAnalysisCorrect.correct; eauto.
  eapply ReachabilityAnalysisCorrect.reachabilityAnalysis_getAnn.
  eapply DVE.F.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.
