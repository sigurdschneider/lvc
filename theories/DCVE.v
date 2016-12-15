Require Import Util AllInRel MapDefined IL Sim Status Annotation.
Require Import Rename RenamedApart RenamedApart_Liveness.
Require UCE DVE.
Require Import Reachability ReachabilityAnalysis ReachabilityAnalysisCorrect.
Require Import TrueLiveness.
Require LivenessAnalysis LivenessAnalysisCorrect.

Arguments sim S {H} S' {H0} r t _ _.

Notation "'co_s' x" := (fst (fst x)) (at level 50).
Notation "'co_lv' x" := (snd (fst x)) (at level 50).
Notation "'co_ra' x" := (snd x) (at level 50).

Definition DCVE i (s:IL.stmt) (ra:ann (⦃var⦄ * ⦃var⦄)) : stmt * ann ⦃var⦄ * ann (⦃var⦄ * ⦃var⦄) :=
  let uc := reachabilityAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let ra_uce := UCE.compile_renamedApart s ra uc in
  let tlv := LivenessAnalysis.livenessAnalysis i s_uce in
  let s_dve := DVE.compile nil s_uce tlv in
  let ra_dve := DVE.compile_renamedApart s_uce tlv ra_uce (fst (getAnn ra_uce)) in
  (s_dve, DVE.compile_live s_uce tlv ∅, ra_dve).

Lemma DCVE_live i (ili:IL.stmt) (PM:LabelsDefined.paramsMatch ili nil) ra
  : Liveness.live_sound i nil nil (co_s (DCVE i ili ra)) (co_lv (DCVE i ili ra)).
Proof.
  unfold DCVE. simpl.
  eapply (@DVE.dve_live _ nil nil).
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  eapply reachability_SC_S, correct; eauto.
  eapply reachabilityAnalysis_getAnn.
Qed.

Lemma DCVE_noUC i ili (PM:LabelsDefined.paramsMatch ili nil) ra
  : LabelsDefined.noUnreachableCode LabelsDefined.isCalled (co_s (DCVE i ili ra)).
Proof.
  intros. subst. simpl.
  eapply LabelsDefined.noUnreachableCode_mono.
  - eapply (@DVE.DVE_noUnreachableCode _ nil nil).
    + eapply @LivenessAnalysisCorrect.correct; eauto.
      eapply (@UCE.UCE_paramsMatch nil nil); eauto.
      * eapply reachability_SC_S, correct; eauto.
      * eapply reachabilityAnalysis_getAnn.
    + eapply UCE.UCE_noUnreachableCode.
      * eapply correct; eauto.
      * eapply reachabilityAnalysis_getAnn.
  - eapply LabelsDefined.trueIsCalled_isCalled.
Qed.

Lemma DCVE_occurVars i s (PM:LabelsDefined.paramsMatch s nil) ra
  : getAnn (co_lv (DCVE i s ra)) ⊆ occurVars s.
Proof.
  simpl.
  rewrite DVE.compile_live_incl_empty; eauto.
  rewrite LivenessAnalysisCorrect.livenessAnalysis_getAnn.
  eapply UCE.compile_occurVars.
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  * eapply reachability_SC_S, correct; eauto.
  * eapply reachabilityAnalysis_getAnn.
Qed.

Lemma DCVE_correct_I (ili:IL.stmt) (E:onv val) ra
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state I.state bot3 Sim (nil, E, ili) (nil, E, co_s (DCVE Liveness.Imperative ili ra)).
Proof.
  intros. subst. unfold DCVE.
  simpl in *.
  assert (reachability SoundAndComplete nil ili
                                           (reachabilityAnalysis ili)). {
    eapply correct; eauto.
  }
  assert (getAnn (reachabilityAnalysis ili)). {
    eapply reachabilityAnalysis_getAnn.
  }
  assert (LabelsDefined.paramsMatch
            (UCE.compile nil ili (reachabilityAnalysis ili)) nil). {
    eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ili (reachabilityAnalysis ili))
   (LivenessAnalysis.livenessAnalysis Liveness.Imperative
      (UCE.compile nil ili (reachabilityAnalysis ili)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=I.state).
  eapply bisim_sim.
  eapply UCE.I.sim_UCE.
  eapply reachability_SC_S, correct; eauto.
  eapply reachabilityAnalysis_getAnn.
  eapply DVE.I.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.


Lemma DCVE_correct_F (ilf:IL.stmt) (E:onv val) ra
  (PM:LabelsDefined.paramsMatch ilf nil)
  : defined_on (IL.occurVars ilf) E
    -> sim F.state F.state bot3 Sim (nil, E, ilf) (nil, E, co_s (DCVE Liveness.Functional ilf ra)).
Proof.
  intros. subst. unfold DCVE.
  simpl in *.
  assert (reachability SoundAndComplete nil ilf
                                           (reachabilityAnalysis ilf)). {
    eapply correct; eauto.
  }
  assert (getAnn (reachabilityAnalysis ilf)). {
    eapply reachabilityAnalysis_getAnn.
  }
  assert (LabelsDefined.paramsMatch
            (UCE.compile nil ilf (reachabilityAnalysis ilf)) nil). {
    eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ilf (reachabilityAnalysis ilf))
   (LivenessAnalysis.livenessAnalysis Liveness.Imperative
      (UCE.compile nil ilf (reachabilityAnalysis ilf)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=F.state).
  eapply bisim_sim.
  eapply UCE.F.sim_UCE.
  eapply reachability_SC_S, correct; eauto.
  eapply reachabilityAnalysis_getAnn.
  eapply DVE.F.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.

Definition compile_renamedApart i s ra :=
  let ra' := (UCE.compile_renamedApart s ra (reachabilityAnalysis s)) in
  DVE.compile_renamedApart (UCE.compile nil s (reachabilityAnalysis s))
                           (LivenessAnalysis.livenessAnalysis i
                                                              (UCE.compile nil s (reachabilityAnalysis s)))
                           ra'
                           (fst (getAnn ra')).

Lemma DCVE_renamedApart i s ra (PM:LabelsDefined.paramsMatch s nil)
  : renamedApart s ra
    -> renamedApart (co_s (DCVE i s ra)) (co_ra (DCVE i s ra)).
Proof.
  intros. simpl.
  assert (true_live_sound i nil nil (UCE.compile nil s (reachabilityAnalysis s))
          (LivenessAnalysis.livenessAnalysis i (UCE.compile nil s (reachabilityAnalysis s)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
    - eapply (@UCE.UCE_paramsMatch nil nil); eauto.
      + eapply reachability_SC_S, correct; eauto.
      + eapply reachabilityAnalysis_getAnn.
  }
  exploit (@LivenessAnalysisCorrect.correct i); eauto.
  eapply (@DVE.DVE_renamedApart i nil nil); eauto.
  - eapply UCE.UCE_renamedApart; eauto.
    + eapply reachability_SC_S, correct; eauto.
  - rewrite <- renamedApart_freeVars.
    Focus 2.
    eapply UCE.UCE_renamedApart; eauto.
    eapply reachability_SC_S, correct; eauto.
    + rewrite DVE.DVE_freeVars; eauto.
      destruct i; eauto using TrueLiveness.true_live_sound_overapproximation_F.
      * eapply TrueLiveness.true_live_sound_overapproximation_F.
        eapply renamedApart_true_live_imperative_is_functional; eauto.
        -- eapply UCE.UCE_renamedApart; eauto.
           ++ eapply reachability_SC_S, correct; eauto.
        -- eapply UCE.UCE_noUnreachableCode; eauto.
           ++ eapply correct; eauto.
           ++ eapply reachabilityAnalysis_getAnn.
        -- eapply LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl.
           ++ eapply UCE.UCE_renamedApart; eauto.
             ** eapply reachability_SC_S, correct; eauto.
           ++ eapply (@paramsMatch_labelsDefined _ nil).
             eapply (@UCE.UCE_paramsMatch nil nil); eauto.
             ** eapply reachability_SC_S, correct; eauto.
             ** eapply reachabilityAnalysis_getAnn.
        -- isabsurd.
Qed.