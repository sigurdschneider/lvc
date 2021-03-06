Require Import Util AllInRel MapDefined IL Sim Status Annotation.
Require Import Rename RenamedApart RenamedApart_Liveness AppExpFree.
Require UCE DVE.
Require Import Reachability ReachabilityAnalysis ReachabilityAnalysisCorrect.
Require Import TrueLiveness VarP.
Require LivenessAnalysis LivenessAnalysisCorrect.

Arguments sim S {H} S' {H0} r t _ _.

Notation "'co_s' x" := (fst (fst x)) (at level 10).
Notation "'co_lv' x" := (snd (fst x)) (at level 10).
Notation "'co_ra' x" := (snd x) (at level 10, only parsing).

Hint Resolve reachability_SC_S correct.

(*
Definition DCE i (s:IL.stmt) (ra:ann (⦃var⦄ * ⦃var⦄)) : stmt * ann ⦃var⦄ * ann (⦃var⦄ * ⦃var⦄) :=
  let uc := reachabilityAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let ra_uce := UCE.compile_renamedApart s ra uc in
  let tlv := LivenessAnalysis.livenessAnalysis i s_uce in
  let s_dve := DVE.compile nil s_uce tlv in
  let ra_dve := DVE.compile_renamedApart s_uce tlv ra_uce (fst (getAnn ra_uce)) in
  (s_dve, DVE.compile_live s_uce tlv ∅, ra_dve).
*)

Definition DCE i (s:IL.stmt) : stmt * ann ⦃var⦄ :=
  let uc := reachabilityAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let tlv := LivenessAnalysis.livenessAnalysis i s_uce in
  let s_dve := DVE.compile nil s_uce tlv in
  (s_dve, DVE.compile_live s_uce tlv ∅).

Definition DCEra i (s:IL.stmt) (ra:ann (⦃var⦄ * ⦃var⦄)) : ann (⦃var⦄ * ⦃var⦄) :=
  let uc := reachabilityAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let ra_uce := UCE.compile_renamedApart s ra uc in
  let tlv := LivenessAnalysis.livenessAnalysis i s_uce in
  let ra_dve := DVE.compile_renamedApart s_uce tlv ra_uce (fst (getAnn ra_uce)) in
  ra_dve.


Lemma DCE_true_live_sound i s (PM:LabelsDefined.paramsMatch s nil)
  : true_live_sound i nil nil (UCE.compile nil s (reachabilityAnalysis s))
                    (LivenessAnalysis.livenessAnalysis i (UCE.compile nil s (reachabilityAnalysis s))).
Proof.
  eapply @LivenessAnalysisCorrect.correct; eauto.
  - eapply (@UCE.UCE_paramsMatch nil nil); eauto.
    + eapply reachabilityAnalysis_getAnn.
Qed.

Hint Resolve DCE_true_live_sound.

Lemma DCE_UCE_params_match s (PM:LabelsDefined.paramsMatch s nil)
  : paramsMatch (UCE.compile nil s (reachabilityAnalysis s)) nil.
Proof.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  eapply reachabilityAnalysis_getAnn.
Qed.

Hint Resolve DCE_UCE_params_match.

Lemma DCE_live i (ili:IL.stmt) (PM:LabelsDefined.paramsMatch ili nil)
  : Liveness.live_sound i nil nil (fst (DCE i ili)) (snd (DCE i ili)).
Proof.
  unfold DCE. simpl.
  eapply (@DVE.dve_live _ nil nil).
  eapply @LivenessAnalysisCorrect.correct; eauto.
Qed.

Lemma DCE_UCE_renamedApart s ra (PM:LabelsDefined.paramsMatch s nil) (RA:renamedApart s ra)
  :  renamedApart (UCE.compile nil s (reachabilityAnalysis s))
                  (UCE.compile_renamedApart s ra (reachabilityAnalysis s)).
Proof.
  eapply UCE.UCE_renamedApart; eauto.
Qed.

Hint Resolve DCE_UCE_renamedApart.

Lemma DCE_noUC b i ili (PM:LabelsDefined.paramsMatch ili nil)
  : LabelsDefined.noUnreachableCode (LabelsDefined.isCalled b)
                                    (fst (DCE i ili)).
Proof.
  intros. subst. simpl.
  eapply LabelsDefined.noUnreachableCode_mono.
  - eapply (@DVE.DVE_noUnreachableCode _ nil nil); eauto.
    + eapply UCE.UCE_noUnreachableCode.
      * eapply correct; eauto.
      * eapply reachabilityAnalysis_getAnn.
  - intros; eapply LabelsDefined.trueIsCalled_isCalled; eauto.
Qed.

Lemma DCE_occurVars i s (PM:LabelsDefined.paramsMatch s nil)
  : getAnn (snd (DCE i s)) ⊆ occurVars s.
Proof.
  simpl.
  rewrite DVE.compile_live_incl_empty; eauto.
  rewrite LivenessAnalysisCorrect.livenessAnalysis_getAnn.
  eapply UCE.compile_occurVars.
Qed.

Lemma DCE_correct_I (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : sim I.state I.state bot3 SimExt (nil, E, ili) (nil, E, fst (DCE Liveness.Imperative ili)).
Proof.
  intros. subst. unfold DCE.
  simpl in *.
  assert (reachability cop2bool SoundAndComplete nil ili
                                           (reachabilityAnalysis ili)). {
    eapply correct; eauto.
  }
  assert (getAnn (reachabilityAnalysis ili)). {
    eapply reachabilityAnalysis_getAnn.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ili (reachabilityAnalysis ili))
   (LivenessAnalysis.livenessAnalysis Liveness.Imperative
      (UCE.compile nil ili (reachabilityAnalysis ili)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=I.state). {
    eapply bisim_sim.
    eapply UCE.I.sim_UCE.
    eapply reachability_SC_S, correct; eauto.
    eapply reachabilityAnalysis_getAnn.
  }
  eapply DVE.I.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.

Lemma DCE_correct_F (ilf:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ilf nil)
  : defined_on (IL.occurVars ilf) E
    -> sim F.state F.state bot3 SimExt (nil, E, ilf) (nil, E, fst (DCE Liveness.Functional ilf)).
Proof.
  intros. subst. unfold DCE.
  simpl in *.
  assert (reachability cop2bool SoundAndComplete nil ilf
                                           (reachabilityAnalysis ilf)). {
    eapply correct; eauto.
  }
  assert (getAnn (reachabilityAnalysis ilf)). {
    eapply reachabilityAnalysis_getAnn.
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

Lemma DCE_renamedApart i s ra (PM:LabelsDefined.paramsMatch s nil)
  : renamedApart s ra
    -> renamedApart (fst (DCE i s)) (DCEra i s ra).
Proof.
  intros. simpl.
  exploit (@LivenessAnalysisCorrect.correct i); eauto.
  eapply (@DVE.DVE_renamedApart i nil nil); eauto.
  - rewrite <- renamedApart_freeVars.
    Focus 2.
    eapply UCE.UCE_renamedApart; eauto.
    + rewrite DVE.DVE_freeVars; eauto.
      destruct i; eauto using TrueLiveness.true_live_sound_overapproximation_F.
      * eapply TrueLiveness.true_live_sound_overapproximation_F.
        eapply renamedApart_true_live_imperative_is_functional; eauto.
        -- eapply UCE.UCE_noUnreachableCode; eauto.
           ++ eapply reachabilityAnalysis_getAnn.
        -- eapply LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl.
           ++ eapply UCE.UCE_renamedApart; eauto.
           ++ eapply (@paramsMatch_labelsDefined _ nil); eauto.
        -- isabsurd.
Qed.


Lemma DCE_true_live_sound_F i s ra (PM:LabelsDefined.paramsMatch s nil) (RA:renamedApart s ra)
  : true_live_sound Functional nil nil (UCE.compile nil s (reachabilityAnalysis s))
                    (LivenessAnalysis.livenessAnalysis i (UCE.compile nil s (reachabilityAnalysis s))).
Proof.
  destruct i; eauto using TrueLiveness.true_live_sound_overapproximation_F.
  * eapply TrueLiveness.true_live_sound_overapproximation_F.
    eapply renamedApart_true_live_imperative_is_functional; eauto.
  - eapply UCE.UCE_noUnreachableCode; eauto.
     + eapply reachabilityAnalysis_getAnn.
  - eapply LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl.
     + eapply UCE.UCE_renamedApart; eauto.
     + eapply (@paramsMatch_labelsDefined _ nil); eauto.
  - isabsurd.
Qed.

Lemma DCE_live_incl i s ra (RA:renamedApart s ra) (PM:LabelsDefined.paramsMatch s nil)
  : ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y)
          (snd (DCE i s)) (DCEra i s ra).
Proof.
  unfold DCE; simpl.
  eapply DVE.DVE_live_incl.
  - instantiate (1:=Functional). eauto.
  - eapply UCE.UCE_renamedApart; eauto.
  - eapply DCE_true_live_sound_F; eauto.
  - eapply LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl; eauto.
  - exploit (@LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl
               i (UCE.compile nil s (reachabilityAnalysis s))); eauto.
    eapply ann_R_get in H. eauto.
  - reflexivity.
  - eauto with cset.
Qed.

Lemma DCE_paramsMatch i s (PM:LabelsDefined.paramsMatch s nil)
  : LabelsDefined.paramsMatch (fst (DCE i s)) nil.
Proof.
  unfold DCE; simpl.
  exploit (@DVE.DVE_paramsMatch i nil nil); eauto.
Qed.

Lemma DCE_app_expfree i s
      (AEF:app_expfree s)
  : app_expfree (fst (DCE i s)).
Proof.
  simpl.
  eapply DVE.DVE_app_expfree.
  eapply UCE.UCE_app_expfree; eauto.
Qed.

Lemma DCE_ra_fst s ra
      (PM:LabelsDefined.paramsMatch s nil) (RA:renamedApart s ra)
  : fst (getAnn (DCEra Liveness.Imperative s ra))
        [=] fst (getAnn ra).
Proof.
  unfold DCEra.
  rewrite DVE.fst_getAnn_renamedApart'; eauto.
  exploit UCE.compile_renamedApart_pes; eauto.
  + rewrite H. reflexivity.
Qed.

Lemma DCE_ra_snd s ra
      (PM:LabelsDefined.paramsMatch s nil) (RA:renamedApart s ra)
  : snd (getAnn (DCEra Liveness.Imperative s ra))
        ⊆ snd (getAnn ra).
Proof.
  unfold DCEra.
  rewrite DVE.snd_getAnn_renamedApart; eauto.
  exploit UCE.compile_renamedApart_pes; eauto.
  + rewrite H. reflexivity.
Qed.

Lemma DCE_var_P i (P:var -> Prop) (s:stmt) (PM:LabelsDefined.paramsMatch s nil)
  (VP:var_P P s)
  : var_P P (fst (DCE i s)).
Proof.
  simpl.
  eapply (@DVE.DVE_var_P i _ nil nil); eauto.
  eapply (@UCE.UCE_var_P _ nil); eauto.
Qed.

Lemma DCE_snd_lv_fst_ra (s:stmt) ra
      (PM:LabelsDefined.paramsMatch s nil) (RA:renamedApart s ra)
  : getAnn (snd (DCE Liveness.Imperative s)) ⊆ fst (getAnn ra).
Proof.
  unfold DCE.
  simpl.
  rewrite DVE.compile_live_incl_empty; eauto.
  exploit (@LivenessAnalysisCorrect.livenessAnalysis_renamedApart_incl
           Imperative (UCE.compile nil s (reachabilityAnalysis s))); eauto using UCE.UCE_renamedApart.
  eapply ann_R_get in H.
  erewrite H.
  exploit UCE.compile_renamedApart_pes; eauto.
  invc H0. simpl. rewrite H3; eauto.
Qed.
