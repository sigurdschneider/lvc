Require Import List CSet CMap.
Require Import Util AllInRel MapDefined IL Sim Status Annotation LabelsDefined.
Require Import Rename RenameApart RenamedApart RenameApart_Liveness.
Require Import Liveness ParallelMove.
Require Import Coherence Invariance.
Require Import Allocation AllocationAlgo AllocationAlgoCorrect.
Require Import Alpha.
Require Import Slot InfinitePartition.
(* Require CopyPropagation ConstantPropagation ConstantPropagationAnalysis.*)

Arguments sim S {H} S' {H0} r t _ _.

Definition rassign
           (s:stmt) (lv: ann (set var)) :=
  let fvl := to_list (getAnn lv) in
  let ϱ := CMap.update_map_with_list fvl fvl (@MapInterface.empty var _ _ _) in
  sdo ϱ' <- regAssign even_part s lv ϱ;
    let s_allocated := rename (CMap.findt ϱ' 0) s in
    let s_lowered := ParallelMove.lower nil
                                       s_allocated
                                       (mapAnn (lookup_set (CMap.findt ϱ' 0)) lv) in
    s_lowered.

Opaque to_list.


Lemma rassign_correct (s:stmt) (lv:ann (set var)) s' ra
      (SC: rassign s lv = Success s') (PM:paramsMatch s nil)
      (RA: renamedApart s ra)
      (LV:live_sound FunctionalAndImperative nil nil s lv)
      (Incl:getAnn lv ⊆ fst (getAnn ra))
  : forall E, sim F.state I.state bot3 Sim (nil, E, s) (nil, E, s').
Proof.
  intros. unfold rassign in SC.
  monadS_inv SC.
  exploit regAssign_correct; eauto.
  eapply injective_on_agree; [| eapply CMap.map_update_list_update_agree; reflexivity].
  hnf; intros ? ? ? ? EqMap.
  rewrite lookup_update_same in EqMap.
  rewrite EqMap; eauto. rewrite lookup_update_same; eauto with cset.
  rewrite of_list_3; eauto.
  rewrite of_list_3; eauto.
  exploit (@live_inj_rename_sound Liveness.FunctionalAndImperative nil nil) as LV_ren;
    eauto using Liveness.live_sound_overapproximation_I.
  simpl in *.
  eapply sim_trans
  with (σ2:=(nil, E, rename (CMap.findt x 0) s):F.state).
  {
    eapply bisim_sim.
    - eapply alphaSim_sim.
      eapply alphaSimI with (ra:=id) (ira:=id); eauto using PIR2, envCorr_idOn_refl.
      exploit regAssign_renamedApart_agree as AGR; eauto.
      rewrite <- map_update_list_update_agree in AGR; eauto with len.
      assert (AGR2:agree_on _eq (freeVars s) id (findt x 0)). {
        exploit renamedApart_freeVars as Incl2; eauto.
        pose proof (freeVars_live (live_sound_overapproximation_F LV)) as Incl3.
        etransitivity; eauto using agree_on_incl.
        hnf; intros.
        edestruct update_with_list_lookup_in_list; eauto.
        Focus 2. dcr. rewrite H4. hnf in H6. subst. get_functional.
        reflexivity. rewrite of_list_3. eauto.
      }
      exploit renamedApart_freeVars as Incl2; eauto.
      pose proof (freeVars_live (live_sound_overapproximation_F LV)) as Incl3.
      assert (AGR3:agree_on _eq (getAnn lv) id
                            (findt (empty nat) 0 [to_list (getAnn lv) <--
                                                        to_list (getAnn lv)])). {
        hnf; intros ? IN.
        edestruct update_with_list_lookup_in_list; eauto.
        Focus 2. dcr. setoid_rewrite H3. hnf in H5. subst.
        get_functional. eauto.
        rewrite of_list_3. eauto.
      }
      eapply alpha_agree_on_morph.
      + eapply renamedApart_locally_inj_alpha;
          eauto using live_sound_overapproximation_F.
        instantiate (1:=(findt (empty nat) 0
                               [to_list (getAnn lv) <-- to_list (getAnn lv)])).
        hnf; intros ? IN.
        rewrite <- AGR; eauto.
        edestruct update_with_list_lookup_in_list; eauto.
        Focus 2. dcr. setoid_rewrite H3 at 2. hnf in H5. subst.
        get_functional. eauto.
        rewrite of_list_3. eauto.
      + eapply agree_on_incl; eauto.
        revert Incl3 AGR2; clear. unfold lookup_set. intros; cset_tac'.
        rewrite <- AGR2; eauto.
      + eauto.
  }
  eapply sim_trans
  with (σ2:=(nil, E, rename (CMap.findt x 0) s):I.state).
  {
    eapply bisim_sim.
    eapply Invariance.srdSim_sim.
    - eapply Allocation.rename_renamedApart_srd; simpl;
        eauto using Liveness.live_sound_overapproximation_I.
      simpl; eauto.
    - simpl. isabsurd.
    - econstructor.
    - reflexivity.
    - eauto using Liveness.live_sound_overapproximation_I.
    - econstructor.
  }
  exploit (@ParallelMove.correct nil);
    try eapply EQ0; try now econstructor; eauto using Liveness.live_sound_overapproximation_I.
  eauto using Liveness.live_sound_overapproximation_I.
  eauto.
Qed.
