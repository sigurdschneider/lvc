Require Import List CSet.
Require Import Util AllInRel MapDefined IL Sim Status Annotation VarP.
Require Import Rename RenameApart RenamedApartAnn RenameApart_Liveness RenameApart_VarP.
Require CMap.
Require Liveness.Liveness LivenessValidators ParallelMove ILN ILN_IL.
Require TrueLiveness LivenessAnalysis LivenessAnalysisCorrect.
Require Import Coherence Coherence_RenamedApart Invariance.
Require Delocation DelocationAlgo DelocationCorrect DelocationValidator.
Require Coherence.Allocation AllocationAlgo AllocationAlgoCorrect.
Require UCE DVE EAE Alpha.
Require ReachabilityAnalysis ReachabilityAnalysisCorrect.
Require Import DCE Slot InfiniteSubset InfinitePartition RegAssign ExpVarsBounded.
Require CopyPropagation ConstantPropagation ConstantPropagationAnalysis.
Require ConstantPropagationCorrect ConstantPropagationAnalysisCorrect.

Require Import RegAssign.
Require Import MoreTac Alpha RenameApart_Alpha RenameApart_Liveness
        RenamedApart_Liveness Coherence Invariance.

Require Import RenameApartToPart FreshGenInst FreshGen.

Require String.

Set Implicit Arguments.

Hint Immediate FGS_even_fast_pos FGS_fast_pres.

Section Compiler.

Definition ensure_f P `{Computable P} (s: String.string) {A} (cont:status A) : status A :=
if [P] then cont else Error s.

Arguments ensure_f P [H] s {A} cont.

Notation "'ensure' P s ; cont " := (ensure_f P s cont)
                                    (at level 20, P at level 0, s at level 0,
                                     cont at level 200, left associativity).

(* Print Grammar operconstr. *)

Definition toDeBruijn (ilin:ILN.nstmt) : status IL.stmt :=
  ILN_IL.labIndices nil ilin.

Lemma toDeBruijn_correct (ilin:ILN.nstmt) s (E:onv val)
 : toDeBruijn ilin = Success s
   ->  @sim _ ILN.statetype_I _ _ bot3 Bisim
           (ILN.I.labenv_empty, E, ilin)
           (nil:list I.block, E, s).
Proof.
  intros. unfold toDeBruijn in H. simpl in *.
  eapply ILN_IL.labIndicesSim_sim.
  econstructor; eauto; isabsurd. econstructor; isabsurd. constructor.
Qed.

Arguments sim S {H} S' {H0} r t _ _.

Require Import AddParams Spilling.


Definition toILF (s:IL.stmt) : IL.stmt :=
  let (s_dcve, lv) := DCE Liveness.Imperative s in
  addParams s_dcve lv.

Lemma toILF_correct (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state F.state bot3 SimExt (nil, E, ili) (nil:list F.block, E, toILF ili).
Proof with eauto using DCE_live, DCE_noUC.
  intros. subst. unfold toILF.
  eapply sim_trans with (S2:=I.state).
  eapply DCE_correct_I; eauto.
  let_pair_case_eq; simpl_pair_eqs; subst.
  unfold fst at 1.
  eapply (@addParams_correct true)...
  eauto using defined_on_incl, DCE_occurVars.
Qed.


Definition optimize (s_in:stmt) : stmt.
  refine
    (let s_ra := rename_apart FG_even_fast_pos s_in in
     let s_cpy := CopyPropagation.copyPropagate (fun x => x) s_ra in
     let an := @ConstantPropagationAnalysis.constantPropagationAnalysis
                s_cpy
                (renamedApartAnn s_ra (freeVars s_in))
                (CopyPropagation.copyPropagation_renamedApart
                   (fun x => x) (rename_apart_renamedApart FGS_even_fast_pos s_in) _)
     in
     let s_cp := ConstantPropagation.constantPropagate (DomainSSA.domenv (proj1_sig (fst an))) s_cpy in
     s_cp).
  eapply lookup_set_on_id. reflexivity.
Defined.

Lemma renamedApartAnn_annotation s G
  : annotation s (renamedApartAnn s G).
Proof.
  revert G.
  induction s using stmt_ind';
    simpl; intros; repeat let_pair_case_eq; subst;
      eauto using @annotation.
  - econstructor; intros; inv_get; try len_simpl; inv_get; eauto with len.
Qed.

Import FiniteFixpointIteration Infra.PartialOrder.

Lemma optimize_correct E s (PM:LabelsDefined.paramsMatch s nil)
  : @sim _ IL.statetype_F _ _ bot3 SimExt
           (nil, E, s)
           (nil:list F.block, E, optimize s).
Proof.
  cbv beta delta [optimize].
  repeat match goal with
         | [ |- context f [ let s := ?e in @?t s ] ] =>
           let s := fresh s in
           set (s:=e) in *;
             let s := eval cbv beta in (t s) in
                 let x := context f[s] in
                 change x
         end.
  eapply sim_trans with (σ2:=(nil, E, s_ra):F.state). {
    eapply bisim_sim. eapply bisim_sym.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    - eapply rename_apart_alpha'; eauto.
      rewrite lookup_set_on_id; [|reflexivity].
      rewrite <- domain_add_spec; eauto.
      eapply inverse_on_id.
    - eapply envCorr_idOn_refl.
  }
  set (RA:= (rename_apart_renamedApart FGS_even_fast_pos s)) in *.
    set (ra:=(renamedApartAnn (rename_apart FG_even_fast_pos s) (freeVars s))) in *.
  set (RA':=(CopyPropagation.copyPropagation_renamedApart (fun x : positive => x) RA
             (lookup_set_on_id (reflexivity (fst (getAnn ra)))))) in *.
  assert (LD:LabelsDefined.labelsDefined s_ra 0). {
    eapply LabelsDefined.paramsMatch_labelsDefined with (L:=nil).
    eapply labelsDefined_paramsMatch; eauto.
  }
  eapply sim_trans with (σ2:=(nil, E, s_cpy):F.state). {
    subst s_cpy.
    eapply (@ValueOpts.sim_vopt bot3 nil nil)
      with (ZL:=nil) (Δ := nil); eauto using SimF.labenv_sim_nil; only 4:isabsurd;
      swap 1 2.
    - eapply CopyPropagation.copyPropagate_sound_eqn; eauto.
      + eapply lookup_set_on_id; reflexivity.
      + isabsurd.
    - hnf; intros. cset_tac'. invc H0.
      simpl. reflexivity.
    - rewrite CopyPropagation.cp_eqns_freeVars; eauto.
      eapply lookup_set_on_id; reflexivity.
  }
  eapply (@ValueOpts.sim_vopt bot3 nil nil)
    with (ZL:=nil) (Δ := nil); eauto using SimF.labenv_sim_nil; only 4:isabsurd;
                                                  swap 1 2.
  - eapply ConstantPropagationCorrect.cp_sound_eqn
      with (Cp:=nil) (Rch:=nil) (ZL:=nil) (ΓL:=nil) (r:=proj1_sig (snd an));
      eauto; only 3:isabsurd.
    + eapply ConstantPropagationAnalysisCorrect.cp_sound_nil; eauto.
      * eapply (@safeFixpoint_fixpoint
                  _
                  (ConstantPropagationAnalysis.constant_propagation_analysis RA')).
      * eapply CopyPropagation.copy_paramsMatch; eauto.
        eapply labelsDefined_paramsMatch; eauto.
    + eapply ConstantPropagationAnalysisCorrect.cp_reachability_sound_nil; eauto.
      * eapply (@safeFixpoint_fixpoint
                  _
                  (ConstantPropagationAnalysis.constant_propagation_analysis RA')).
      * eapply CopyPropagation.copy_paramsMatch; eauto.
        eapply labelsDefined_paramsMatch; eauto.
    + eapply LabelsDefined.paramsMatch_labelsDefined_nil.
      eapply CopyPropagation.copy_paramsMatch; eauto.
      eapply labelsDefined_paramsMatch; eauto.
    + isabsurd.
  - subst an.
    rewrite ConstantPropagationAnalysisCorrect.constantPropagationAnalysis_getAnn.
    unfold DomainSSA.domenv.
    rewrite ConstantPropagationCorrect.cp_eqns_no_assumption.
    + hnf; intros. cset_tac.
    + intros.
      rewrite <- ConstantPropagationAnalysisCorrect.constantPropagation_init_inv;
        eauto.
      unfold DomainSSA.domenv.
      reflexivity.
  - cases.
    * rewrite ConstantPropagationCorrect.cp_eqns_freeVars.
      rewrite renamedApart_freeVars; eauto. reflexivity.
    * rewrite ConstantPropagationCorrect.eqns_freeVars_singleton.
      simpl. clear_all. cset_tac.
Qed.

Definition slt (D:set var) (EV:For_all Even.even_pos_fast D)
  : Slot D.
  refine (@Build_Slot _ Pos.succ _ _).
  - hnf; intros.
    eapply EV in H.
    cset_tac'. eapply EV in H0.
    rewrite <- Even.even_pos_fast_correct in *.
    rewrite Even.even_not_even in H.
    Even.spos.
  - hnf; intros. eapply Pos.succ_inj; eauto.
Defined.

Definition max_reg := 19%positive.

Definition fromILF (s:stmt) o spo :=
  let s_eae := EAE.compile s in
  let sra := rename_apart_to_part FGS_even_fast_pos s_eae in
  let dcve := DCE Liveness.Imperative (fst sra) in
  let fvl := to_list (getAnn (snd dcve)) in
  let k := exp_vars_bound (fst dcve) in
  let spilled := spill spo k Pos.succ (fst dcve) (snd dcve) in
  let rdom := (domain_add FG_fast_pres (empty_domain FG_fast_pres)
                         (getAnn (snd (spilled)))) in
  let ren2 := snd (renameApart FG_fast_pres rdom id (fst spilled)) in
  let ras := rassign even_part_pos o max_reg ren2
                    (snd (renameApart_live FG_fast_pres
                                           rdom
                                           id
                                           (fst (spilled))
                                           (snd (spilled)))) in
  (fst dcve, ren2, ras).

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.


Definition slotted_vars (s:stmt) :=
  let s_eae := EAE.compile s in
  let sra := rename_apart_to_part FGS_even_fast_pos s_eae in
  let dcve := DCE Liveness.Imperative (fst sra) in
  let k := exp_vars_bound (fst dcve) in
  drop k (to_list (getAnn (snd dcve))).

Definition fromILF_fvl (s:stmt) :=
           to_list (freeVars (EAE.compile s)).

Definition fromILF_fvl_ren (s:stmt) : list var :=
  (fst
     (fresh_list FG_even_fast_pos (empty_domain FG_even_fast_pos)
                 (to_list (freeVars (EAE.compile s))))).

Hint Resolve Liveness.live_sound_overapproximation_I Liveness.live_sound_overapproximation_F.

Lemma length_to_list X `{OrderedType X}
  : forall x y : ⦃X⦄, x [=] y -> ❬to_list x❭ = ❬to_list y❭.
Proof.
  Transparent to_list.
  unfold to_list.
  unfold Proper, respectful; intros.
  rewrite !elements_length.
  rewrite H0. reflexivity.
Qed.

Opaque to_list.


Opaque to_list.


Lemma fromILF_fvl_ren_EAE X `{OrderedType X} Y s t (f:Y->Y) x
  : s [=] t
    -> ARange.range f x ❬to_list s❭ =
      ARange.range f x ❬to_list t❭.
Proof.
  unfold fromILF_fvl_ren. intros.
  f_equal.
  erewrite length_to_list; eauto.
Qed.


Lemma rename_apart_to_part_freeVars (s:stmt)
  : fst (getAnn (rename_apart_to_part_ra FGS_even_fast_pos s))
        [=]   of_list (fst
                         (fresh_list FG_even_fast_pos (empty_domain FG_even_fast_pos)
                                     (to_list (freeVars s)))).
Proof.
  unfold rename_apart_to_part_ra; simpl.
  rewrite fst_renamedApartAnn.
  reflexivity.
Qed.


Lemma fromILF_correct (s s':stmt) E (PM:LabelsDefined.paramsMatch s nil) o spo
      (OK:snd (fromILF s o spo) = Success s')
      (Def:defined_on (freeVars s) E)
  : sim F.state I.state bot3 SimExt (nil, E, s)
        (nil, (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                [Pos.succ ⊝ slotted_vars s <--
                          lookup_list (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                          (slotted_vars s)], s').
Proof.
  set (E':= id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E).
  set (E'':= (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
              [Pos.succ ⊝ slotted_vars s <-- lookup_list (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                        (slotted_vars s)]).
  unfold slotted_vars in *.
  let_unfold' fromILF OK. subst ras.
  eapply sim_trans with (S2:=F.state). {
    eapply EAE.sim_EAE.
  }
  refold.

  assert (AEF1:AppExpFree.app_expfree s_eae) by eapply EAE.EAE_app_expfree.
  assert (AEF2:AppExpFree.app_expfree (fst sra)). {
    eapply app_expfree_rename_apart; eauto.
  }
  assert (AEF3:AppExpFree.app_expfree (fst dcve)). {
    eapply DCE_app_expfree; eauto.
  }

  assert (RA:RenamedApart.renamedApart (fst sra) (rename_apart_to_part_ra FGS_even_fast_pos s_eae)). {
    eapply rename_apart_to_part_renamedApart.
  }

  assert (EVB:exp_vars_bounded k (fst dcve)). {
    eapply exp_vars_bound_sound.
  }

  assert (PM1:LabelsDefined.paramsMatch s_eae nil) by
      (eapply EAE.EAE_paramsMatch; eauto).
  assert (PM2:LabelsDefined.paramsMatch (fst sra) nil). {
    eapply labelsDefined_paramsMatch; eauto.
  }
  assert (PM3:LabelsDefined.paramsMatch (fst dcve) nil). {
    eapply DCE_paramsMatch; eauto.
  }

  assert (EV:For_all Even.even_pos_fast
                     (fst (getAnn (DCEra Liveness.Imperative (fst sra)
                                          (rename_apart_to_part_ra FGS_even_fast_pos s_eae)))
                          ∪ snd (getAnn (DCEra Liveness.Imperative (fst sra)
                                                (rename_apart_to_part_ra FGS_even_fast_pos s_eae))))). {
    pose proof (rename_to_subset_even s_eae) as HY1.
    rewrite DCE_ra_fst; eauto.
    rewrite DCE_ra_snd; eauto.
    subst sra. rewrite rename_apart_to_part_occurVars.
    eapply rename_to_subset_even.
  }
  pose (@slt _ EV) as slt.

  assert (NOC1:LabelsDefined.noUnreachableCode (LabelsDefined.isCalled true) (fst dcve)). {
    eapply DCE_noUC; eauto.
  }

  assert (Incl1:getAnn (snd dcve)
         ⊆ fst (getAnn (DCEra Liveness.Imperative (fst sra) (rename_apart_to_part_ra FGS_even_fast_pos s_eae)))). {
    exploit DCE_live_incl as INCL; eauto.
    eapply ann_R_get in INCL; eauto.
  }

  assert (PM4:LabelsDefined.paramsMatch (fst spilled) nil). {
    eapply spill_paramsMatch with (slt:=slt);
      eauto using DCE_live, DCE_renamedApart, DCE_live_incl, DCE_paramsMatch.
  }

  eapply sim_trans with (σ2:=(nil, E', fst sra):F.state). {
    eapply bisim_sim. eapply bisim_sym.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    - eapply rename_apart_alpha'; eauto.
      rewrite update_with_list_lookup_set_incl; eauto with len.
      rewrite <- fresh_list_domain_spec; eauto.
      rewrite fresh_list_len; eauto.
      rewrite of_list_3; eauto.
      instantiate (1:=id[fst (fresh_list FG_even_fast_pos
                                         (empty_domain FG_even_fast_pos)
                                         (to_list (freeVars s_eae)))
                             <-- to_list (freeVars s_eae)]).
      hnf; intros.
      rewrite <- of_list_3 in H.
      edestruct (of_list_get_first _ H) as [n]; eauto; dcr. hnf in H1. subst x0.
      eapply update_with_list_lookup_in_list_first in H4; dcr.
      rewrite H3.
      edestruct update_with_list_lookup_in_list_first; dcr.
      Focus 4. rewrite H5. hnf. instantiate (1:=n) in H4. get_functional.
      symmetry; eauto. rewrite fresh_list_len; eauto. eauto.
      intros.
      eapply NoDupA_get_neq'; [ eauto | eauto | | | eapply H4 | eapply H1 ].
      eapply fresh_list_nodup; eauto.
      eauto with len.
      rewrite fresh_list_len; eauto. eauto.
    - hnf; intros.
      decide (y ∈ freeVars s_eae).
      + unfold E'. simpl in H, H0.
        unfold fromILF_fvl_ren, fromILF_fvl. subst s_eae.
        unfold comp. simpl. rewrite H. reflexivity.
      + simpl in H,H0.
        rewrite lookup_set_update_not_in_Z in H0; [|rewrite of_list_3;eauto].
        unfold id in H0; subst x.
        subst E'.
        unfold fromILF_fvl_ren, fromILF_fvl. unfold comp; simpl.
        subst s_eae. rewrite H; eauto.
  }
  eapply sim_trans with (σ2:=(nil, E', fst sra):I.state). {
     eapply bisim_sim. eapply SimCompanion.simc_sim.
     eapply Invariance.srdSim_sim with (AL:=nil) (Lv:=nil); simpl; eauto using PIR2.
     - eapply renamedApart_coherent with (DL:=nil); simpl; eauto.
     - hnf; intros; isabsurd.
     - econstructor.
     - intros. inv H.
     - eapply renamedApart_live; simpl; eauto.
  }
  eapply sim_trans with (σ2:=(nil, E', fst dcve):I.state). {
    eapply DCE_correct_I; eauto.
  }

  assert (LS1:Liveness.live_sound Liveness.FunctionalAndImperative nil nil (fst spilled) (snd spilled)). {
    eapply spill_spill_live with (k:=k) (slt:=slt);
      eauto using DCE_live, DCE_renamedApart,
      DCE_live_incl, DCE_paramsMatch.
  }
  eapply sim_trans with (σ2:=(nil, E'', fst spilled):F.state). {
    assert (VP:var_P (inf_subset_P even_inf_subset_pos) (fst dcve)). {
      eapply DCE_var_P; eauto.
      eapply renameApart_var_P.
      - eauto.
      - intros. eapply FG_even_fast_inf_subset.
      - intros. eapply even_fast_list_even; eauto.
      - eapply even_fast_update_even; eauto.
    }
    eapply spill_correct with (k:=k) (slt:=slt);
        eauto using DCE_live, DCE_renamedApart, DCE_live_incl,
        DCE_paramsMatch.
    - hnf; intros.
      rewrite Incl1 in H.
      rewrite DCE_ra_fst in H; eauto.
      rewrite rename_apart_to_part_freeVars in H.
      edestruct update_with_list_lookup_in_list.
      Focus 3.
      destruct H0 as [? [? [? [? [? ?]]]]].
      unfold comp. rewrite H2.
      unfold fromILF_fvl in H1.
      Transparent to_list.
      eapply get_elements_in in H1.
      Opaque to_list.
      rewrite EAE.EAE_freeVars in H1.
      eapply Def in H1. eauto.
      unfold fromILF_fvl_ren, fromILF_fvl. simpl. len_simpl.
      reflexivity. eauto.
  }
  eapply sim_trans with (σ2:=(nil, E'',ren2):F.state). {
    eapply bisim_sim. eapply bisim_sym.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    - eapply rename_apart_alpha'; eauto.
      rewrite lookup_set_on_id; [|reflexivity].
      subst rdom. rewrite <- domain_add_spec; eauto.
      rewrite <- Liveness.freeVars_live; eauto with cset.
      eapply inverse_on_id.
    - eapply envCorr_idOn_refl.
  }
  eapply rassign_correct; eauto.
  - eapply labelsDefined_paramsMatch; eauto.
  - eapply renameApart'_renamedApart.
    + eauto.
    + rewrite lookup_set_on_id; [|reflexivity].
      instantiate (1:=(getAnn (snd spilled))).
      eapply Liveness.freeVars_live; eauto.
    + subst rdom. rewrite <- domain_add_spec; eauto.
  - eapply app_expfree_rename_apart; eauto.
    eapply spill_app_expfree; eauto.
  - unfold rename_apart.
    eapply (@renameApart_live_sound_srd _ _ _ _ _ Liveness.FunctionalAndImperative
                                        nil nil nil nil nil); eauto using PIR2.
    + isabsurd.
    + eapply spill_srd with (k:=k) (slt:=slt);
        eauto using DCE_live, DCE_renamedApart,
        DCE_live_incl, DCE_paramsMatch.
    + eapply spill_noUnreachableCode with (k:=k) (slt:=slt);
        eauto using DCE_live, DCE_renamedApart,
        DCE_live_incl, DCE_paramsMatch.
    + rewrite lookup_set_on_id; try reflexivity.
      subst rdom. rewrite <- domain_add_spec; eauto.
  - erewrite getAnn_snd_renameApart_live; eauto.
    rewrite fst_renamedApartAnn.
    exploit (@DCE_live_incl Liveness.Imperative) as INCL; eauto.
    eapply ann_R_get in INCL; eauto.
    rewrite lookup_set_on_id; [|reflexivity].
    reflexivity.
  - erewrite getAnn_snd_renameApart_live; eauto.
    rewrite lookup_set_on_id; [|reflexivity].
    subst spilled.
    eapply defined_on_incl; swap 1 2.
    eapply getAnn_spill with (slt:=slt);
      eauto using DCE_live, DCE_renamedApart,
      DCE_live_incl, DCE_paramsMatch.
    + eapply defined_on_union.
      * subst E'.
        eapply defined_on_update_list_disj.
        -- subst dcve. subst sra.
           unfold rename_apart_to_part.
           unfold fromILF_fvl_ren.
           rewrite TakeSet.take_list_incl.
           rewrite of_list_3.
           rewrite DCE_snd_lv_fst_ra; eauto.
           rewrite rename_apart_to_part_freeVars.
           subst s_eae.
           hnf; intros. eapply Def.
           rewrite <- (@EAE.EAE_freeVars s).
           unfold fromILF_fvl.
           setoid_rewrite <- (of_list_3 (freeVars (EAE.compile s))) at 3.
           eapply update_with_list_lookup_in. clear. rewrite fresh_list_len. reflexivity.
           eauto. eauto.
        -- subst fvl.
           rewrite TakeSet.take_list_incl.
           rewrite of_list_map; eauto.
           rewrite of_list_drop_incl.
           rewrite of_list_3.
           rewrite Incl1.
           rewrite DCE_ra_fst; eauto.
           rewrite rename_apart_to_part_freeVars; eauto.
           clear. hnf; intros.
           eapply even_fast_list_even in H0.
           cset_tac'.
           eapply even_fast_list_even in H.
           unfold even_inf_subset_pos in H. simpl in *.
           rewrite Even.even_pos_fast_succ in *.
           eapply negb_prop_elim in H0; eapply H0; eauto.
      * rewrite <- of_list_map; eauto.
        eapply defined_on_update_list'; eauto with len.
        -- subst fvl.
           change (Slot_slot slt) with Pos.succ.
           hnf; intros. clear - H. cset_tac.
        -- subst E'.
           rewrite lookup_list_map; eauto.
           rewrite <- defined_on_defined; eauto. subst fvl.
           unfold fromILF_fvl_ren, fromILF_fvl.
           rewrite of_list_drop_incl.
           rewrite of_list_3.
           rewrite Incl1.
           rewrite DCE_ra_fst; eauto.
           rewrite rename_apart_to_part_freeVars; eauto.
           subst s_eae.
           hnf; intros. eapply Def.
                      rewrite <- (@EAE.EAE_freeVars s).
           unfold fromILF_fvl.
           setoid_rewrite <- (of_list_3 (freeVars (EAE.compile s))) at 3.
           eapply update_with_list_lookup_in. clear. rewrite fresh_list_len. reflexivity.
           eauto. eauto.
           Grab Existential Variables. eauto.
Qed.

End Compiler.


Print Assumptions fromILF_correct.
Print Assumptions toILF_correct.
Print Assumptions optimize_correct.
