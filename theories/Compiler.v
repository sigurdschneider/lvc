Require Import List CSet.
Require Import Util AllInRel MapDefined IL Sim Status Annotation VarP.
Require Import Rename RenameApart RenameApart_Liveness RenameApart_VarP.
Require CMap.
Require Liveness LivenessValidators ParallelMove ILN ILN_IL.
Require TrueLiveness LivenessAnalysis LivenessAnalysisCorrect.
Require Coherence Invariance.
Require Delocation DelocationAlgo DelocationCorrect DelocationValidator.
Require Allocation AllocationAlgo AllocationAlgoCorrect.
Require UCE DVE EAE Alpha.
Require ReachabilityAnalysis ReachabilityAnalysisCorrect.
Require Import DCVE Slot InfinitePartition RegAssign ExpVarsBounded.
(* Require CopyPropagation ConstantPropagation ConstantPropagationAnalysis.*)

Require Import String.

Set Implicit Arguments.

Section Compiler.

Hypothesis ssa_construction : stmt -> ann (option (set var)) * ann (list var).
Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).
Hypothesis first : forall (A:Type), A -> ( A -> status (A * bool)) -> status A.

Arguments first {A} _ _.


(*Definition constantPropagationAnalysis :=
Analysis.fixpoint ConstantPropagationAnalysis.constant_propagation_analysis first. *)


Class ToString (T:Type) := toString : T -> string.

Hypothesis OutputStream : Type.
Hypothesis print_string : OutputStream -> string -> OutputStream.

Hypothesis toString_nstmt : ILN.nstmt -> string.
Instance ToString_nstmt : ToString ILN.nstmt := toString_nstmt.

Hypothesis toString_stmt : stmt -> string.
Instance ToString_stmt : ToString stmt := toString_stmt.

Hypothesis toString_ann : forall A, (A -> string) -> ann A -> string.
Instance ToString_ann {A} `{ToString A} : ToString (ann A) :=
  toString_ann (@toString A _).

Hypothesis toString_live : set var -> string.
Instance ToString_live : ToString (set var) := toString_live.

Hypothesis toString_list : list var -> string.
Instance ToString_list : ToString (list var) := toString_list.

Notation "S '<<' x '<<' y ';' s" := (let S := print_string S (x ++ "\n" ++ toString y ++ "\n\n") in s) (at level 1, left associativity).

Definition ensure_f P `{Computable P} (s: string) {A} (cont:status A) : status A :=
if [P] then cont else Error s.

Arguments ensure_f P [H] s {A} cont.

Notation "'ensure' P s ; cont " := (ensure_f P s cont)
                                    (at level 20, P at level 0, s at level 0, cont at level 200, left associativity).

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

(*
Definition toILF (s:IL.stmt) : IL.stmt :=
  let (s_dcve, lv) := DCVE Liveness.Imperative s in
  addParams s_dcve lv.

Lemma toILF_correct (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state F.state bot3 Sim (nil, E, ili) (nil:list F.block, E, toILF ili).
Proof with eauto using DCVE_live, DCVE_noUC.
  intros. subst. unfold toILF.
  eapply sim_trans with (S2:=I.state).
  eapply DCVE_correct_I; eauto. let_pair_case_eq; simpl_pair_eqs; subst.
  unfold fst at 1.
  eapply addParams_correct...
  eauto using defined_on_incl, DCVE_occurVars.
Qed.
 *)

(*
Definition optimize (s':stmt) : status stmt :=
  let s := rename_apart s' in
  sdo ALAE <- constantPropagationAnalysis s;
  match ALAE with
    | (AL, AEc) =>
      let AE := (fun x => MapInterface.find x AEc) in
      ensure (ConstantPropagation.cp_sound AE nil s)
             "Constant propagation unsound";
      ensure (forall x, x ∈ freeVars s' -> AE x = None)
             "Constant propagation makes no assumptions on free vars";
      let s := ConstantPropagation.constantPropagate AE s in
      sdo lv <- livenessAnalysis s;
      ensure (TrueLiveness.true_live_sound Liveness.Functional nil s lv) "Liveness unsound (2)";
      Success (DVE.compile nil s lv)
  end.
*)

Print all.

Require Import RenameApart_VarP.

Require Import StableFresh.

Definition rename_apart_to_part1 (s:stmt) :=
  let xl := (fresh_list_stable (stable_fresh_P even_inf_subset)
                              ∅
                              (to_list (freeVars s))) in
  let s' := (renameApart' (stable_fresh_P even_inf_subset)
                       (id [to_list (freeVars s) <-- xl])
                       (of_list xl)
                       s) in
  (co_ra s', renamedApartAnn (co_ra s') (of_list xl)).

Opaque to_list.

Lemma rename_apart_to_part1_renamedApart s
  : RenamedApart.renamedApart (fst (rename_apart_to_part1 s))
                              (snd (rename_apart_to_part1 s)).
Proof.
  unfold rename_apart_to_part1. simpl.
  eapply renameApart'_renamedApart.
  - rewrite update_with_list_lookup_set_incl; eauto with len.
    rewrite of_list_3; eauto.
  - reflexivity.
Qed.


Lemma rename_apart_to_part1_occurVars s
  : fst (getAnn (snd (rename_apart_to_part1 s)))
        ∪ snd (getAnn (snd (rename_apart_to_part1 s)))
        [=] occurVars (fst (rename_apart_to_part1 s)).
Proof.
  unfold rename_apart_to_part1; simpl.
  rewrite occurVars_freeVars_definedVars.
  rewrite snd_renamedApartAnn.
  eapply eq_union_lr; eauto.
  rewrite fst_renamedApartAnn.
  rewrite freeVars_renamedApart'.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + eapply DelocationAlgo.nodup_to_list_var.
    + rewrite of_list_3; eauto.
  - rewrite update_with_list_lookup_list_eq; eauto with len.
    + eapply DelocationAlgo.nodup_to_list_var.
    + rewrite of_list_3; eauto.
Qed.

Lemma rename_to_subset_even (s:stmt)
  : For_all (inf_subset_P even_inf_subset)
            (occurVars (fst (rename_apart_to_part1 s))).
Proof.
  eapply var_P_occurVars.
  eapply renameApart_var_P.
  - intros. eapply least_fresh_P_full_spec.
  - intros.
    edestruct update_with_list_lookup_in_list; dcr.
    Focus 3. rewrite H3. hnf in H5. subst.
    exploit fresh_list_stable_get; eauto; dcr; subst.
    eapply least_fresh_P_full_spec.
    eauto with len. rewrite of_list_3; eauto.
Qed.

Definition slt (D:set var) (EV:For_all even D)
  : Slot D.
  refine (@Build_Slot _ S _ _).
  - hnf; intros.
    eapply EV in H.
    cset_tac'. eapply EV in H0.
    rewrite even_not_even in H. cset_tac.
  - hnf; intros. cset_tac.
Defined.

Require Import RegAssign.

Definition fromILF (s:stmt) :=
  let s_eae := EAE.compile s in
  let sra := rename_apart_to_part1 s_eae in
  let dcve := DCVE Liveness.Imperative (fst sra) (snd sra) in
  let fvl := to_list (getAnn (co_lv dcve)) in
  let k := exp_vars_bound (co_s dcve) in
  let spilled := spill k S (co_s dcve) (co_lv dcve) in
  let ren2 := snd (renameApart' (stable_fresh_part even_part)
                               id (getAnn (snd (spilled))) (fst spilled)) in
  let ras := rassign parallel_move ren2
                    (snd (renameApart_live (stable_fresh_part even_part)
                                           id (getAnn (snd (spilled)))
                                           (fst (spilled))
                                           (snd (spilled)))) in
  ras.

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.

Require Import MoreTac Alpha RenameApart_Alpha RenameApart_Liveness
        RenamedApart_Liveness Coherence Invariance.

Definition slotted_vars (s:stmt) :=
  let s_eae := EAE.compile s in
  let sra := rename_apart_to_part1 s_eae in
  let dcve := DCVE Liveness.Imperative (fst sra) (snd sra) in
  let k := exp_vars_bound (co_s dcve) in
  drop k (to_list (getAnn (co_lv dcve))).

Definition fromILF_fvl (s:stmt) :=
           to_list (freeVars (EAE.compile s)).

Definition fromILF_fvl_ren (s:stmt) :=
  fresh_list_stable (stable_fresh_P even_inf_subset) ∅ (to_list (freeVars (EAE.compile s))).

Hint Resolve Liveness.live_sound_overapproximation_I Liveness.live_sound_overapproximation_F.

Instance length_to_list_morphism X `{OrderedType X}
  : Proper (Equal ==> eq) (fun x => ❬(@to_list X _ _ _ x)❭).
Proof.
  Transparent to_list.
  unfold to_list.
  unfold Proper, respectful; intros.
  rewrite !elements_length.
  rewrite H0. reflexivity.
Qed.

Opaque to_list.

Lemma fromILF_fvl_ren_EAE s
  : of_list (fromILF_fvl_ren (EAE.compile s)) [=] of_list (fromILF_fvl_ren s).
Proof.
  unfold fromILF_fvl_ren.
  eapply fresh_list_stable_P_ext_eq.
  eapply length_to_list_morphism.
  rewrite EAE.EAE_freeVars; eauto.
Qed.

Lemma rename_apart_to_part1_freeVars s
  : fst (getAnn (snd (rename_apart_to_part1 s)))
        [=] of_list (fromILF_fvl_ren s).
Proof.
  unfold rename_apart_to_part1; simpl.
  rewrite fst_renamedApartAnn.
  unfold fromILF_fvl_ren.
  eapply fresh_list_stable_P_ext_eq.
  eapply length_to_list_morphism.
  rewrite EAE.EAE_freeVars; eauto.
Qed.

Lemma fromILF_correct (s s':stmt) E (PM:LabelsDefined.paramsMatch s nil)
      (OK:fromILF s = Success s')
      (Def:defined_on (freeVars s) E)
  : sim F.state I.state bot3 Sim (nil, E, s)
        (nil, (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                 [S ⊝ slotted_vars s <-- lookup_list (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                    (slotted_vars s)], s').
Proof.
  set (E':= id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E).
  set (E'':= (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
              [S ⊝ slotted_vars s <-- lookup_list (id [fromILF_fvl_ren s <-- fromILF_fvl s] ∘ E)
                 (slotted_vars s)]).
  let_unfold' fromILF OK. subst ras.
  eapply sim_trans with (S2:=F.state). {
    eapply EAE.sim_EAE.
  }
  refold.

  assert (AEF1:AppExpFree.app_expfree s_eae) by eapply EAE.EAE_app_expfree.
  assert (AEF2:AppExpFree.app_expfree (fst sra)). {
    eapply app_expfree_rename_apart; eauto.
  }
  assert (AEF3:AppExpFree.app_expfree (co_s dcve)). {
    eapply DCVE_app_expfree; eauto.
  }

  assert (RA:RenamedApart.renamedApart (fst sra) (snd sra)). {
    eapply rename_apart_to_part1_renamedApart.
  }

  assert (EVB:exp_vars_bounded k (co_s dcve)). {
    eapply exp_vars_bound_sound.
  }

  assert (PM1:LabelsDefined.paramsMatch s_eae nil) by
      (eapply EAE.EAE_paramsMatch; eauto).
  assert (PM2:LabelsDefined.paramsMatch (fst sra) nil). {
    eapply labelsDefined_paramsMatch; eauto.
  }
  assert (PM3:LabelsDefined.paramsMatch (co_s dcve) nil). {
    eapply DCVE_paramsMatch; eauto.
  }

  assert (EV:For_all (fun n : nat => even n)
                     (fst (getAnn (snd (DCVE Liveness.Imperative (fst sra) (snd sra))))
                          ∪ snd (getAnn (snd (DCVE Liveness.Imperative (fst sra) (snd sra)))))). {
    pose proof (rename_to_subset_even s_eae) as HY1.
    rewrite DCVE_ra_fst; eauto.
    rewrite DCVE_ra_snd; eauto.
    subst sra. rewrite rename_apart_to_part1_occurVars.
    eapply rename_to_subset_even.
  }
  pose (@slt _ EV) as slt.

  assert (NOC1:LabelsDefined.noUnreachableCode (LabelsDefined.isCalled true) (co_s dcve)). {
    eapply DCVE_noUC; eauto.
  }

  assert (Incl1:getAnn (co_lv dcve)
         ⊆ fst (getAnn (snd (DCVE Liveness.Imperative (fst sra) (snd sra))))). {
    exploit DCVE_live_incl as INCL; eauto.
    eapply ann_R_get in INCL; eauto.
  }

  assert (PM4:LabelsDefined.paramsMatch (fst spilled) nil). {
    eapply spill_paramsMatch with (slt:=slt);
      eauto using DCVE_live, DCVE_renamedApart, DCVE_live_incl, DCVE_paramsMatch.
  }

  eapply sim_trans with (σ2:=(nil, E', fst sra):F.state). {
    eapply bisim_sim. eapply bisim_sym.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    - eapply rename_apart_alpha'; eauto.
      rewrite update_with_list_lookup_set_incl; eauto with len.
      rewrite of_list_3; eauto.
      instantiate (1:=id[fresh_list_stable (stable_fresh_P even_inf_subset)
                                           ∅ (to_list (freeVars s_eae)) <--to_list (freeVars s_eae)]).
      hnf; intros.
      rewrite <- of_list_3 in H.
      edestruct (of_list_get_first _ H) as [n]; eauto; dcr. hnf in H1. subst x0.
      eapply update_with_list_lookup_in_list_first in H4; dcr.
      rewrite H3.
      edestruct update_with_list_lookup_in_list_first; dcr.
      Focus 4. rewrite H5. hnf. instantiate (1:=n) in H4. get_functional.
      symmetry; eauto. eauto with len. eauto.
      intros.
      eapply NoDupA_get_neq'; [ eauto | eauto | | | eapply H4 | eapply H1 ].
      eapply fresh_list_stable_nodup. eauto.
      eauto with len.
      eauto.
    - hnf; intros.
      decide (y ∈ freeVars s_eae).
      + unfold E'.
        unfold comp. unfold fromILF_fvl, fromILF_fvl_ren.
        subst s_eae.
        rewrite H. eauto.
      + rewrite lookup_set_update_not_in_Z in H0; eauto.
        subst; reflexivity.
        rewrite of_list_3; eauto.
  }
  eapply sim_trans with (σ2:=(nil, E', fst sra):I.state). {
     eapply bisim_sim.
     eapply Invariance.srdSim_sim; simpl; eauto using PIR2.
     - eapply renamedApart_coherent with (DL:=nil); simpl; eauto.
     - hnf; intros; isabsurd.
     - econstructor.
     - eapply renamedApart_live; simpl; eauto.
     - econstructor.
  }
  eapply sim_trans with (σ2:=(nil, E', co_s dcve):I.state). {
    eapply DCVE_correct_I; eauto.
  }

  assert (LS1:Liveness.live_sound Liveness.FunctionalAndImperative nil nil (fst spilled) (snd spilled)). {
    eapply spill_live with (k:=k) (slt:=slt);
      eauto using DCVE_live, DCVE_renamedApart,
      DCVE_live_incl, DCVE_paramsMatch.
  }
  eapply sim_trans with (σ2:=(nil, E'', fst spilled):F.state). {
    assert (VP:var_P (inf_subset_P even_inf_subset) (co_s dcve)). {
      eapply DCVE_var_P; eauto.
      eapply renameApart_var_P.
      - intros. eapply least_fresh_P_full_spec.
      - intros.
        edestruct update_with_list_lookup_in_list.
        Focus 3. destruct H0 as [? [? [? [? [? ?]]]]].
        rewrite H2. hnf in H3. subst.
        exploit fresh_list_stable_get; eauto; dcr; subst.
        eapply least_fresh_P_full_spec.
        eauto with len. rewrite of_list_3; eauto.
    }
    eapply spill_correct with (k:=k) (slt:=slt);
        eauto using DCVE_live, DCVE_renamedApart, DCVE_live_incl,
        DCVE_paramsMatch.
    - hnf; intros.
      unfold dcve, sra, s_eae in Incl1.
      rewrite Incl1 in H.
      rewrite DCVE_ra_fst in H; eauto.
      rewrite rename_apart_to_part1_freeVars in H.
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
      unfold fromILF_fvl_ren, fromILF_fvl.
      eauto with len.
      rewrite <- fromILF_fvl_ren_EAE. eauto.
  }
  eapply sim_trans with (σ2:=(nil, E'',ren2):F.state). {
    eapply bisim_sim. eapply bisim_sym.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    - eapply rename_apart_alpha'; eauto.
      rewrite lookup_set_on_id; [|reflexivity].
      eapply Liveness.freeVars_live; eauto.
      eapply inverse_on_id.
    - eapply envCorr_idOn_refl.
  }
  eapply rassign_correct; eauto.
  - eapply labelsDefined_paramsMatch; eauto.
  - eapply renameApart'_renamedApart.
    + rewrite lookup_set_on_id; [|reflexivity].
      instantiate (1:=(getAnn (snd spilled))).
      eapply Liveness.freeVars_live; eauto.
    + reflexivity.
  - unfold rename_apart.
    eapply (@renameApart_live_sound_srd _ _ Liveness.FunctionalAndImperative
                                        nil nil nil nil nil); eauto using PIR2.
    + isabsurd.
    + eapply spill_srd with (k:=k) (slt:=slt);
        eauto using DCVE_live, DCVE_renamedApart,
        DCVE_live_incl, DCVE_paramsMatch.
    + eapply spill_noUnreachableCode with (k:=k) (slt:=slt);
        eauto using DCVE_live, DCVE_renamedApart,
        DCVE_live_incl, DCVE_paramsMatch.
    + rewrite lookup_set_on_id; try reflexivity.
  - erewrite getAnn_snd_renameApart_live; eauto.
    rewrite fst_renamedApartAnn.
    exploit (@DCVE_live_incl Liveness.Imperative) as INCL; eauto.
    eapply ann_R_get in INCL; eauto.
    rewrite lookup_set_on_id; [|reflexivity].
    reflexivity.
Qed.



(*
Lemma optimize_correct (E:onv val) s s'
: optimize s = Success s'
  -> LabelsDefined.labelsDefined s 0
  -> sim (nil:list F.block, E, s) (nil:list F.block, E, s').
Proof.
  intros.
  unfold optimize, ensure_f in *.
  monadS_inv H. destruct x.
  repeat (cases in EQ0; [| isabsurd]).
  monadS_inv EQ0.
  repeat (cases in EQ2; [| isabsurd]).
  invc EQ2.

  eapply sim_trans with (S2:=F.state).
  eapply bisim_sim.
  eapply Alpha.alphaSim_sim. econstructor; eauto using rename_apart_alpha, PIR2.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha. hnf; intros.
  cbv in H, H1. instantiate (1:=E). congruence.
  eapply sim_trans with (S2:=F.state).
  Focus 2.
  eapply DVE.sim_DVE; eauto. reflexivity.
  eapply sim'_sim.
  eapply ValueOpts.sim_vopt; eauto.
  Focus 2.
  eapply ConstantPropagation.cp_sound_eqn; eauto.
  eapply rename_apart_renamedApart. instantiate (1:=nil). simpl.
  eapply labelsDefined_rename_apart; eauto.
  intros; isabsurd.
  rewrite fst_renamedApartAnn.
  intros. hnf; intros.
  rewrite ConstantPropagation.cp_eqns_no_assumption in H. cset_tac; intuition. eassumption.
  constructor.
  eapply rename_apart_renamedApart.
  rewrite fst_renamedApartAnn.
  rewrite ConstantPropagation.cp_eqns_no_assumption. eapply incl_empty. eauto.
  hnf; intuition.
Qed.
*)

End Compiler.

Print Assumptions toDeBruijn_correct.
Print Assumptions toILF_correct.
(* Print Assumptions fromILF_correct.
   Print Assumptions optimize_correct. *)
