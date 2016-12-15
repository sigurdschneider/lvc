Require Import List CSet.
Require Import Util AllInRel MapDefined IL Sim Status Annotation.
Require Import Rename RenameApart RenameApart_Liveness.
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

Lemma var_P_occurVars (P:var -> Prop) s
  : var_P P s
    -> For_all P (occurVars s).
Proof.
  induction 1; unfold For_all in *; intros; simpl in *; cset_tac'.
  eapply list_union_get in H4. destruct H4; dcr; inv_get; cset_tac.
Qed.

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
  : fst (getAnn (snd (rename_apart_to_part1 s))) ∪ snd (getAnn (snd (rename_apart_to_part1 s)))
        [=] occurVars (fst (rename_apart_to_part1 s)).
Proof.
  unfold rename_apart_to_part1; simpl.
  rewrite occurVars_freeVars_definedVars.
  rewrite snd_renamedApartAnn.
  eapply eq_union_lr; eauto.
  rewrite fst_renamedApartAnn.
  rewrite freeVars_renamedApart'. admit.
  admit.
Admitted.

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

Definition slt (s:stmt) (ra:ann (set var * set var))
           (VP:var_P even s)
  : Slot (fst (getAnn (snd (rename_apart_to_part1 s))) ∪ snd (getAnn (snd (rename_apart_to_part1 s)))).
  refine (@Build_Slot _ S _ _).
  - hnf; intros. rewrite rename_apart_to_part1_occurVars in *.
    exploit (rename_to_subset_even _ H); eauto.
    eapply map_iff in H0; dcr; eauto. hnf in H4. subst.
    exploit (rename_to_subset_even _ H3); eauto.
    Opaque even. simpl in *.
    rewrite even_not_even in H0. cases in H1; simpl in *; eauto.
  - hnf; intros. cset_tac.
Qed.

Require Import RegAssign.

Definition fromILF (s:stmt) :=
  let s_eae := EAE.compile s in
  let sra := rename_apart_to_part1 s_eae in
  let dcve := DCVE Liveness.Imperative (fst sra) (snd sra) in
  let fvl := to_list (getAnn (co_lv dcve)) in
  let k := exp_vars_bound (co_s dcve) in
  let spilled := spill k (slt (co_s dcve) (co_ra dcve)) (co_s dcve) (co_lv dcve) in
  let ras := rassign parallel_move spilled in
  ras.

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.

Require Import MoreTac Alpha RenameApart_Alpha RenameApart_Liveness
        RenamedApart_Liveness Coherence Invariance.

Lemma fromILF_correct (s s':stmt) E (PM:LabelsDefined.paramsMatch s nil)
      (OK:fromILF s = Success s')
  : sim F.state F.state bot3 Sim (nil, E, s)
        (nil, id[fresh_list_stable (stable_fresh_P even_inf_subset) ∅ (to_list (freeVars (EAE.compile s))) <-- to_list (freeVars (EAE.compile s))] ∘ E, s').
Proof.
  set (E':=id [fresh_list_stable (stable_fresh_P even_inf_subset) ∅ (to_list (freeVars (EAE.compile s))) <-- to_list (freeVars (EAE.compile s))]∘ E).
  let_unfold' fromILF OK. subst ras.
  eapply sim_trans with (S2:=F.state). {
    eapply EAE.sim_EAE.
  }
  refold.
  assert (AEF:AppExpFree.app_expfree s_eae) by eapply EAE.EAE_app_expfree.

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
        unfold comp.
        rewrite H. eauto.
      + rewrite lookup_set_update_not_in_Z in H0; eauto.
        subst; reflexivity.
        rewrite of_list_3; eauto.
  }
  assert (RA:RenamedApart.renamedApart (fst sra) (snd sra)). {
    eapply rename_apart_to_part1_renamedApart.
  }
  assert (LabelsDefined.paramsMatch (fst sra) nil). {
    admit.
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
  eapply sim_trans with (S2:=F.state). {
    eapply spill_correct with (k:=k) (slt:=(slt (co_s dcve)));
      eauto using DCVE_live, DCVE_noUC, DCVE_renamedApart, DCVE_live_incl, DCVE_paramsMatch.
    - admit.
    - admit.
    - eapply DCVE_renamedApart.

    - eapply exp_vars_bound_sound.
    - exploit DCVE_live_incl as INCL; eauto.
      eapply ann_R_get in INCL; eauto.
  }
  instantiate (1:=(Slot_slot (slt (co_s dcve)))).
  change (DCVE Liveness.Imperative (fst sra) (snd sra)) with dcve.

    admit.

    admit. admit. admit.
  }
  admit.
Admitted.

  eapply (@sim_trans _ I.state _ I.state).
  eapply
  repeat let_case_eq; repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
  set (s_ren := rename_apart (EAE.compile s)).
  set (s_dcve :=
  monadS_inv H.
  exploit (@ParallelMove.correct parallel_move nil); try eapply EQ0; try now econstructor; eauto.
  eapply (@Liveness.live_rename_sound _ nil nil).
  eapply (@renameApart_live_sound_srd _ nil nil nil nil nil); eauto.
  clear; isabsurd.
  eapply (@Delocation.live_sound_compile nil nil nil nil); eauto.
  eapply DelocationAlgo.is_trs; eauto.
  eapply (@ReconstrLiveSound.reconstr_live_sound _ _ nil _ nil).


  eapply AllocationAlgo.regAssign_renamedApart_agree in EQ; eauto;
    [|eapply rename_apart_renamedApart; eauto
     |].

  Focus 5. eapply DCVE_live; eauto. eapply EAE.EAE_paramsMatch. eauto.
  admit.
  reflexivity. reflexivity. isabsurd.
  eapply (sim_trans _ H).
  Unshelve.
  eapply sim_trans with (σ2:=(nil:list F.block, E, EAE.compile s)).
  eapply EAE.sim_EAE.
  eapply sim_trans with (σ2:=(nil:list F.block, E, fst (DCVE Liveness.Functional (EAE.compile s)))).
  eapply DCVE_correct_F; eauto. eapply EAE.EAE_paramsMatch; eauto.
  admit.
  eapply sim_trans with (σ2:=(nil:list F.block, E, _)).
  eapply bisim_sim.
  eapply (@Alpha.alphaSim_sim (nil, E, _) (nil, E, _)).
  econstructor; eauto using PIR2, Alpha.envCorr_idOn_refl.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.

  eapply sim_trans with (σ2:=(nil:list F.block, E, _)).
  eapply bisim_sim.
  eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
  instantiate (2:=id).
  eapply Allocation.renamedApart_locally_inj_alpha; eauto.
  eapply rename_apart_renamedApart; eauto.
  eapply AllocationAlgoCorrect.regAssign_correct; eauto.
  admit.
  eapply RenameApart_Liveness.renameApart_live_sound.
  eapply Liveness.live_sound_overapproximation_F; eauto.
  eapply AllocationAlgo.regAssign_renamedApart_agree in EQ1; eauto.
  rewrite fst_renamedApartAnn in EQ1.

  eapply (@Liveness.live_rename_sound _ nil nil); eauto.
  admit.
  eapply sim_trans with (σ2:=(nil, E, rename (CMap.findt x 0) (rename_apart (fst (DCVE (EAE.compile s)))))); eauto.
  eapply Liveness.live_sound_overapproximation_I; eauto.
  eauto.

  exploit rename_apart_renamedApart; eauto.
  exploit AllocationAlgoCorrect.regAssign_correct' as XXX; eauto. admit. admit. admit. admit. admit.
  - eapply injective_on_agree; [| eapply CMap.map_update_list_update_agree; reflexivity].
    hnf; intros ? ? ? ? EqMap.
    rewrite lookup_update_same in EqMap.
    rewrite EqMap; eauto. rewrite lookup_update_same; eauto with cset.
    rewrite of_list_3; eauto.
    rewrite of_list_3; eauto.
  - rewrite fst_renamedApartAnn. eauto.
  - eapply sim_trans with (σ2:=(nil:list F.block, E,
                                    rename (CMap.findt x0 0)
                                           (rename_apart (EAE.compile s)))).
    eapply bisim_sim.
    eapply Alpha.alphaSim_sim. econstructor; eauto using PIR2.
    instantiate (1:=id).
    eapply Allocation.renamedApart_locally_inj_alpha; eauto.
    eapply Liveness.live_sound_overapproximation_F; eauto.
    eapply AllocationAlgo.regAssign_renamedApart_agree in EQ1; eauto.
    rewrite fst_renamedApartAnn in EQ1.
    rewrite <- CMap.map_update_list_update_agree in EQ1; eauto.
    hnf; intros. repeat rewrite <- EQ1; eauto;
                   repeat rewrite lookup_update_same; eauto;
                     rewrite of_list_3; eauto.
    hnf; intros ? ? ? EQy. cbv in EQy. subst. rewrite EQy. reflexivity.
    eapply sim_trans with (S2:=I.state).
    eapply bisim_sim.
    eapply Coherence.srdSim_sim.
    econstructor. eapply Allocation.rename_renamedApart_srd; eauto.
    rewrite fst_renamedApartAnn; eauto.
    eapply I. isabsurd. econstructor. reflexivity.
    eapply (@Liveness.live_rename_sound _ nil); eauto.
    eapply Liveness.live_sound_overapproximation_I; eauto.
    econstructor.
    eapply (ParallelMove.pmSim_sim).
    econstructor; try now econstructor; eauto.
    eapply (@Liveness.live_rename_sound _ nil); eauto.
    eapply Liveness.live_sound_overapproximation_I; eauto.
    eauto.
Qed.
 *)


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
