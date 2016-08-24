Require Import List CSet.
Require Import Util AllInRel MapDefined IL Rename RenameApart Sim BisimSim Status Annotation.
Require CMap.
Require Liveness LivenessValidators ParallelMove ILN ILN_IL.
Require TrueLiveness LivenessAnalysis LivenessAnalysisCorrect.
Require Coherence Invariance.
Require Delocation DelocationAlgo DelocationCorrect DelocationValidator.
Require Allocation AllocationAlgo AllocationAlgoCorrect.
Require UCE DVE EAE Alpha.
Require UnreachableCodeAnalysis UnreachableCodeAnalysisCorrect.
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


Definition additionalArguments s lv :=
  fst (DelocationAlgo.computeParameters nil nil nil s lv).

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
   ->  @sim _ ILN.statetype_I _ _ Bisim
           (ILN.I.labenv_empty, E, ilin)
           (nil:list I.block, E, s).
Proof.
  intros. unfold toDeBruijn in H. simpl in *.
  eapply ILN_IL.labIndicesSim_sim.
  econstructor; eauto; isabsurd. econstructor; isabsurd. constructor.
Qed.

Arguments sim S {H} S' {H0} t _ _.

Definition DCVE (s:IL.stmt) : stmt * ann (set var) :=
  let uc := UnreachableCodeAnalysis.unreachableCodeAnalysis s in
  let s_uce := UCE.compile nil s uc in
  let tlv := LivenessAnalysis.livenessAnalysis s_uce in
  let s_dve := DVE.compile nil s_uce tlv in
  (s_dve, DVE.compile_live s_uce tlv ∅).

Lemma DCVE_live (ili:IL.stmt) (PM:LabelsDefined.paramsMatch ili nil)
  : Liveness.live_sound Liveness.Imperative nil nil (fst (DCVE ili)) (snd (DCVE ili)).
Proof.
  unfold DCVE. simpl.
  eapply (@DVE.dve_live _ nil nil).
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  eapply UnreachableCode.unreachable_code_SC_S, UnreachableCodeAnalysisCorrect.correct; eauto.
  eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
Qed.

Lemma DCVE_noUC ili (PM:LabelsDefined.paramsMatch ili nil)
  : LabelsDefined.noUnreachableCode LabelsDefined.isCalled (fst (DCVE ili)).
Proof.
  intros. subst. simpl.
  eapply LabelsDefined.noUnreachableCode_mono.
  - eapply (@DVE.DVE_noUnreachableCode _ nil nil).
    + eapply @LivenessAnalysisCorrect.correct; eauto.
      eapply (@UCE.UCE_paramsMatch nil nil); eauto.
      * eapply UnreachableCode.unreachable_code_SC_S, UnreachableCodeAnalysisCorrect.correct; eauto.
      * eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
    + eapply UCE.UCE_noUnreachableCode.
      * eapply UnreachableCodeAnalysisCorrect.correct; eauto.
      * eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
  - eapply LabelsDefined.trueIsCalled_isCalled.
Qed.

Lemma DCVE_occurVars s (PM:LabelsDefined.paramsMatch s nil)
  : getAnn (snd (DCVE s)) ⊆ occurVars s.
Proof.
  simpl.
  rewrite DVE.compile_live_incl_empty; eauto.
  rewrite LivenessAnalysisCorrect.livenessAnalysis_getAnn.
  eapply UCE.compile_occurVars.
  eapply @LivenessAnalysisCorrect.correct; eauto.
  eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  * eapply UnreachableCode.unreachable_code_SC_S, UnreachableCodeAnalysisCorrect.correct; eauto.
  * eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
Qed.

Lemma DCVE_correct (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state I.state Sim (nil, E, ili) (nil, E, fst (DCVE ili)).
Proof.
  intros. subst. unfold DCVE.
  simpl in *; unfold ensure_f, additionalArguments in *.
  assert (UnreachableCode.unreachable_code UnreachableCode.SoundAndComplete nil ili
                                           (UnreachableCodeAnalysis.unreachableCodeAnalysis ili)). {
    eapply UnreachableCodeAnalysisCorrect.correct; eauto.
  }
  assert (getAnn (UnreachableCodeAnalysis.unreachableCodeAnalysis ili)). {
    eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
  }
  assert (LabelsDefined.paramsMatch
            (UCE.compile nil ili (UnreachableCodeAnalysis.unreachableCodeAnalysis ili)) nil). {
    eapply (@UCE.UCE_paramsMatch nil nil); eauto.
  }
  assert (TrueLiveness.true_live_sound Liveness.Imperative nil nil
   (UCE.compile nil ili (UnreachableCodeAnalysis.unreachableCodeAnalysis ili))
   (LivenessAnalysis.livenessAnalysis
      (UCE.compile nil ili (UnreachableCodeAnalysis.unreachableCodeAnalysis ili)))). {
    eapply @LivenessAnalysisCorrect.correct; eauto.
  }
  eapply sim_trans with (S2:=I.state).
  eapply BisimSim.bisim_sim'.
  eapply UCE.I.sim_UCE.
  eapply UnreachableCode.unreachable_code_SC_S, UnreachableCodeAnalysisCorrect.correct; eauto.
  eapply UnreachableCodeAnalysisCorrect.unreachableCodeAnalysis_getAnn.
  eapply DVE.I.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
Qed.

Definition toILF (ili:IL.stmt) : IL.stmt :=
  let (s_dcve, lv) := DCVE ili in
  let additional_params := additionalArguments s_dcve lv in
  Delocation.compile nil s_dcve additional_params.

Lemma toILF_correct (ili:IL.stmt) (E:onv val)
  (PM:LabelsDefined.paramsMatch ili nil)
  : defined_on (IL.occurVars ili) E
    -> sim I.state F.state Sim (nil, E, ili) (nil:list F.block, E, toILF ili).
Proof with eauto using DCVE_live, DCVE_noUC.
  intros. subst. unfold toILF.
  eapply sim_trans with (S2:=I.state).
  eapply DCVE_correct; eauto. let_pair_case_eq; simpl_pair_eqs; subst.
  unfold fst at 1.
  eapply sim_trans with (S2:=I.state).
  - eapply BisimSim.bisim_sim'.
    eapply DelocationCorrect.correct; eauto.
    + eapply DelocationAlgo.is_trs; eauto...
    + eapply (@Delocation.live_sound_compile nil)...
      eapply DelocationAlgo.is_trs...
      eapply DelocationAlgo.is_live...
    + eapply defined_on_incl; eauto.
      eapply DCVE_occurVars...
  - eapply BisimSim.bisim_sim'.
    eapply sim_sym.
    eapply (@Invariance.srdSim_sim nil nil nil nil nil);
      [ | isabsurd | econstructor | reflexivity | | econstructor ].
    + eapply Delocation.trs_srd; eauto.
      eapply DelocationAlgo.is_trs...
    + eapply (@Delocation.live_sound_compile nil nil nil)...
      eapply DelocationAlgo.is_trs...
      eapply DelocationAlgo.is_live...
Qed.

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

(*
Definition fromILF (s:stmt) : status stmt :=
  let (s_dcve, lv) := DCVE s in
  let s_eae := EAE.compile s_dcve in
  let s_ra := rename_apart s_eae in
  let fvl := to_list (getAnn lv) in
  let ϱ := CMap.update_map_with_list fvl fvl (@MapInterface.empty var _ _ _) in
  sdo ϱ' <- AllocationAlgo.regAssign s_ra lv ϱ;
    let s_allocated := rename (CMap.findt ϱ' 0) s_ra in
    let s_lowered := ParallelMove.lower parallel_move
                                       nil
                                       s_allocated
                                       (mapAnn (map (CMap.findt ϱ' 0)) lv) in
    s_lowered.

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.


Lemma fromILF_correct (s s':stmt) E
  : fromILF s = Success s'
  -> sim F.state I.state Sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros.
  let_case_eq; simpl_pair_eqs; subst.
  monadS_inv H.

  eapply sim_trans with (σ2:=(nil:list F.block, E, rename_apart (EAE.compile s))).
  eapply sim_trans with (σ2:=(nil:list F.block, E, EAE.compile s)).
  eapply bisim_sim'. eapply EAE.sim_EAE.
  eapply bisim_sim'.
  eapply (@Alpha.alphaSim_sim (nil, E, _) (nil, E, _)).
  econstructor; eauto using PIR2, Alpha.envCorr_idOn_refl.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.
  exploit rename_apart_renamedApart; eauto.
  exploit AllocationAlgoCorrect.regAssign_correct'; eauto.
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
