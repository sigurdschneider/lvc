Require Import List CSet.
Require Import Util AllInRel MapDefined IL Rename EnvTy RenameApart Sim BisimSim Status Annotation.
Require CMap.
Require Liveness LivenessValidators ParallelMove ILN ILN_IL.
Require TrueLiveness LivenessAnalysis LivenessAnalysisCorrect.
Require Coherence Invariance.
Require Delocation DelocationAlgo DelocationCorrect DelocationValidator.
Require Allocation AllocationAlgo AllocationAlgoCorrect.
Require DVE EAE Alpha.
(* Require CopyPropagation ConstantPropagation ConstantPropagationAnalysis.*)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.
Require Import String ExtrOcamlString.

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


Definition toILF (ili:IL.stmt) : IL.stmt :=
  let lv := LivenessAnalysisCorrect.livenessAnalysis ili in
  let ilid := DVE.compile nil ili lv in
  let additional_params := additionalArguments ilid (DVE.compile_live ili lv ∅) in
  Delocation.compile nil ilid additional_params.

Arguments sim S {H} S' {H0} t _ _.


Lemma toILF_correct (ili:IL.stmt) s (E:onv val)
  : toILF ili = s
    -> defined_on (IL.freeVars ili) E
    -> sim I.state F.state Sim (nil, E, ili) (nil:list F.block, E, s).
Proof.
  intros. subst. unfold toILF.
  simpl in *; unfold ensure_f, additionalArguments in *.
  - assert (PM:LabelsDefined.paramsMatch ili nil) by admit.
    assert (LD:LabelsDefined.labelsDefined ili 0) by admit.
    eapply sim_trans with (S2:=I.state).
    eapply DVE.I.sim_DVE; [ reflexivity | eapply LivenessAnalysisCorrect.correct; eauto ].
    assert (Liveness.live_sound
              Liveness.Imperative nil nil
              (DVE.compile nil ili (LivenessAnalysisCorrect.livenessAnalysis ili))
              (DVE.compile_live ili (LivenessAnalysisCorrect.livenessAnalysis ili) {})). {
      eapply (@DVE.dve_live _ nil nil).
      eapply @LivenessAnalysisCorrect.correct; eauto.
    }
    assert (Delocation.trs
              nil nil
              (DVE.compile nil ili (LivenessAnalysisCorrect.livenessAnalysis ili))
              (DVE.compile_live ili (LivenessAnalysisCorrect.livenessAnalysis ili) {})
              (fst
                 (DelocationAlgo.computeParameters
                    nil nil nil
                    (DVE.compile nil ili (LivenessAnalysisCorrect.livenessAnalysis ili))
                    (DVE.compile_live ili (LivenessAnalysisCorrect.livenessAnalysis ili) {})))). {
      eapply DelocationAlgo.is_trs; eauto.

    }
    eapply sim_trans with (S2:=I.state).
    eapply BisimSim.bisim_sim'.
    eapply DelocationCorrect.correct; eauto.
    + eapply (@Delocation.live_sound_compile nil); eauto.
      eapply DelocationAlgo.is_live; eauto.
      admit.
    + hnf; intros. rewrite DVE.compile_live_incl_empty in H2;
                     [ | eapply LivenessAnalysisCorrect.correct; eauto].
      eapply H0. admit.
    + eapply BisimSim.bisim_sim'.
      eapply sim_sym.
      eapply (@Invariance.srdSim_sim nil nil nil nil nil);
        [ | isabsurd | econstructor | reflexivity | | econstructor ].
      eapply Delocation.trs_srd; eauto.
      eapply (@Delocation.live_sound_compile nil nil nil); eauto.
      eapply DelocationAlgo.is_live; eauto. admit.
Admitted.

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

Definition fromILF (s:stmt) : status stmt :=
  let s_hoisted := EAE.compile s in
  let s_renamed_apart := rename_apart s_hoisted in
  let fv := freeVars s_renamed_apart in
  sdo lv <- livenessAnalysis s_renamed_apart;
    if [Liveness.live_sound Liveness.FunctionalAndImperative nil s_renamed_apart lv
        /\ getAnn lv ⊆ freeVars s_hoisted] then
       let fvl := to_list (getAnn lv) in
       let ϱ := CMap.update_map_with_list fvl fvl (@MapInterface.empty var _ _ _) in
       sdo ϱ' <- AllocationAlgo.regAssign s_renamed_apart lv ϱ;
       let s_allocated := rename (CMap.findt ϱ' 0) s_renamed_apart in
       let s_lowered := ParallelMove.lower parallel_move
                                            nil
                                            s_allocated
                                            (mapAnn (map (CMap.findt ϱ' 0)) lv) in
       s_lowered
     else
       Error "Liveness unsound.".

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.


Lemma fromILF_correct (s s':stmt) E
  : fromILF s = Success s'
  -> sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros.
  monadS_inv H.
  cases in EQ0.
  monadS_inv EQ0; dcr.
  eapply sim_trans with (σ2:=(nil:list F.block, E, rename_apart (EAE.compile s))).
  eapply sim_trans with (σ2:=(nil:list F.block, E, EAE.compile s)).
  eapply bisim_sim. eapply EAE.sim_EAE.
  eapply bisim_sim.
  eapply (@Alpha.alphaSim_sim (nil, E, _) (nil, E, _)).
  econstructor; eauto using PIR2, Alpha.envCorr_idOn_refl.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.
  exploit rename_apart_renamedApart; eauto.
  exploit AllocationAlgoCorrect.regAssign_correct; eauto.
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

Print Assumptions toILF_correct.
Print Assumptions fromILF_correct.
(* Print Assumptions optimize_correct. *)


(* Unset Extraction AccessOpaque. *)


Extraction Inline bind Option.bind toString.

Extraction "extraction/lvc.ml" toILF fromILF AllocationAlgo.regAssign (* optimize *) toDeBruijn.
