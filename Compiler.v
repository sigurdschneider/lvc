Require Import List CSet.
Require Import Util AllInRel IL ILRaise EnvTy ParamsMatch RegAlloc RenameApart Sim Status.
Require Coherence ILIToILF Liveness ParallelMove ILN LivenessAnalysis CoherenceAlgo RegAllocAlgo.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlString.

Set Implicit Arguments.

Section Compiler.

Hypothesis allocation_oracle : stmt -> ann (set var) -> (var -> var) -> status (var -> var).
Hypothesis ssa_construction : stmt -> ann (option (set var)) * ann (list var).
Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).
Hypothesis first : ann (set var) -> ( ann (set var) -> ann (set var) * bool) -> ann (set var).

Definition livenessAnalysis (s:stmt) :=
@AbsInt.analysis (set var) Subset (@Subset_computable _ _ ) first _ _ _ LivenessAnalysis.liveness_analysis s.

Definition additionalArguments s lv :=
  fst (CoherenceAlgo.computeParameters nil nil s lv).

Definition toILF (ilin:ILN.nstmt) (lv:ann (set var)) : status IL.stmt :=
  sdo ili <- ILN.labIndices ilin nil; 
  if [Liveness.live_sound nil ili lv] then
    let additional_arguments := additionalArguments ili lv
    in if [ILIToILF.trs nil nil ili lv additional_arguments] then
         Success (ILIToILF.compile nil ili additional_arguments)
       else Error ("Additional Arguments insufficient")
    else Error ("Liveness unsound").


Definition fromILF (s:stmt) : status stmt :=
  let s_renamed_apart := rename_apart s
  in let lv := livenessAnalysis s_renamed_apart in
     if [Liveness.live_sound nil s_renamed_apart lv
         /\ getAnn lv ⊆ freeVars s] then
       sdo ϱ <- allocation_oracle s_renamed_apart lv id;
       if [agree_on (getAnn lv) ϱ id
           /\ locally_inj ϱ s_renamed_apart lv ] then
         let s_allocated := rename ϱ s_renamed_apart in
         let s_lowered := ParallelMove.lower parallel_move nil s_allocated (mapAnn (lookup_set ϱ) lv) in
         s_lowered
       else
         Error "Register allocation not injective."
     else
       Error "Liveness unsound.".
Lemma toILF_correct ilin alv s (E:env val)
  : toILF ilin alv = Success s
   -> @sim _ ILN.statetype_I _ _ (ILN.I.labenv_empty, E, ilin) 
          (nil:list F.block, E, s).
Proof.
  intros. unfold toILF in H; simpl in *.
  Opaque Liveness.live_sound_dec.
  Opaque ILIToILF.trs_dec.
  monadS_inv H.
  destruct if in EQ0.
  destruct if in EQ0; isabsurd. inv EQ0.
  refine (sim_trans (ILN.labIndicesSim_sim _) (sim_trans (ILIToILF.trsR_sim _) (sim_sym (Coherence.srdSim_sim _)))).
  econstructor; eauto; isabsurd. econstructor; isabsurd.
  econstructor; eauto using AIR4; eauto; try reflexivity; isabsurd.

  econstructor; eauto 30 using ILIToILF.compile_typed, agree_on_refl, AIR2, PIR2; isabsurd.
  eapply (@ILIToILF.live_sound_compile nil); eauto.
  isabsurd.
Qed.

Lemma fromILF_correct (s s':stmt) E
  : fromILF s = Success s' 
  -> sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros.
  destruct if in H; dcr; isabsurd.
  monadS_inv H; dcr. destruct if in EQ0.
  eapply sim_trans with (σ2:=(nil:list F.block, E, rename_apart s)). 
  eapply (@Alpha.alphaSim_sim (nil, E, s) (nil, E, rename_apart s)).
  econstructor; eauto using AIR3, Alpha.envCorr_idOn_refl. 
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.
  eapply sim_trans with (σ2:=(nil:list F.block, E, 
    rename x (rename_apart s))).
  eapply Alpha.alphaSim_sim. econstructor; eauto using AIR3.
  eapply ssa_locally_inj_alpha; eauto.
  eapply rename_apart_ssa; eauto; eapply lookup_set_on_id; try reflexivity.
  eapply a.
  instantiate (1:=id). destruct a. 
  eapply (@inverse_on_agree_on _ _ _ _ id x id id); try intuition.
  eapply inverse_on_id.
  hnf; intros. cbv in H2; subst. rewrite H2; eauto.
  refine (sim_trans (Coherence.srdSim_sim _) (ParallelMove.pmSim_sim _)).
  econstructor; isabsurd. eapply rename_ssa_srd; eauto.
  eapply rename_apart_ssa; eauto. eapply a.
  eapply I. econstructor. 
  eapply agree_on_refl.
  eapply (@Liveness.live_rename_sound nil); eauto.
  instantiate (1:=parallel_move). 
  econstructor; try eapply EQ0.
  eapply (@Liveness.live_rename_sound nil); eauto.
  constructor.
  reflexivity.
  congruence.
Qed.

End Compiler.

Print Assumptions toILF_correct. 
Print Assumptions fromILF_correct.
 
Extraction Inline bind Option.bind.

Extraction "extraction/lvc.ml" toILF fromILF ILN.labIndices RegAllocAlgo.linear_scan.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)
