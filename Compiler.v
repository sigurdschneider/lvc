Require Import List CSet.
Require Import Util AllInRel IL ILRaise EnvTy ParamsMatch RegAlloc RenameApart Sim.
Require Coherence ILIToILF Liveness ParallelMove ILN LivenessAnalysis CoherenceAlgo.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlString.

Set Implicit Arguments.

Section Compiler.

Hypothesis allocation_oracle : forall {s:stmt} {G G':set var}, Coherence.ssa G s G' -> var -> var.
Hypothesis ssa_construction : stmt -> ann (option (set var)) * ann (list var).
Hypothesis parallel_move : var -> list var -> list var -> option (list(list var * list var)).
Hypothesis first : ann (set var) -> ( ann (set var) -> ann (set var) * bool) -> ann (set var).

Definition livenessAnalysis (s:stmt) :=
@AbsInt.analysis (set var) Subset (@Subset_computable _ _ ) first _ _ _ LivenessAnalysis.liveness_analysis s.

Definition additionalArguments s lv :=
  fst (CoherenceAlgo.computeParameters nil nil s lv).

Definition toILF (ili:stmt) (lv:ann(set var)) : option IL.stmt :=
  if [Liveness.live_sound nil ili lv] then
    let additional_arguments := additionalArguments ili lv
    in if [ILIToILF.trs nil nil (freeVars ili) ili lv additional_arguments] then
         Some (ILIToILF.compile nil ili additional_arguments)
       else None
    else None.


Definition fromILF (s:stmt) : option stmt :=
  let s_renamed_apart := rename_apart s
  in let ϱ := allocation_oracle (rename_apart_ssa s)
     in let lv := livenessAnalysis s_renamed_apart
        in if [Liveness.live_sound nil s_renamed_apart lv
               /\ getAnn lv ⊆ freeVars s 
               /\ agree_on (getAnn lv) ϱ id
               /\ locally_inj ϱ s_renamed_apart lv ] then
             let s_allocated := rename ϱ s_renamed_apart in
             mdo s_lowered <- ParallelMove.lower parallel_move nil s_allocated (Liveness.live_rename ϱ lv) ;
             Some s_lowered
           else
             None.

Lemma toILF_correct ili s E
  : params_match (nil: list I.block) ili
   -> toILF ili = Some s
   -> sim (nil:list I.block, E, ili) (nil:list F.block, E, s).
Proof.
  intros. unfold toILF in H0. destruct (ssa_construction ili); intros. 
  destruct if in H0; isabsurd; monad_inv H0. 
  refine (sim_trans (ILIToILF.trsR_sim _) (sim_sym (Coherence.srdSim_sim _))).
  econstructor; eauto using AIR4; eauto; try reflexivity; isabsurd.
  econstructor; eauto 30 using ILIToILF.compile_typed, agree_on_refl, AIR2; isabsurd.
  split; isabsurd. 
  destruct H; eauto using (ILIToILF.compile_params_match t H).
Qed.

Lemma fromILF_correct (s s':stmt) E
  : params_match nil s
  -> fromILF s = Some s' 
  -> sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros. destruct if in H0; dcr; isabsurd.
  monad_inv H0; dcr.
  eapply sim_trans with (σ2:=(nil:list F.block, E, rename_apart s)). 
  eapply (@Alpha.alphaSim_sim (nil, E, s) (nil, E, rename_apart s)).
  econstructor; eauto using AIR3, Alpha.envCorr_idOn_refl. 
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.
  eapply sim_trans with (σ2:=(nil:list F.block, E, 
    rename (allocation_oracle (rename_apart_ssa s)) (rename_apart s))). 
  eapply Alpha.alphaSim_sim. econstructor; eauto using AIR3.
  eapply ssa_locally_inj_alpha; eauto.
  eapply rename_apart_ssa; eauto; eapply lookup_set_on_id; try reflexivity.
  instantiate (1:=id). eapply agree_on_inverse_on; eauto; intuition.
  split. simpl. eapply (rename_apart_parameters_match (L:=nil)); isabsurd; eauto.
  simpl. eapply H. isabsurd. 
  hnf; intros. cbv in H4; subst. rewrite H4; eauto.
  refine (sim_trans (Coherence.srdSim_sim _) (ParallelMove.pmSim_sim _)).
  econstructor; isabsurd. eapply rename_ssa_srd; eauto.
  eapply rename_apart_ssa; eauto.
  eapply I. econstructor. eapply rename_params_match with (L:=nil).
  eapply rename_apart_params_match; eauto.
  eapply agree_on_refl.
  econstructor; eauto using AIR3; isabsurd. 
  eapply (@Liveness.live_rename_sound nil); eauto. 
  reflexivity.
Qed.

End Compiler.

Print Assumptions toILF_correct. 
Print Assumptions fromILF_correct.
 
Extraction Inline bind Option.bind.

Extraction "extraction/lyn.ml" toILF fromILF ILN.labIndices.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)
