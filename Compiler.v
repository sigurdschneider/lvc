Require Import List CSet.
Require Import Util AllInRel IL EnvTy RenameApart Sim Status Annotation.
Require Liveness LivenessValidators ParallelMove ILN LivenessAnalysis.
Require Coherence Delocation DelocationAlgo DelocationValidator Allocation AllocationAlgo.
Require CopyPropagation DVE.
Require ConstantPropagation ConstantPropagationAnalysis.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatBigInt.
Require Import String ExtrOcamlString.

Set Implicit Arguments.

Section Compiler.

Hypothesis allocation_oracle : stmt -> ann (set var) -> (var -> var) -> status (var -> var).
Hypothesis ssa_construction : stmt -> ann (option (set var)) * ann (list var).
Hypothesis parallel_move : var -> list var -> list var -> (list(list var * list var)).
Hypothesis first : forall (A:Type), A -> ( A -> status (A * bool)) -> status A.

Arguments first {A} _ _.

Definition livenessAnalysis :=
Analysis.fixpoint LivenessAnalysis.liveness_analysis first.

Definition constantPropagationAnalysis :=
Analysis.fixpoint ConstantPropagationAnalysis.constant_propagation_analysis first.


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

Definition ensure P `{Computable P} (s: string) : status unit :=
if [P] then Success tt else Error s.

Arguments ensure P [H] s.

Definition toILF (ilin:ILN.nstmt) : status IL.stmt :=
  sdo ili <- ILN.labIndices ilin nil;
  sdo lv <- livenessAnalysis ili;
  sdo _ <- ensure (Liveness.true_live_sound nil ili lv) "Liveness unsound";
  let ilid := DVE.compile nil ili lv in
  let additional_params := additionalArguments ilid (DVE.compile_live ili lv) in
  sdo _ <- ensure (Delocation.trs nil nil ilid (DVE.compile_live ili lv) additional_params) "Liveness unsound";
    Success (Delocation.compile nil ilid additional_params).


Definition optimize (s:stmt) : status stmt :=
  let s := rename_apart s in
  sdo ALAE <- constantPropagationAnalysis s;
  match ALAE with
    | (AL, Some AE) =>
      let s := ValueOpts.compile s
                                (ConstantPropagation.cp_choose
                                   (fun x => MapInterface.find x AE) s)
      in
      sdo lv <- livenessAnalysis s;
        Success (DVE.compile nil s lv)
    | _ => Error "Constant propagation returned bottom"
  end.
(*
Definition fromILF (s:stmt) : status stmt :=
  let s_renamed_apart := rename_apart s
  in let lv := livenessAnalysis s_renamed_apart in
     if [Liveness.live_sound nil s_renamed_apart lv
         /\ getAnn lv ⊆ freeVars s] then
       sdo ϱ <- allocation_oracle s_renamed_apart lv id;
       if [agree_on _eq (getAnn lv) ϱ id
           /\ Allocation.locally_inj ϱ s_renamed_apart lv ] then
         let s_allocated := rename ϱ s_renamed_apart in
         let s_lowered := ParallelMove.lower parallel_move nil s_allocated (mapAnn (lookup_set ϱ) lv) in
         s_lowered
       else
         Error "Register allocation not injective."
     else
       Error "Liveness unsound.".
*)
Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.

Lemma sim_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim σ1 σ2 -> sim σ2 σ3 -> sim σ1 σ3.
Proof.
  intros. eapply sim'_sim.
  refine (sim'_trans (sim_sim' H2) (sim_sim' H3)).
Qed.

Arguments sim_trans [S1] {H} σ1 [S2] {H0} σ2 [S3] {H1} σ3 _ _.

Lemma bisim_sim {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2)
  : Bisim.bisim σ1 σ2 -> Sim.sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1.
  - econstructor; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr. eexists; eauto.
    + intros. edestruct H7; eauto; dcr. eexists; eauto.
  - econstructor 4; eauto.
Qed.


Lemma toILF_correct ilin s (E:onv val)
  : toILF ilin = Success s
   -> @sim _ ILN.statetype_I _ _ (ILN.I.labenv_empty, E, ilin)
          (nil:list F.block, E, s).
Proof.
  intros. unfold toILF in H. simpl in *; unfold ensure, additionalArguments in *.
  monadS_inv H.
  destruct if in EQ2; isabsurd.
  destruct if in EQ0; isabsurd. clear x1 EQ0 EQ2 x2.
  eapply sim_trans with (S2:=I.state).
  - eapply bisim_sim. eapply ILN.labIndicesSim_sim.
    econstructor; eauto; isabsurd. econstructor; isabsurd.
  - case_eq (DelocationAlgo.computeParameters nil nil nil
              (DVE.compile nil x x0) (DVE.compile_live x x0)); intros.
    assert (l = nil). admit. subst. eauto.
    exploit (@DVE.dve_live nil); eauto.
    exploit Delocation.trs_srd; eauto using PIR2.
    exploit (@DelocationAlgo.computeParameters_live nil nil nil); eauto using PIR2.
    eapply sim_trans with (S2:=I.state). Focus 2.
    eapply bisim_sim. eapply Bisim.bisim_sym.
    rewrite H in X0.
    eapply Coherence.srdSim_sim; eauto.
    econstructor; eauto using AIR2. isabsurd. reflexivity.
    simpl. rewrite H in t.
    eapply (@Delocation.live_sound_compile nil nil nil); eauto.

    eapply sim_trans with (S2:=I.state).
    Focus 2.
    eapply bisim_sim. eapply Delocation.trsR_sim.
    rewrite H in t.
    econstructor; eauto using AIR53. reflexivity.
    eapply (@Delocation.live_sound_compile nil); eauto. admit.
    exfalso; admit.
Admitted.

(*
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
*)

Lemma optimize_correct (E:onv val) s s'
: optimize s = Success s'
  -> sim (nil:list F.block, E, s) (nil:list F.block, E, s').
Proof.
  intros.
  unfold optimize in H.
  (*
  eapply (@sim_trans F.state _ F.state _).
  instantiate (1:= (nil, E, DVE.compile s lv)).
  admit.
  eapply (@sim_trans F.state _ F.state _).
  eapply CopyPropagation.subst_id.
  eapply sim_sym.
  eapply CopyPropagation.sim_CP.
Qed.
*)
Admitted.

End Compiler.

(*Print Assumptions toILF_correct.
Print Assumptions fromILF_correct.*)

(* Unset Extraction AccessOpaque. *)

Extraction Inline bind Option.bind toString.

Extraction "extraction/lvc.ml" toILF AllocationAlgo.linear_scan optimize.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
