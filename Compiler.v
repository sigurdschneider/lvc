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

Definition ensure_f P `{Computable P} (s: string) {A} (cont:status A) : status A :=
if [P] then cont else Error s.

Arguments ensure_f P [H] s {A} cont.

Notation "'ensure' P s ; cont " := (ensure_f P s cont)
                                    (at level 20, P at level 0, s at level 0, cont at level 200, left associativity).

(* Print Grammar operconstr. *)

Definition toILF (ilin:ILN.nstmt) : status IL.stmt :=
  sdo ili <- ILN.labIndices ilin nil;
  sdo lv <- livenessAnalysis ili;
  ensure (Liveness.true_live_sound nil ili lv /\ getAnn lv ⊆ freeVars ili) ("Liveness unsound (1)") ;
  let ilid := DVE.compile nil ili lv in
  let additional_params := additionalArguments ilid (DVE.compile_live ili lv) in
  ensure (Delocation.trs nil nil ilid (DVE.compile_live ili lv) additional_params)
         "Additional arguments insufficient";
    Success (Delocation.compile nil ilid additional_params).



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
      let s := ValueOpts.compile s (ConstantPropagation.cp_choose AE s) in
      sdo lv <- livenessAnalysis s;
      ensure (Liveness.true_live_sound nil s lv) "Liveness unsound (2)";
      Success (DVE.compile nil s lv)
  end.


Definition fromILF (s:stmt) : status stmt :=
  let s_renamed_apart := rename_apart s in
  sdo lv <- livenessAnalysis s_renamed_apart;
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


Lemma toILF_correct (ilin:ILN.nstmt) s (E:onv val)
  : toILF ilin = Success s
    -> Delocation.defined_on (ILN.freeVars ilin) E
    -> @sim _ ILN.statetype_I _ _ (ILN.I.labenv_empty, E, ilin)
          (nil:list F.block, E, s).
Proof.
  intros. unfold toILF in H. simpl in *; unfold ensure_f, additionalArguments in *.
  monadS_inv H.
  repeat (destruct if in EQ2; [|isabsurd]).
  invc EQ2. dcr.
  eapply sim_trans with (S2:=I.state).
  - eapply bisim_sim. eapply ILN.labIndicesSim_sim.
    econstructor; eauto; isabsurd. econstructor; isabsurd.
  - case_eq (DelocationAlgo.computeParameters nil nil nil
              (DVE.compile nil x x0) (DVE.compile_live x x0)); intros.
    assert (l = nil). {
    exploit (DelocationAlgo.computeParameters_length nil nil); eauto.
    eapply (@DVE.dve_live nil); eauto. destruct l; simpl in *; congruence.
    }
    subst.
    exploit (@DVE.dve_live nil); eauto.
    exploit Delocation.trs_srd; eauto using PIR2.
    exploit (@DelocationAlgo.computeParameters_live nil nil nil); eauto using PIR2.
    eapply sim_trans with (S2:=I.state). Focus 2.
    eapply bisim_sim. eapply Bisim.bisim_sym.
    rewrite H2 in X0.
    eapply Coherence.srdSim_sim; eauto.
    econstructor; eauto using AIR2. isabsurd. reflexivity.
    simpl. rewrite H2 in t.
    eapply (@Delocation.live_sound_compile nil nil nil); eauto.

    eapply sim_trans with (S2:=I.state).
    Focus 2.
    eapply bisim_sim. eapply Delocation.trsR_sim.
    rewrite H2 in t.
    econstructor; eauto using AIR53. reflexivity.
    eapply (@Delocation.live_sound_compile nil); eauto.
    hnf; intros. rewrite DVE.compile_live_incl in H3. eapply H0; eauto.
    Lemma labIndices_freeVars ilin s L
    : ILN.labIndices ilin L = Success s
      -> ILN.freeVars ilin = freeVars s.
    Proof.
      intros. general induction ilin; simpl in *; monadS_inv H; simpl.
      - erewrite IHilin; eauto.
      - erewrite IHilin1, IHilin2; eauto.
      - reflexivity.
      - reflexivity.
      - erewrite IHilin; eauto.
      - erewrite IHilin1, IHilin2; try eapply EQ, EQ1; eauto.
    Qed.
    intros. erewrite labIndices_freeVars; eauto.
    eauto.
    eapply DVE.I.sim_DVE. reflexivity. eauto.
Qed.


Lemma fst_ssa_ann s G
 : fst (getAnn (ssa_ann s G)) = G.
Proof.
  general induction s; eauto.
Qed.

Lemma fromILF_correct (s s':stmt) E
  : fromILF s = Success s'
  -> sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros.
  monadS_inv H.
  destruct if in EQ0; dcr; isabsurd.
  monadS_inv EQ0; dcr. destruct if in EQ2; dcr.
  eapply sim_trans with (σ2:=(nil:list F.block, E, rename_apart s)).
  eapply bisim_sim.
  eapply (@Alpha.alphaSim_sim (nil, E, s) (nil, E, rename_apart s)).
  econstructor; eauto using AIR3, Alpha.envCorr_idOn_refl.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha.
  eapply sim_trans with (σ2:=(nil:list F.block, E,
    rename x0 (rename_apart s))).
  eapply bisim_sim.
  eapply Alpha.alphaSim_sim. econstructor; eauto using AIR3.
  eapply Allocation.ssa_locally_inj_alpha; eauto.
  eapply rename_apart_ssa; eauto; eapply lookup_set_on_id; try reflexivity.
  instantiate (1:=id).
  eapply (inverse_on_agree_on (inverse_on_id (G:=getAnn x))).
  symmetry; eauto. reflexivity.
  hnf; intros. cbv in H4; subst. rewrite H4; eauto.
  eapply sim_trans with (S2:=I.state).
  eapply bisim_sim.
  eapply Coherence.srdSim_sim.
  econstructor; isabsurd. eapply Allocation.rename_ssa_srd; eauto.
  eapply rename_apart_ssa; eauto. rewrite fst_ssa_ann; eauto.
  rewrite fst_ssa_ann; eauto.
  eapply I. econstructor. reflexivity.
  eapply (@Liveness.live_rename_sound nil); eauto.
  eapply (ParallelMove.pmSim_sim).
  econstructor; try now econstructor; eauto.
  eapply (@Liveness.live_rename_sound nil); eauto. eauto.
  congruence.
Qed.

Lemma labelsDefined_rename_apart L s ϱ G
: LabelsDefined.labelsDefined s L
  -> LabelsDefined.labelsDefined (snd (rename_apart' ϱ G s)) L.
Proof.
  intros.
  general induction H; simpl; repeat (let_pair_case_eq; simpl); try now econstructor; eauto; simpl_pair_eqs; instantiate; subst; eauto; subst.
  - subst. exploit IHlabelsDefined; eauto. econstructor. eapply X.
  - subst. econstructor.
    + eapply IHlabelsDefined1; eauto.
    + eapply IHlabelsDefined2; eauto.
  - subst. econstructor. eapply IHlabelsDefined; eauto.
  - subst. econstructor.
    + eapply IHlabelsDefined1; eauto.
    + eapply IHlabelsDefined2; eauto.
Qed.

Lemma optimize_correct (E:onv val) s s'
: optimize s = Success s'
  -> LabelsDefined.labelsDefined s 0
  -> sim (nil:list F.block, E, s) (nil:list F.block, E, s').
Proof.
  intros.
  unfold optimize, ensure_f in *.
  monadS_inv H. destruct x.
  repeat (destruct if in EQ0; [| isabsurd]).
  monadS_inv EQ0.
  repeat (destruct if in EQ2; [| isabsurd]).
  invc EQ2.

  eapply sim_trans with (S2:=F.state).
  eapply bisim_sim.
  eapply Alpha.alphaSim_sim. econstructor; eauto using rename_apart_alpha, AIR3.
  eapply Alpha.alpha_sym. eapply rename_apart_alpha. hnf; intros.
  cbv in H, H1. instantiate (1:=E). congruence.
  eapply sim_trans with (S2:=F.state).
  Focus 2.
  eapply DVE.sim_DVE; eauto. reflexivity.
  eapply sim'_sim.
  eapply ValueOpts.sim_vopt; eauto.
  Focus 2.
  eapply ConstantPropagation.cp_sound_eqn; eauto.
  eapply rename_apart_ssa. instantiate (1:=nil). simpl.
  eapply labelsDefined_rename_apart; eauto.
  intros; isabsurd.
  rewrite fst_ssa_ann.
  Lemma cp_eqns_no_assumption d G
  : (forall x : var,
      x \In G -> MapInterface.find x d = ⎣⎦)
     -> ConstantPropagation.cp_eqns (fun x0 : var => MapInterface.find x0 d)
        G [=] ∅.
  Proof.
    intros. revert H. pattern G. eapply set_induction.
    intros. eapply empty_is_empty_1 in H. rewrite H.
    reflexivity.
    intros. eapply Add_Equal in H1. rewrite H1.
    assert ({x; s} [=] {{x}} ∪ s) by (cset_tac; intuition).
    rewrite H3. rewrite ConstantPropagation.cp_eqns_union.
    rewrite ConstantPropagation.cp_eqns_single. unfold ConstantPropagation.cp_eqn.
    rewrite H2. rewrite H. cset_tac; intuition. intros; eapply H2.
    rewrite H1. cset_tac; intuition. rewrite H1. cset_tac; intuition.
  Qed.
  intros. hnf; intros.
  rewrite cp_eqns_no_assumption in H. cset_tac; intuition. eassumption.
  constructor.
  eapply rename_apart_ssa.
  rewrite fst_ssa_ann.
  rewrite cp_eqns_no_assumption. eapply incl_empty. eauto.
  hnf; intuition.
Qed.

End Compiler.

Print Assumptions toILF_correct.
Print Assumptions fromILF_correct.
Print Assumptions optimize_correct.


(* Unset Extraction AccessOpaque. *)


Extraction Inline bind Option.bind toString.

Extraction "extraction/lvc.ml" toILF AllocationAlgo.linear_scan optimize.



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
