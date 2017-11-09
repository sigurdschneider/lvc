Require Import compcert.lib.Coqlib compcert.common.Errors.
Require Import compcert.common.Linking compcert.common.Smallstep.
Require Import compcert.driver.Compiler.

Definition transf_linear_program (f: Linear.program) : res Asm.program :=
   OK f
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Local Open Scope linking_scope.

Definition my_passes :=
  mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Linear.program -> Asm.program -> Prop :=
  pass_match (compose_passes my_passes).

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_linear_program_match:
  forall p tp,
  transf_linear_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_linear_program, time in T. simpl in T.
  set (p18 := CleanupLabels.transf_program p) in *.
  destruct (partial_if Compopts.debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.


Lemma semantics_strongly_receptive:
  forall p, strongly_receptive (Linear.semantics p).
Proof.
  intros. constructor; simpl; intros.
  - (* receptiveness *)
    set (ge := Globalenvs.Genv.globalenv p) in *.
    inversion H; subst.
    + exploit Events.ec_trace_length; eauto.
      eapply Events.external_call_spec. destruct t1; eauto; simpl in *; try omega; intros.
      eapply Events.external_call_receptive with (t2:=ev2::nil) in H2; eauto.
      destruct H2 as [? [? ?]].
      do 2 eexists; econstructor; eauto.
    + exploit Events.ec_trace_length; eauto.
      eapply Events.external_call_spec. destruct t1; eauto; simpl in *; try omega; intros.
      eapply Events.external_call_receptive with (t2:=ev2::nil) in H2; eauto.
      destruct H2 as [? [? ?]].
      do 2 eexists; econstructor; eauto.
  - hnf; intros. inv H; simpl; eauto.
    + destruct t; eauto.
      assert (t = nil). {
        exploit Events.ec_trace_length; eauto.
        eapply Events.external_call_spec.
        destruct t; simpl in *; try omega; intros; eauto.
      } subst. simpl; eauto.
    + destruct t; eauto.
      assert (t = nil). {
        exploit Events.ec_trace_length; eauto.
        eapply Events.external_call_spec.
        destruct t; simpl in *; try omega; intros; eauto.
      } subst. simpl; eauto.
Qed.

(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)


Theorem linear_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Linear.semantics p) (Asm.semantics tp)
  /\ backward_simulation (atomic (Linear.semantics p)) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Linear.semantics p) (Asm.semantics p4)).
  {
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply Asmgenproof.transf_program_correct; eassumption.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.


Lemma linear_single_events p
  :  single_events (Linear.semantics p).
Proof.
  hnf; intros. inv H; simpl; try omega.
  - exploit Events.ec_trace_length; eauto.
    eapply Events.external_call_spec.
  - exploit Events.ec_trace_length; eauto.
    eapply Events.external_call_spec.
Qed.


Remark backward_simulation_identity p :
  backward_simulation (Linear.semantics p) (Linear.semantics p).
Proof.
  intros.
  eapply (Backward_simulation (fun (x y:unit) => False) (fun x => eq)).
  econstructor.
  - hnf; intros. econstructor. firstorder.
  - eauto.
  - firstorder. econstructor.
  - intros. subst. eexists; split; eauto. econstructor.
  - intros. subst. unfold final_state; simpl.
    hnf in s2. hnf in H0.
    eapply H0. constructor 1.
  - intros. subst. do 2 eexists; split; eauto. left. econstructor; eauto.
    econstructor. rewrite Events.E0_right. reflexivity.
  - intros. reflexivity.
Qed.

Theorem linear_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Linear.semantics p) (Asm.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Linear.semantics p)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + eapply backward_simulation_identity.
    + eapply linear_single_events.
    + eapply ssr_well_behaved; eapply semantics_strongly_receptive.
  - eapply linear_semantic_preservation; eauto.
Qed.

(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_linear_program_correct:
  forall p tp,
  transf_linear_program p = OK tp ->
  backward_simulation (Linear.semantics p) (Asm.semantics tp).
Proof.
  intros. apply linear_preservation. apply transf_linear_program_match; auto.
Qed.

(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_linear_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Linear.semantics c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_linear_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply linear_preservation; auto.
Qed.
