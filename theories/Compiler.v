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
Require Import DCVE.
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
   ->  @sim _ ILN.statetype_I _ _ bot3 Bisim
           (ILN.I.labenv_empty, E, ilin)
           (nil:list I.block, E, s).
Proof.
  intros. unfold toDeBruijn in H. simpl in *.
  eapply ILN_IL.labIndicesSim_sim.
  econstructor; eauto; isabsurd. econstructor; isabsurd. constructor.
Qed.

Arguments sim S {H} S' {H0} r t _ _.

Definition addParams (s:IL.stmt) (lv:ann (set var)) : IL.stmt :=
  let additional_params := additionalArguments s lv in
  Delocation.compile nil s additional_params.


Lemma addParams_correct (E:onv val) (ili:IL.stmt) lv
  : defined_on (getAnn lv) E
    -> Liveness.live_sound Liveness.Imperative nil nil ili lv
    -> LabelsDefined.noUnreachableCode LabelsDefined.isCalled ili
    -> sim I.state F.state bot3 Sim (nil, E, ili) (nil:list F.block, E, addParams ili lv).
Proof with eauto using DCVE_live, DCVE_noUC.
  intros. subst. unfold addParams.
  eapply sim_trans with (S2:=I.state).
  - eapply bisim_sim.
    eapply DelocationCorrect.correct; eauto.
    + eapply DelocationAlgo.is_trs; eauto...
    + eapply (@Delocation.live_sound_compile nil)...
      eapply DelocationAlgo.is_trs...
      eapply DelocationAlgo.is_live...
  - eapply bisim_sim.
    eapply bisim_sym.
    eapply (@Invariance.srdSim_sim nil nil nil nil nil);
      [ | isabsurd | econstructor | reflexivity | | econstructor ].
    + eapply Delocation.trs_srd; eauto.
      eapply DelocationAlgo.is_trs...
    + eapply (@Delocation.live_sound_compile nil nil nil)...
      eapply DelocationAlgo.is_trs...
      eapply DelocationAlgo.is_live...
Qed.

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

Require Import SimplSpill SpillSim DoSpill DoSpillRm Take Drop.
Require Import ReconstrLive ReconstrLiveSound.
Require Import RenameApart_Liveness.

Definition max := max.
Definition slot n x := x + n.

Inductive Slot (VD:set var) :=
  {
    Slot_slot :> var -> var;
    Slot_Disj : disj VD (map Slot_slot VD);
    Slot_Inj : injective_on VD Slot_slot
  }.

Hint Immediate Slot_Disj Slot_Inj.

Smpl Add
    match goal with
    | [ |- @Equivalence.equiv
            _
            (@_eq _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))
            (@OT_Equivalence _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))
            ?x ?y ] => hnf
    | [ H : @Equivalence.equiv
              _
              (@_eq _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))
              (@OT_Equivalence _ (@SOT_as_OT _ (@eq nat) nat_OrderedType))
              ?x ?y |- _ ] => hnf in H; clear_trivial_eqs
    end : cset.


Definition Slot_p (VD:set var) n (EQ:n = S (fold max VD 0)): Slot VD.
  refine (@Build_Slot VD (fun x => x + n) _ _).
  - hnf; intros. cset_tac.
    exploit Fresh.fresh_spec'; try eapply H; eauto.
    unfold max in H2. omega.
  - hnf; intros. cset_tac. omega.
Qed.

Definition spill (k:nat) (VD:set var) (slt:Slot VD)
           (s:stmt) (lv:ann (set var)) : stmt * ann (set var) :=
  let fvl := to_list (getAnn lv) in
  let (R,M) := (of_list (take k fvl), of_list (drop k fvl)) in
  let spl := @simplSpill k nil nil R M s lv in
  let s_spilled := do_spill slt s spl nil in
  let lv_spilled := reconstr_live nil nil ∅ s_spilled (do_spill_rm slt spl) in
  let s_fun := addParams s_spilled lv_spilled in
  (s_fun, lv_spilled).

Lemma of_list_drop_incl X `{OrderedType X} (n : nat) (L:list X)
  : of_list (drop n L) ⊆ of_list L.
Proof.
  general induction L; destruct n; simpl; eauto with cset.
  rewrite drop_nil; eauto.
Qed.

Lemma of_list_drop_elements_incl X `{OrderedType X} (n : nat) (s : set X)
  : of_list (drop n (elements s)) ⊆ s.
Proof.
  rewrite of_list_drop_incl.
  rewrite of_list_elements; eauto.
Qed.

Lemma disj_incl X `{OrderedType X} (D1 D1' D2 D2':set X)
  : disj D1' D2'
    -> D1 ⊆ D1'
    -> D2 ⊆ D2'
    -> disj D1 D2.
Proof.
  intros.
  eapply disj_1_incl. eapply disj_2_incl; eauto.
  eauto.
Qed.

Lemma get_InA_R X (R:X -> X -> Prop) `{Reflexive X R} (L:list X) n x
  :  Get.get L n x
     -> InA R x L.
Proof.
  revert_until X. clear.
  intros. general induction H0; eauto using InA.
Qed.

Lemma NoDupA_get_neq' X (R:X -> X -> Prop) `{Reflexive X R}
      `{Transitive X R}
      (L:list X) n x m y
  : NoDupA R L
    -> n < m
    -> Get.get L n x
    -> Get.get L m y
    -> ~ R x y.
Proof.
  revert_until X. clear.
  intros.
  general induction H3; invt NoDupA.
  inv H4; try omega.
  eapply get_InA_R in H10; eauto.
  - revert H0 H6 H10 ; clear.
    intros. general induction H10.
    + intro. eapply H6. econstructor; eauto.
    + intro. eapply IHInA; eauto.
  - inv H4; try omega.
    eapply IHget; try eapply H11; eauto; omega.
Qed.

Lemma NoDupA_get_neq X (R:X -> X -> Prop) `{Reflexive X R}
      `{Symmetric X R}
      `{Transitive X R}
      (L:list X) n x m y
  : NoDupA R L
    -> n <> m
    -> Get.get L n x
    -> Get.get L m y
    -> ~ R x y.
Proof.
  intros.
  decide (n < m).
  - eapply NoDupA_get_neq'; eauto.
  - assert (m < n) by omega.
    intro. symmetry in H7.
    eapply NoDupA_get_neq'; eauto.
Qed.

Lemma defined_on_update_list_disj X `{OrderedType X} Y lv (E: X -> option Y) (Z:list X) vl
: defined_on lv E
  -> disj (of_list Z) lv
  -> defined_on lv (E [Z <-- vl]).
Proof.
  revert_until toString_list. clear.
  unfold defined_on; intros.
  general induction Z; destruct vl; simpl in *; eauto.
  - lud.
    + exfalso. eapply H1; eauto. simpl. cset_tac.
    + eapply IHZ; eauto with cset.
Qed.

Lemma agree_on_update_list_slot X `{OrderedType X} Y (L:list X) (L':list Y) (V:X->Y)
      `{Proper _ (_eq ==> eq) V} f `{Proper _ (_eq ==> _eq) f} V' D (Len:❬L❭= ❬L'❭)
  :  agree_on eq (D \ of_list L) V (fun x => V' (f x))
     -> lookup_list V L = L'
     -> injective_on (D ∪ of_list L) f
     -> agree_on eq D V (fun x => V'[f ⊝ L <-- L'] (f x)).
Proof.
  revert_until toString_list. clear.
  intros. hnf; intros.
  decide (x ∈ of_list L).
  - assert (In:f x ∈ of_list (f ⊝ L)).
    rewrite of_list_map; eauto. cset_tac.
    subst.
    edestruct update_with_list_lookup_in_list; try eapply In; dcr.
    Focus 2. rewrite H8. rewrite lookup_list_map in H7. inv_get.
    eapply H4 in H10; eauto with cset.
    eapply get_in_of_list in H7. cset_tac. eauto with len.
  - rewrite lookup_set_update_not_in_Z; eauto.
    eapply H2; cset_tac. rewrite of_list_map; eauto. cset_tac.
    eapply H4 in H8; eauto; cset_tac.
Qed.

Lemma spill_correct k (kGT:k > 0) (s:stmt) lv ra E
      (PM:LabelsDefined.paramsMatch s nil)
      (LV:Liveness.live_sound Liveness.Imperative nil nil s lv)
      (AEF:AppExpFree.app_expfree s)
      (RA:RenamedApart.renamedApart s ra)
      (Def:defined_on (getAnn lv) E)
      (Bnd:Spilling.fv_e_bounded k s)
      (Incl:getAnn lv ⊆ fst (getAnn ra))
      (NUC:LabelsDefined.noUnreachableCode LabelsDefined.isCalled s)
      (slt:Slot (fst (getAnn ra) ∪ snd (getAnn ra)))
      (aIncl:ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) lv ra)
  : sim I.state F.state bot3 Sim
        (nil, E, s)
        (nil, E [slt ⊝ drop k (to_list (getAnn lv)) <-- lookup_list E (drop k (to_list (getAnn lv)))], fst (spill k slt s lv )).
Proof.
  unfold spill.
  set (R:=of_list (take k (to_list (getAnn lv)))).
  set (M:=of_list (drop k (to_list (getAnn lv)))).
  set (spl:=(simplSpill k nil nil R M s lv)).
  set (VD:=fst (getAnn ra) ∪ snd (getAnn ra)).
  assert (lvRM:getAnn lv [=] R ∪ M). {
    subst R M. rewrite <- of_list_app. rewrite <- take_eta.
    rewrite of_list_3. eauto.
  }
  assert (SPS:Spilling.spill_sound k nil nil (R, M) s spl). {
    eapply simplSpill_sat_spillSound; eauto using PIR2.
    subst R. rewrite TakeSet.take_of_list_cardinal; eauto.
    rewrite lvRM; eauto.
  }
  assert (Disj: disj R M). {
    subst R M. clear. hnf; intros.
    eapply of_list_get_first in H; dcr; cset_tac.
    eapply of_list_get_first in H0; dcr; cset_tac.
    inv_get.
    refine (NoDupA_get_neq' _ _ H0 H _); eauto.
    eapply (elements_3w (getAnn lv)).
    omega.
  }
  assert (InclR: R ⊆ VD). {
    subst R VD. unfold to_list.
    rewrite TakeSet.take_set_incl. eauto with cset.
  }
  assert (InclM: M ⊆ VD). {
    subst M VD. unfold to_list.
    rewrite of_list_drop_elements_incl. eauto with cset.
  }
  assert (DefRM:defined_on (R ∪ map slt M)
                           (E [slt ⊝ drop k (elements (getAnn lv)) <--
                                   lookup_list E (drop k (elements (getAnn lv)))])).   {
    subst R M.
    eapply defined_on_union.
    - eapply defined_on_update_list_disj; eauto with len.
      eapply defined_on_incl; eauto.
      eapply TakeSet.take_set_incl.
      unfold to_list. rewrite TakeSet.take_set_incl.
      rewrite of_list_map; eauto. symmetry.
      eapply disj_incl; [ eapply (Slot_Disj slt); eauto | |]; eauto with cset.
    - eapply defined_on_update_list'; eauto with len.
      rewrite of_list_map; eauto. clear; hnf; intros. exfalso; cset_tac.
      rewrite lookup_list_map; eauto.
      rewrite <- defined_on_defined.
      eapply defined_on_incl; eauto.
      rewrite of_list_drop_elements_incl; eauto.
      clear; intuition.
  }
  eapply sim_trans with (S2:=I.state).
  - eapply sim_I with (slot:=slt) (k:=k) (R:=R) (M:=M) (sl:=spl) (Λ:=nil)
      (VD:=VD)
      (V':=E [slt ⊝ drop k (elements (getAnn lv)) <-- lookup_list E (drop k (elements (getAnn lv)))]);
      eauto.
    + eapply agree_on_update_list_dead; eauto.
      rewrite of_list_map. symmetry.
      eapply disj_incl; [ eapply (Slot_Disj slt); eauto | subst R |].
      * unfold to_list.
        rewrite TakeSet.take_set_incl. eauto with cset.
      * rewrite of_list_drop_elements_incl, Incl.
        eauto with cset.
      * eauto.
    + subst M.
      eapply agree_on_update_list_slot; try eassumption.
      clear; intuition. clear; intuition.
      eauto with len.
      eapply agree_on_empty; clear; cset_tac.
      reflexivity.
      eapply injective_on_incl; eauto.
      unfold to_list.
      rewrite of_list_drop_elements_incl. cset_tac.
    + admit.
    + rewrite <- Incl, lvRM; eauto.
    + eapply SimI.labenv_sim_nil.
    + eauto.
  - eapply addParams_correct; eauto.
    + rewrite (@ReconstrLiveSmall.reconstr_live_small nil nil nil s _ R M VD); eauto.
      * rewrite union_comm, empty_neutral_union. eauto.
      * reflexivity.
      * isabsurd.
      * admit.
    + eapply (@reconstr_live_sound k slt nil _ nil R M VD); eauto using PIR2.
      ** reflexivity.
      ** admit.
      ** isabsurd.
    + eapply (@do_spill_no_unreachable_code _ _ _ nil nil); eauto.
Admitted.


Definition fromILF (k:nat) (s:stmt) : status stmt :=
  let s_eae := EAE.compile s in
  let s_ra := rename_apart s_eae in
  let (s_dcve, lv) := DCVE Liveness.Imperative s_ra in
  let fvl := to_list (getAnn lv) in
  let s_ren := rename_apart s_fun in
  let lv_ren := snd (renameApart_live id (freeVars s_fun) s_fun lv_spilled) in
  let fvl := to_list (getAnn lv_ren) in
  let ϱ := CMap.update_map_with_list fvl fvl (@MapInterface.empty var _ _ _) in
  sdo ϱ' <- AllocationAlgo.regAssign s_ren lv_ren ϱ;
    let s_allocated := rename (CMap.findt ϱ' 0) s_ren in
    let s_lowered := ParallelMove.lower parallel_move
                                       nil
                                       s_allocated
                                       (mapAnn (map (CMap.findt ϱ' 0)) lv_ren) in
    s_lowered.

Opaque LivenessValidators.live_sound_dec.
Opaque DelocationValidator.trs_dec.


Lemma fromILF_correct k (s s':stmt) E (PM:LabelsDefined.paramsMatch s nil)
  : fromILF k s = Success s'
    -> sim F.state I.state bot3 Sim (nil:list F.block, E, s) (nil:list I.block, E, s').
Proof.
  unfold fromILF; intros.
  repeat let_case_eq; repeat simpl_pair_eqs; subst.
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
