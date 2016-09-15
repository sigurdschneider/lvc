Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness.

Set Implicit Arguments.
Unset Printing Records.

Definition filter (Z:params) (lv:set var) := List.filter (fun x => B[x ∈ lv]) Z.

Fixpoint compile (LV:list ((set var) * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtLet x e s, ann1 _ an =>
      if [x ∈ getAnn an \/ isCall e]
      then stmtLet x e (compile LV s an)
      else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [op2bool e = Some true] then
        (compile LV s ans)
      else if [ op2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtApp f Y, ann0 _ =>
      let lvZ := nth (counted f) LV (∅, nil) in
      stmtApp f (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (zip (fun Zs a => (filter (fst Zs) (getAnn a), compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.

Lemma getAnn_eq X Y Y' (F:list (Y * Y')) (als:list (ann X))
  : ❬F❭ = ❬als❭
    -> getAnn ⊝ als = fst ⊝ pair ⊜ (getAnn ⊝ als) (fst ⊝ F).
Proof.
  intros LEN.
  rewrite map_zip.
  rewrite zip_map_fst; eauto with len.
Qed.

Lemma getAnn_take_eq X Y Y' (F:list (Y * Y')) (als:list (ann X)) k a LV
  : ❬F❭ = ❬als❭
    -> get als k a
    -> getAnn ⊝ take k als = fst ⊝ take k (pair ⊜ (getAnn ⊝ als) (fst ⊝ F) ++ LV).
Proof.
  intros LEN Get.
  rewrite take_app_lt; eauto with len.
  repeat rewrite map_take.
  rewrite map_zip.
  rewrite zip_map_fst; eauto with len.
Qed.


Fixpoint compile_live (s:stmt) (a:ann (set var)) (G:set var) : ann (set var) :=
  match s, a with
    | stmtLet x e s, ann1 lv an as a =>
      if [x ∈ getAnn an \/ isCall e] then ann1 (G ∪ lv) (compile_live s an {x})
                         else compile_live s an G
    | stmtIf e s t, ann2 lv ans ant =>
      if [op2bool e = Some true] then
        compile_live s ans G
      else if [op2bool e = Some false ] then
        compile_live t ant G
      else
        ann2 (G ∪ lv) (compile_live s ans ∅) (compile_live t ant ∅)
    | stmtApp f Y, ann0 lv => ann0 (G ∪ lv)
    | stmtReturn x, ann0 lv => ann0 (G ∪ lv)
    | stmtFun F t, annF lv ans ant =>
      let ans' := zip (fun Zs a => let a' := compile_live (snd Zs) a ∅ in
                               setTopAnn a' (getAnn a' ∪ of_list (filter (fst Zs) (getAnn a)))) F ans
      in annF (G ∪ lv) ans' (compile_live t ant ∅)
    | _, a => a
  end.


Lemma compile_live_incl G i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> getAnn (compile_live s lv G) ⊆ G ∪ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity.
    + etransitivity; eauto. rewrite H4; eauto.
    + etransitivity; eauto. rewrite <- H5; eauto.
Qed.

Lemma compile_live_incl_empty i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> getAnn (compile_live s lv ∅) ⊆ getAnn lv.
Proof.
  intros.
  eapply compile_live_incl in H.
  rewrite H. cset_tac; intuition.
Qed.

Lemma incl_compile_live G i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> G ⊆ getAnn (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; eauto with cset.
  - repeat cases; simpl; eauto.
Qed.

Lemma dve_live i ZL LV s lv G
  : true_live_sound i ZL LV s lv
    -> live_sound i (filter ⊜ ZL LV) LV (compile (zip pair LV ZL) s lv) (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - cases; eauto. econstructor; eauto.
    + eapply live_exp_sound_incl; eauto.
    + rewrite compile_live_incl; eauto.
      rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - repeat cases; eauto.
    + econstructor; eauto.
      eapply live_op_sound_incl; eauto.
      rewrite compile_live_incl_empty; eauto with cset.
      rewrite compile_live_incl_empty; eauto with cset.
  - econstructor; eauto using zip_get.
    + simpl. cases; eauto.
      rewrite <- H1. rewrite minus_inter_empty. eapply incl_right.
      unfold filter. rewrite of_list_filter.
      cset_tac; intuition.
    + erewrite get_nth; eauto using zip_get.
      simpl. eauto with len.
    + intros ? ? Get. erewrite get_nth in Get; eauto using zip_get. simpl in *.
      edestruct filter_by_get as [? [? []]]; eauto; dcr. simpl in *; cases in H6.
      eapply live_op_sound_incl.
      eapply argsLive_live_exp_sound; eauto. eauto with cset.
  - econstructor; eauto.
    eapply live_op_sound_incl; eauto using incl_right.
  - econstructor; simpl in *; eauto with len.
    + eapply live_sound_monotone.
      rewrite map_zip. simpl.
      do 2 rewrite zip_app in IHtrue_live_sound; eauto with len.
      rewrite zip_map_l, zip_map_r in IHtrue_live_sound.
      eapply IHtrue_live_sound.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. unfold filter.
      rewrite of_list_filter. cset_tac.
    + intros; inv_get. simpl.
      eapply live_sound_monotone.
      eapply live_sound_monotone2; eauto.
      rewrite map_zip. simpl.
      do 2 rewrite zip_app in H2; eauto with len.
      rewrite zip_map_l, zip_map_r in H2.
      eapply H2; eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto.
      unfold filter. rewrite of_list_filter. cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      unfold filter. rewrite of_list_filter. clear_all; cset_tac.
    + rewrite compile_live_incl; eauto with cset.
Qed.

Lemma DVE_callChain Lv ZL F als n l'
  : ❬F❭ = ❬als❭
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
         get F n Zs ->
         get als n a ->
         forall n0 : nat,
           trueIsCalled (snd Zs) (LabI n0) ->
           trueIsCalled (compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd Zs) a) (LabI n0))
     -> callChain trueIsCalled F (LabI l') (LabI n)
     -> callChain trueIsCalled
                 ((fun (Zs : params * stmt) (a : ann ⦃var⦄) =>
                     (filter (fst Zs) (getAnn a),
                      compile (pair ⊜ (getAnn ⊝ als ++ Lv) (fst ⊝ F ++ ZL)) (snd Zs) a)) ⊜ F als)
                 (LabI l') (LabI n).
Proof.
  intros LEN IH CC.
  general induction CC.
  + econstructor.
  + inv_get. econstructor 2.
    eapply zip_get; eauto.
    eapply IH; eauto.
    eauto.
Qed.

Lemma DVE_isCalled i ZL LV s lv n
  : true_live_sound i ZL LV s lv
    -> trueIsCalled s (LabI n)
    -> trueIsCalled (compile (zip pair LV ZL) s lv) (LabI n).
Proof.
  intros LS IC.
  general induction LS; invt trueIsCalled; simpl; repeat cases; eauto using trueIsCalled;
    try congruence.
  - destruct l' as [l'].
    econstructor; rewrite <- zip_app; eauto with len.
    rewrite zip_length2; eauto. eapply DVE_callChain; eauto.
Qed.

Lemma DVE_noUnreachableCode i ZL LV s lv
  : true_live_sound i ZL LV s lv
    -> noUnreachableCode trueIsCalled s
    -> noUnreachableCode trueIsCalled (compile (zip pair LV ZL) s lv).
Proof.
  intros LS UC.
  general induction LS; inv UC; simpl; repeat cases; eauto using noUnreachableCode.
  - econstructor; intros; inv_get; rewrite <- zip_app; simpl; eauto with len.
    + edestruct H8 as [[l] [IC CC]]. rewrite zip_length2 in H4; eauto.
      eexists (LabI l); split; eauto.
      eapply DVE_isCalled; eauto.
      eapply DVE_callChain; eauto using DVE_isCalled.
Qed.

Require Import BisimSim.

Module I.

  Require Import SimI.


Instance SR : PointwiseProofRelationI ((set var) * params) := {
   ParamRelIP G Z Z' := Z' = (List.filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRelIP V V' G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL /\
     agree_on eq (fst G \ of_list (snd G)) V V';
}.

Lemma sim_I ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative ZL LV s lv
-> labenv_sim Sim (sim'r r) SR (zip pair LV ZL) L L'
-> sim'r r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - destruct e.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_op il_statetype_I);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H10. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_I); intros; eauto 20 using op_eval_live, agree_on_incl.
  - eapply labenv_sim_app; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z0 H7);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros. eapply argsLive_liveSound; eauto.
        erewrite get_nth; eauto using zip_get; simpl.
        rewrite H12. eexists; split; eauto.
        repeat split; eauto using filter_filter_by_length.
        eapply agree_on_incl; eauto.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_fun_ptw; eauto.
    + intros. left. rewrite <- zip_app; eauto with len. eapply IH; eauto using agree_on_incl.
    + intros. hnf; intros; simpl in *; dcr; subst.
      inv_get.
      rewrite <- zip_app; eauto with len.
      eapply IH; eauto.
      eapply agree_on_update_filter'; eauto.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative nil nil s lv
-> @sim I.state _ I.state _ Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_I nil nil); eauto.
  eapply labenv_sim_nil.
Qed.

End I.

Module F.

  Require Import SimF.

Instance SR : PointwiseProofRelationF ((set var) * params) := {
   ParamRelFP G Z Z' := Z' = (List.filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRelFP G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL
}.

Lemma sim_F ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional ZL LV s lv
-> labenv_sim Sim (sim'r r) SR (zip pair LV ZL) L L'
-> sim'r r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim'r. revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - destruct e.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_op il_statetype_F);
          eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
      * case_eq (op_eval V e); intros.
        -- pone_step_left.
           eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
           eapply agree_on_incl; eauto.
           rewrite <- H10. cset_tac; intuition.
        -- pno_step_left.
    + cases. exploit H9; eauto. inv H2.
      * eapply (sim_let_call il_statetype_F); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_if_elim il_statetype_F); intros; eauto 20 using op_eval_live, agree_on_incl.
  - eapply labenv_sim_app; eauto using zip_get.
    + intros; simpl in *; dcr; subst.
      split; [|split]; intros.
      * exploit (@omap_filter_by _ _ _ _ (fun y : var => if [y \In blv] then true else false) _ _ Z0 H7);
          eauto.
        exploit omap_op_eval_live_agree; eauto.
        intros. eapply argsLive_liveSound; eauto.
        erewrite get_nth; eauto using zip_get; simpl.
        rewrite H12. eexists; split; eauto.
        repeat split; eauto using filter_filter_by_length.
  - pno_step.
    simpl. erewrite <- op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply sim_fun_ptw; eauto.
    + intros. left. rewrite <- zip_app; eauto with len. eapply IH; eauto using agree_on_incl.
    + intros. hnf; intros; simpl in *; dcr; subst.
      inv_get.
      rewrite <- zip_app; eauto with len.
      eapply IH; eauto. simpl in *.
      exploit H9; eauto.
      eapply agree_on_update_filter'; eauto using agree_on_incl.
    + hnf; intros; simpl in *; subst.
      inv_get; simpl; eauto.
    + eauto with len.
    + eauto with len.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional nil nil s lv
-> @sim F.state _ F.state _ Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply (@sim_F nil nil); eauto. eapply labenv_sim_nil.
Qed.

End F.