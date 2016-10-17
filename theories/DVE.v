Require Import CSet Util Fresh Filter Take MoreList OUnion AllInRel.
Require Import IL Annotation LabelsDefined Sawtooth InRel Liveness TrueLiveness.

Set Implicit Arguments.
Unset Printing Records.

(** * Dead Variable Elimination *)

Definition filter_set (Z:params) (lv:set var) := List.filter (fun x => B[x ∈ lv]) Z.

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
      stmtFun (zip (fun Zs a => (filter_set (fst Zs) (getAnn a), compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.


(** ** Correctness with respect to the imperative semantics IL/I *)

Module I.

  Require Import SimI.


Instance SR : PointwiseProofRelationI ((set var) * params) := {
   ParamRelIP G Z Z' := Z' = (filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRelIP V V' G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL /\
     agree_on eq (fst G \ of_list (snd G)) V V';
}.

Lemma sim_I ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative ZL LV s lv
-> labenv_sim Sim (sim r) SR (zip pair LV ZL) L L'
-> sim r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim. revert_except s.
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
-> @sim I.state _ I.state _ bot3 Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros.
  eapply (@sim_I nil nil); eauto.
  eapply labenv_sim_nil.
Qed.

End I.

(** ** Correctness with respect to the functional semantics IL *)
(** Functional here means that variables are lexically scoped binders instead of assignables. *)

Module F.

  Require Import SimF.

Instance SR : PointwiseProofRelationF ((set var) * params) := {
   ParamRelFP G Z Z' := Z' = (filter (fun x => B[x ∈ fst G]) Z) /\ snd G = Z;
   ArgRelFP G VL VL' :=
     VL' = (filter_by (fun x => B[x ∈ fst G]) (snd G) VL) /\
     length (snd G) = length VL
}.

Lemma sim_F ZL LV r L L' V V' s  lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional ZL LV s lv
-> labenv_sim Sim (sim r) SR (zip pair LV ZL) L L'
-> sim r Sim (L,V, s) (L',V', compile (zip pair LV ZL) s lv).
Proof.
  unfold sim. revert_except s.
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
-> @sim F.state _ F.state _ bot3 Sim (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros.
  eapply (@sim_F nil nil); eauto. eapply labenv_sim_nil.
Qed.

End F.


(** ** Reconstruction of Liveness Information after DVE *)
(** In this section we show that liveness information can
    be transformed alongside DVE.
    This means that liveness recomputation after the transformation is not neccessary. *)


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
                               setTopAnn a' (getAnn a' ∪ of_list (filter_set (fst Zs) (getAnn a)))) F ans
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
    -> live_sound i (filter_set ⊜ ZL LV) LV (compile (zip pair LV ZL) s lv) (compile_live s lv G).
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
      unfold filter_set. rewrite of_list_filter.
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
      rewrite compile_live_incl_empty; eauto. unfold filter_set.
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
      unfold filter_set. rewrite of_list_filter. cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      unfold filter_set. rewrite of_list_filter. clear_all; cset_tac.
    + rewrite compile_live_incl; eauto with cset.
Qed.

(** ** DVE and Unreachable Code *)
(** We show that DVE does not introduce unreachable code. *)

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
                     (filter_set (fst Zs) (getAnn a),
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

Require Import AppExpFree.

Lemma DVE_app_expfree LVZL s lv
: app_expfree s
  -> app_expfree (compile LVZL s lv).
Proof.
  intros AEF.
  general induction AEF; destruct lv; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      repeat cases; eauto using app_expfree.
  - econstructor. intros; inv_get.
    edestruct filter_by_get; eauto; dcr.
    cases in H4. exploit H1; eauto.
  - econstructor; intros; inv_get; eauto.
    eapply H0; eauto.
Qed.

Require Import RenamedApart PE.

Fixpoint compile_renamedApart (s:stmt) (lv:ann (set var)) (a:ann (set var * set var)) (D:set var)
  : ann (set var * set var) :=
  match s, lv, a with
  | stmtLet x e s, ann1 lv alv, ann1 (_, _) an as a =>

    if [x ∈ getAnn alv \/ isCall e] then
      let an' := compile_renamedApart s alv an {x;D} in
      ann1 (D, {x;snd (getAnn an')}) an'
    else compile_renamedApart s alv an D
  | stmtIf e s t, ann2 lv ans ant, ann2 (_,_) bns bnt =>
    let bns' := compile_renamedApart s ans bns D in
    let bnt' := compile_renamedApart t ant bnt D in
      if [op2bool e = Some true] then bns'
      else if [op2bool e = Some false ] then bnt'
           else ann2 (D,
                      snd (getAnn bns') ∪ snd (getAnn bnt'))
                     bns' bnt'
    | stmtApp f Y, ann0 lv, ann0 _ => ann0 (D, ∅)
    | stmtReturn x, ann0 lv, ann0 _ => ann0 (D, ∅)
    | stmtFun F t, annF lv anF ant, annF (_, _) bnF bnt =>
      let abnF := (pair ⊜ anF bnF) in
      let bnF' := zip (fun (Zs:params * stmt) ab =>
                        compile_renamedApart (snd Zs) (fst ab) (snd ab) (of_list (filter_set (fst Zs) (getAnn (fst ab))) ∪ D)) F abnF in
      let abnF' := (pair ⊜ anF bnF') in
      let bnt' := compile_renamedApart t ant bnt D in
      annF (D, list_union ((fun Zs ab => of_list (filter_set (fst Zs) (getAnn (fst ab))) ∪ snd (getAnn (snd ab))) ⊜ F abnF')
                          ∪ snd (getAnn bnt'))
           bnF' bnt'
    | _, _, a => a
  end.

Lemma fst_getAnn_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> fst (getAnn (compile_renamedApart s lv G D)) = D.
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; eauto.
Qed.

Lemma fst_getAnn_renamedApart' i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> fst (getAnn (compile_renamedApart s lv G D)) [=] D.
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; eauto.
Qed.

Hint Resolve fst_getAnn_renamedApart fst_getAnn_renamedApart'.

Lemma snd_getAnn_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> snd (getAnn (compile_renamedApart s lv G D)) ⊆ snd (getAnn G).
Proof.
  intros RA TLS.
  general induction TLS; invt renamedApart; simpl; repeat cases; simpl; srewrite D'; eauto.
  - rewrite IHTLS; eauto. rewrite H9; eauto.
  - rewrite IHTLS; eauto. rewrite H9; eauto with cset.
  - rewrite H0; eauto. rewrite H15; eauto with cset.
  - rewrite H2; eauto. rewrite H16; eauto with cset.
  - rewrite H0, H2; eauto. rewrite H15, H16; eauto.
  - rewrite IHTLS, H11; eauto.
    eapply incl_union_lr; eauto.
    eapply list_union_incl; intros; inv_get; simpl.
    eapply incl_list_union; eauto using zip_get.
    rewrite H1; eauto.
    unfold defVars, filter_set; rewrite of_list_filter; simpl.
    clear. cset_tac. cset_tac.
Qed.

Lemma unique_filter X p (L:list X)
  : unique L
    -> unique (filter p L).
Proof.
  general induction L; simpl in *; dcr; eauto.
  - cases; eauto.
    constructor; eauto.
    rewrite filter_InA; intuition.
Qed.


Lemma DVE_renamedApart i LV ZL s lv G D
  : renamedApart s G
    -> true_live_sound i ZL LV s lv
    -> D ⊆ fst (getAnn G)
    -> getAnn lv ⊆ D
    -> renamedApart (compile (zip pair LV ZL)  s lv) (compile_renamedApart s lv G D).
Proof.
  intros RA TLS Dincl inclD.
  general induction TLS; invt renamedApart; simpl; eauto using renamedApart.
  - cases; simpl in *.
    + econstructor; try reflexivity; eauto with cset.
      exploit H; eauto. eapply Exp.freeVars_live in H1. eauto with cset.
      eapply IHTLS; eauto.
      rewrite H9, Dincl; simpl; eauto with cset.
      rewrite <- inclD, <- H0. eauto with cset.
      eapply pe_eta_split; econstructor; simpl; eauto.
    + eapply IHTLS; eauto.
      * rewrite H9; simpl; cset_tac.
      * rewrite <- inclD, <- H0. revert NOTCOND; clear; cset_tac.
  - repeat cases; eauto.
    + exploit H4; eauto.
      eapply H0; eauto with cset pe.
    + exploit H5; eauto.
      eapply H2; eauto with cset pe.
    + econstructor; try reflexivity; eauto.
      * exploit H3; eauto. eapply Op.freeVars_live in H6. eauto with cset.
      * rewrite !snd_getAnn_renamedApart, H15, H16; eauto.
      * exploit H4; eauto.
        eapply H0; pe_rewrite; eauto with cset.
      * exploit H5; eauto.
        eapply H2; pe_rewrite; eauto with cset.
      * eapply pe_eta_split; econstructor; simpl; eauto.
      * eapply pe_eta_split; econstructor; simpl; eauto.
  - econstructor; eauto.
    eapply list_union_incl; intros; inv_get; eauto with cset. simpl in *.
    edestruct filter_by_get; eauto. simpl in *.
    erewrite get_nth in *; eauto using zip_get. simpl in *; dcr.
    cases in H10.
    exploit argsLive_live_exp_sound; eauto.
    eapply Op.freeVars_live in H7. rewrite H7. eauto.
  - econstructor; eauto.
    eapply Op.freeVars_live in H. rewrite H. eauto.
  - econstructor; eauto with len; (try eapply eq_union_lr); eauto.
    * intros; inv_get. simpl in *.
      rewrite <- zip_app; eauto with len.
      eapply H1; eauto.
      -- edestruct H8; eauto; dcr. rewrite H4. rewrite Dincl;  eauto.
         unfold filter_set; rewrite of_list_filter. clear; cset_tac.
      -- unfold filter_set; rewrite of_list_filter.
    * hnf; intros; inv_get.
      edestruct H8; eauto; dcr.
      simpl. econstructor; unfold filter_set; simpl in *.
      erewrite fst_getAnn_renamedApart; eauto with cset.
      split. eapply unique_filter; eauto.
      split. eapply disj_2_incl; eauto. rewrite of_list_filter.
      eapply disj_1_incl; eauto. cset_tac.
      erewrite fst_getAnn_renamedApart, !snd_getAnn_renamedApart; eauto.
      pe_rewrite. rewrite of_list_filter. eapply disj_1_incl; eauto.
      clear; cset_tac.
    * hnf; intros. inv_get.
      unfold defVars; simpl. exploit H9; try eapply H4; eauto using zip_get.
      unfold defVars in*. rewrite !snd_getAnn_renamedApart; eauto.
      unfold filter_set. rewrite !of_list_filter; eauto.
      eapply disj_1_incl. eapply disj_2_incl. eauto.
      clear; cset_tac.
      clear; cset_tac.
    * rewrite <- zip_app; eauto with len; simpl in *.
      eapply IHTLS; eauto.
      pe_rewrite. eauto. rewrite <- inclD; eauto.
    * eapply pe_eta_split; econstructor; eauto.
      erewrite fst_getAnn_renamedApart; eauto.
    * eapply list_union_eq; intros; eauto 20 with len.
      inv_get. unfold defVars; simpl.
      unfold filter_set; simpl. reflexivity.
Qed.
