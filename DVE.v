Require Import CSet Le.
Require Import Plus Util AllInRel Map.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Sim Fresh Filter Liveness TrueLiveness Filter MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint compile (LV:list (set var * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtLet x e s, ann1 lv an =>
      if [x ∈ getAnn an] then stmtLet x e (compile LV s an)
                         else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [exp2bool e = Some true] then
        (compile LV s ans)
      else if [ exp2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtApp f Y, ann0 lv =>
      let lvZ := nth (counted f) LV (∅,nil) in
      stmtApp f (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile LV s an)
    | stmtFun F t, annF lv ans ant =>
      let LV' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) ++ LV in
      stmtFun (zip (fun Zs a => (List.filter (fun x => B[x ∈ getAnn a]) (fst Zs),
                              compile LV' (snd Zs) a)) F ans)
              (compile LV' t ant)
    | s, _ => s
  end.

Definition ArgRel (V V:onv val) (G:(set var * params)) (VL VL': list val) : Prop :=
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL.

Definition ParamRel (G:(set var * params)) (Z Z' : list var) : Prop :=
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Instance SR : ProofRelation (set var * params) := {
   ParamRel := ParamRel;
   ArgRel := ArgRel;
   BlockRel := fun lvZ b b' => True (* F.block_Z b = snd lvZ *)
}.
intros. inv H; inv H0; simpl in *.
erewrite filter_filter_by_length; eauto.
Defined.


Lemma agree_on_update_filter X `{OrderedType X} Y `{Equivalence (option Y)}
      (lv:set X) (V: X -> option Y) Z VL
: length Z = length VL
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             List.map Some (filter_by (fun x => B[x ∈ lv]) Z VL)]).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1.
  - eapply agree_on_refl. eapply H0.
  - simpl. cases. simpl. eapply agree_on_update_same. reflexivity.
    eapply agree_on_incl. eapply IHlength_eq. eauto. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' X `{OrderedType X} Y `{Equivalence (option Y)} (lv:set X) (V V':X -> option Y) Z VL
: length Z = length VL
  -> agree_on R (lv \ of_list Z) V V'
  -> agree_on R lv
             (V [Z <-- List.map Some VL])
             (V' [(List.filter (fun x => B[x ∈ lv]) Z) <-- (List.map Some
                             (filter_by (fun x => B[x ∈ lv]) Z VL))]).
Proof.
  intros.
  eapply agree_on_trans. eapply H0.
  eapply update_with_list_agree; eauto. rewrite map_length; eauto.
  eapply agree_on_update_filter; eauto.
Qed.


Lemma sim_DVE' r L L' V V' s LV lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional LV s lv
-> simL' sim_progeq r SR LV L L'
-> sim'r r (L,V, s) (L',V', compile LV s lv).
Proof.
  revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros. cases.
    + pone_step.
      instantiate (1:=v). erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
      left. eapply (IH s); eauto. eapply agree_on_update_same; eauto with cset.
    + eapply sim'_expansion_closed;
      [ | eapply S_star2 with (y:=EvtTau);
          [ econstructor; eauto | eapply star2_refl ]
        | eapply star2_refl].
      eapply (IH s); eauto. eapply agree_on_update_dead; eauto with cset.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
      eapply H10; congruence.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s2); eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      eapply H8. case_eq (exp2bool e); intros; try destruct b; congruence.
      destruct o. case_eq (val2bool v); intros.
      pone_step. left. eapply IH; eauto with cset.
      pone_step. left; eapply (IH s2); eauto with cset.
      pno_step.
  - destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    + remember (omap (exp_eval V) Y). symmetry in Heqo.
      rewrite (get_nth (∅, nil) H4); simpl.
      destruct o.
      * exploit omap_filter_by; eauto.
        unfold simL' in H1. inRel_invs. simpl in *.
        hnf in H17; dcr; subst; simpl in *.
        eapply sim_drop_shift; eauto.
        eapply (inRel_sawtooth H1). eapply (inRel_sawtooth H1). eapply H19. eauto.
        eapply omap_exp_eval_live_agree; eauto.
        eapply argsLive_liveSound; eauto.
        hnf; split; eauto. simpl. exploit omap_length; try eapply Heqo; eauto.
        congruence.
      * pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
      hnf in H1. inRel_invs. eauto.
  - pno_step; simpl. erewrite <- exp_eval_live_agree; eauto; symmetry; eauto.
  - pfold.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    econstructor 2; try eapply star2_refl.
    + eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
    + eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply (IH s); eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + intros. inv H3. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply (IH s); eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + eapply sim'Err; try eapply star2_refl; simpl; eauto.
      stuck2.
  - pone_step. left. eapply IH; eauto with cset.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto with len.
      * intros. inv_get; simpl. split. hnf; intros; simpl.
        unfold ParamRel, ArgRel. intuition.
        eapply (IH s1); eauto. subst.
        eapply agree_on_update_filter'; eauto.
        eapply agree_on_incl; eauto. simpl.
        exploit H8; eauto.
        exploit H6; eauto.
        unfold ParamRel. intuition.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Functional nil s lv
-> @sim F.state _ F.state _ (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply sim_DVE'; eauto. hnf. econstructor.
Qed.

Module I.

  Require Import SimI.

Definition ArgRel (V V':onv val) (G:(set var * params)) (VL VL': list val) : Prop :=
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL /\
  agree_on eq (fst G \ of_list (snd G)) V V'.

Definition ParamRel (G:(set var * params)) (Z Z' : list var) : Prop :=
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Instance SR : ProofRelationI (set var * params) := {
   ParamRelI := ParamRel;
   ArgRelI := ArgRel;
   BlockRelI := fun lvZ b b' => I.block_Z b = snd lvZ
}.
intros. inv H; inv H0; dcr; simpl in *.
erewrite filter_filter_by_length; eauto.
Defined.

Lemma sim_I r L L' V V' s LV lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative LV s lv
-> simILabenv sim_progeq r SR LV L L'
-> sim'r r (L,V, s) (L',V', compile LV s lv).
Proof.
  revert_except s.
  sind s; destruct s; simpl; intros; invt true_live_sound; simpl in * |- *.
  - case_eq (exp_eval V e); intros. cases.
    + pone_step. instantiate (1:=v).
      erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto.
      left. eapply (IH s); eauto. eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto.
    + eapply sim'_expansion_closed;
      [ | eapply S_star2 with (y:=EvtTau);
          [ econstructor; eauto | eapply star2_refl ]
        | eapply star2_refl].
      eapply (IH s); eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat cases.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s1); eauto. eapply agree_on_incl; eauto.
      eapply H10; congruence.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply (IH s2); eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      eapply H8. case_eq (exp2bool e); intros; try destruct b; congruence.
      destruct o. case_eq (val2bool v); intros.
      pfold; econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. reflexivity.
      left; eapply (IH s1); eauto using agree_on_incl.
      pfold; econstructor; try eapply plus2O.
      econstructor 3; eauto. reflexivity.
      econstructor 3; eauto. reflexivity.
      left; eapply (IH s2); eauto using agree_on_incl.
      pfold. econstructor 3; try eapply star2_refl; eauto.
      stuck.
  - destruct (get_dec L (counted l)) as [[[bZ bs]]|].
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    rewrite (get_nth (∅, nil) H4); eauto; simpl.
    destruct o.
    exploit omap_filter_by; eauto.
    hnf in H1. inRel_invs; simpl in *; subst.
    hnf in H15. dcr; simpl in *; clear_trivial_eqs; subst.
    eapply sim_drop_shift_I. eapply (inRel_sawtooth H1).
    eapply (inRel_sawtooth H1). eauto. eauto.
    simpl. eapply H18; eauto.
    eapply omap_exp_eval_live_agree; eauto.
    inv H0.
    eapply argsLive_liveSound; eauto.
    hnf; split; eauto. simpl. split.
    exploit omap_length; try eapply Heqo; eauto. congruence.
    eapply agree_on_incl; eauto.
    pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    hnf in H1. inRel_invs; eauto.
  - pfold. econstructor 4; try eapply star2_refl.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
    stuck2. stuck2.
  - pfold.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    econstructor 2; try eapply star2_refl.
    + eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
    + eexists (ExternI f l default_val); eexists; try (now (econstructor; eauto)).
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply (IH s); eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + intros. inv H3. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply (IH s); eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + eapply sim'Err; try eapply star2_refl; simpl; eauto.
      stuck2.
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IH; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + eapply simILabenv_mon; eauto. eapply simILabenv_extension; eauto with len.
      * intros. inv_get; simpl. split. hnf; intros; simpl.
        unfold ParamRel, ArgRel. intuition.
        eapply (IH s1); eauto. subst.
        eapply agree_on_update_filter'; eauto.
        exploit H6; eauto.
        unfold ParamRel. intuition.
Qed.

Lemma sim_DVE V V' s lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative nil s lv
-> @sim I.state _ I.state _ (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply sim'_sim.
  eapply sim_I; eauto. hnf. econstructor.
Qed.

End I.


Fixpoint compile_live (s:stmt) (a:ann (set var)) (G:set var) : ann (set var) :=
  match s, a with
    | stmtLet x e s, ann1 lv an as a =>
      if [x ∈ getAnn an] then ann1 (G ∪ lv) (compile_live s an {x})
                         else compile_live s an G
    | stmtIf e s t, ann2 lv ans ant =>
      if [exp2bool e = Some true] then
        compile_live s ans G
      else if [exp2bool e = Some false ] then
        compile_live t ant G
      else
        ann2 (G ∪ lv) (compile_live s ans ∅) (compile_live t ant ∅)
    | stmtApp f Y, ann0 lv => ann0 (G ∪ lv)
    | stmtReturn x, ann0 lv => ann0 (G ∪ lv)
    | stmtExtern x f Y s, ann1 lv an as a =>
      ann1 (G ∪ lv) (compile_live s an {x})
    | stmtFun F t, annF lv ans ant =>
      let ans' := zip (fun Zs a => let a' := compile_live (snd Zs) a ∅ in
                               setTopAnn a' (getAnn a' ∪ of_list (List.filter (fun x => B[x ∈ getAnn a]) (fst Zs)))) F ans in
      annF (G ∪ lv) ans' (compile_live t ant ∅)
    | _, a => a
  end.


Lemma compile_live_incl G i LV s lv
  : true_live_sound i LV s lv
    -> getAnn (compile_live s lv G) ⊆ G ∪ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity.
    + etransitivity; eauto. rewrite <- H2. eauto. congruence.
    + etransitivity; eauto.  rewrite <- H3; eauto.
Qed.

Lemma compile_live_incl_empty i LV s lv
  : true_live_sound i LV s lv
    -> getAnn (compile_live s lv ∅) ⊆ getAnn lv.
Proof.
  intros.
  eapply compile_live_incl in H.
  rewrite H. cset_tac; intuition.
Qed.

Lemma incl_compile_live G i LV s lv
  : true_live_sound i LV s lv
    -> G ⊆ getAnn (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto.
  - cases; simpl; try reflexivity. cset_tac; intuition.
    rewrite <- IHtrue_live_sound. cset_tac; intuition.
  - repeat cases; simpl; try reflexivity; eauto.
Qed.

Definition compile_LV (LV:list (set var *params)) :=
  List.map (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                      (fst lvZ, Z')) LV.

Lemma dve_live i LV s lv G
  : true_live_sound i LV s lv
    -> live_sound i (compile_LV LV) (compile LV s lv) (compile_live s lv G).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - cases; eauto. econstructor; eauto.
    + eapply live_exp_sound_incl; eauto. eauto.
    + rewrite compile_live_incl; eauto.
      rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - repeat cases; eauto.
    + econstructor; eauto; try rewrite compile_live_incl; eauto.
      eapply live_exp_sound_incl. eapply incl_right.
      eapply H1. case_eq (exp2bool e); intros; try destruct b; congruence.
      cset_tac; intuition.
      cset_tac; intuition.
  - econstructor.
    + eapply (map_get_1 (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                                   (fst lvZ, Z')) H); eauto.
    + simpl. destruct i; simpl in * |- *; eauto.
      rewrite <- H0. rewrite minus_inter_empty. eapply incl_right.
      cset_tac; intuition. eapply filter_incl2; eauto.
      eapply filter_in; eauto. intuition. hnf. cases; eauto.
      rewrite <- H0. rewrite minus_inter_empty. eapply incl_right.
      cset_tac; intuition. eapply filter_incl2; eauto.
      eapply filter_in; eauto. intuition. hnf. cases; eauto.
    + simpl. eapply get_nth in H. erewrite H. simpl.
      erewrite filter_filter_by_length. reflexivity. congruence.
    + intros. eapply get_nth in H. erewrite H in H3. simpl in *.
      edestruct filter_by_get as [? [? [? []]]]; eauto; dcr.
      eapply live_exp_sound_incl. eapply incl_right.
      eapply argsLive_live_exp_sound; eauto. simpl in *.
      decide (x0 ∈ blv); intuition.
  - econstructor; eauto.
    eapply live_exp_sound_incl; eauto using incl_right.
  - econstructor; eauto.
    + intros; eapply live_exp_sound_incl; eauto using incl_right.
    + rewrite compile_live_incl; eauto. rewrite <- H1. cset_tac; intuition.
    + eapply incl_compile_live; eauto.
  - econstructor; simpl in *; eauto with len.
    + eapply live_sound_monotone.
      eapply IHtrue_live_sound.
      unfold compile_LV. rewrite map_app. eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. rewrite of_list_filter.
      split; cset_tac.
    + intros; inv_get.
      eapply live_sound_monotone.
      eapply live_sound_monotone2; eauto. eapply H2; eauto.
      unfold compile_LV. rewrite map_app. eapply PIR2_app; eauto.
      eapply PIR2_get; eauto 30 with len.
      intros; inv_get. simpl. rewrite getAnn_setTopAnn.
      rewrite compile_live_incl_empty; eauto. rewrite of_list_filter.
      split; cset_tac.
    + intros; inv_get.
      repeat rewrite getAnn_setTopAnn; simpl.
      split; eauto. cases; eauto.
      exploit H3; eauto.
      rewrite compile_live_incl_empty; eauto. rewrite <- H5.
      rewrite of_list_filter.
      clear_all; cset_tac.
    + rewrite compile_live_incl; eauto with cset.
Qed.
