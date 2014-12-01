Require Import CSet Le.
Require Import Plus Util AllInRel Map.

Require Import Val EqDec Computable Var Env EnvTy IL Annotation.
Require Import Sim Fresh Filter Liveness Filter MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Definition exp2bool (e:exp) : option bool :=
  match e with
    | Con c => Some (val2bool c)
    | _ => None
  end.

Lemma exp2bool_val2bool E e b
: exp2bool e = Some b
  -> exists v, exp_eval E e = Some v /\ val2bool v = b.
Proof.
  destruct e; simpl; intros; try congruence.
  inv H; eauto.
Qed.

Fixpoint compile (LV:list (set var * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtExp x e s, ann1 lv an =>
      if [x ∈ getAnn an] then stmtExp x e (compile LV s an)
                         else compile LV s an
    | stmtIf e s t, ann2 _ ans ant =>
      if [exp2bool e = Some true] then
        (compile LV s ans)
      else if [ exp2bool e = Some false ] then
        (compile LV t ant)
      else
        stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtGoto f Y, ann0 lv =>
      let lvZ := nth (counted f) LV (∅,nil) in
      stmtGoto f (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtExtern x f e s, ann1 lv an =>
      stmtExtern x f e (compile LV s an)
    | stmtLet Z s t, ann2 lv ans ant =>
      let LV' := (getAnn ans,Z)::LV in
      stmtLet (List.filter (fun x => B[x ∈ getAnn ans]) Z)
              (compile LV' s ans) (compile LV' t ant)
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
  - simpl. destruct if. simpl. eapply agree_on_update_same. reflexivity.
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
  general induction s; simpl; inv H0; simpl in * |- *.
  - case_eq (exp_eval V e); intros. destruct if.
    + pfold. econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto. reflexivity.
      left. eapply IHs; eauto. eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto.
    + eapply sim'_expansion_closed;
      [ | eapply S_star2 with (y:=EvtTau);
          [ econstructor; eauto | eapply star2_refl ]
        | eapply star2_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat destruct if.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply IHs1; eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply IHs2; eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      destruct o. case_eq (val2bool v); intros.
      pfold; econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. reflexivity.
      left; eapply IHs1; eauto using agree_on_incl.
      pfold; econstructor; try eapply plus2O.
      econstructor 3; eauto. reflexivity.
      econstructor 3; eauto. reflexivity.
      left; eapply IHs2; eauto using agree_on_incl.
      pfold. econstructor 3; try eapply star2_refl; eauto.
      stuck.
  - destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    + remember (omap (exp_eval V) Y). symmetry in Heqo.
      exploit (get_nth); try eapply H4; eauto. rewrite X; simpl.
      destruct o.
      * exploit omap_filter_by; eauto.
        unfold simL' in H1.
        edestruct AIR5_length; try eassumption; dcr.
        edestruct get_length_eq; try eassumption.
        edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
        simpl in *. repeat get_functional; subst.
        inv H16. hnf in H21. hnf in H19. simpl in *.
        dcr; simpl in *. subst bZ.
        eapply sim_drop_shift. eapply H22; eauto.
        eapply omap_exp_eval_live_agree; eauto.
        inv H0.
        eapply argsLive_liveSound; eauto.
        hnf; split; eauto. simpl. exploit omap_length; try eapply Heqo; eauto.
        congruence.
      * pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    + pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
      hnf in H1.
      edestruct AIR5_nth3 as [? [? [? []]]]; eauto; dcr.
  - pfold. econstructor 4; try eapply star2_refl.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
    stuck2. stuck2.
  - pfold.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    econstructor 2; try eapply star2_refl.
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply IHs; eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply IHs; eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + eapply sim'Err; try eapply star2_refl; simpl; eauto.
      stuck2.
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IHs2; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * hnf; intros. split. simpl. hnf. simpl; intuition.
        hnf; intros. hnf in H3. hnf in H2. dcr; simpl in *. subst.
        eapply IHs1; eauto.
        eapply agree_on_update_filter'; eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
      * hnf; intros; eauto.
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

Import Sim.I.

Definition ArgRel (V V':onv val) (G:(set var * params)) (VL VL': list val) : Prop :=
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL /\
  agree_on eq (fst G \ of_list (snd G)) V V'.

Definition ParamRel (G:(set var * params)) (Z Z' : list var) : Prop :=
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Instance SR : SimRelation (set var * params) := {
   ParamRel := ParamRel;
   ArgRel := ArgRel;
   BlockRel := fun lvZ b b' => I.block_Z b = snd lvZ
}.
intros. inv H; inv H0; dcr; simpl in *.
erewrite filter_filter_by_length; eauto.
Defined.

Lemma sim_I r L L' V V' s LV lv
: agree_on eq (getAnn lv) V V'
-> true_live_sound Imperative LV s lv
-> simL' r SR LV L L'
-> sim'r r (L,V, s) (L',V', compile LV s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  - case_eq (exp_eval V e); intros. destruct if.
    + pfold. econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto. eapply agree_on_sym; eauto. reflexivity.
      left. eapply IHs; eauto. eapply agree_on_update_same. reflexivity.
      eapply agree_on_incl; eauto.
    + eapply sim'_expansion_closed;
      [ | eapply S_star2 with (y:=EvtTau);
          [ econstructor; eauto | eapply star2_refl ]
        | eapply star2_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    + pfold. econstructor 3; [| eapply star2_refl|]; eauto. stuck.
  - repeat destruct if.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply IHs1; eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor; eauto. eapply star2_refl.
      eapply star2_refl.
    + edestruct (exp2bool_val2bool V); eauto; dcr.
      eapply sim'_expansion_closed.
      eapply IHs2; eauto. eapply agree_on_incl; eauto.
      eapply S_star2 with (y:=EvtTau) (yl:=nil).
      econstructor 3; eauto. eapply star2_refl.
      eapply star2_refl.
    + remember (exp_eval V e). symmetry in Heqo.
      exploit exp_eval_live_agree; eauto.
      destruct o. case_eq (val2bool v); intros.
      pfold; econstructor; try eapply plus2O.
      econstructor; eauto. reflexivity.
      econstructor; eauto. reflexivity.
      left; eapply IHs1; eauto using agree_on_incl.
      pfold; econstructor; try eapply plus2O.
      econstructor 3; eauto. reflexivity.
      econstructor 3; eauto. reflexivity.
      left; eapply IHs2; eauto using agree_on_incl.
      pfold. econstructor 3; try eapply star2_refl; eauto.
      stuck.
  - destruct (get_dec L (counted l)) as [[[bZ bs]]|].
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit (get_nth); try eapply H4; eauto. rewrite X; simpl.
    destruct o.
    exploit omap_filter_by; eauto.
    unfold simL' in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H21. dcr; simpl in *. subst bZ.
    eapply sim_drop_shift. eapply H21; eauto.
    eapply omap_exp_eval_live_agree; eauto.
    inv H0.
    eapply argsLive_liveSound; eauto.
    hnf; split; eauto. simpl. exploit omap_length; try eapply Heqo; eauto.
    split.
    congruence. eapply agree_on_incl; eauto.
    pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    pfold; econstructor 3; try eapply star2_refl; eauto; stuck2.
    hnf in H1.
    edestruct AIR5_nth3 as [? [? [? []]]]; eauto; dcr.
  - pfold. econstructor 4; try eapply star2_refl.
    simpl. erewrite <- exp_eval_live_agree; eauto. eapply agree_on_sym; eauto.
    stuck2. stuck2.
  - pfold.
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit omap_exp_eval_live_agree; eauto.
    destruct o.
    econstructor 2; try eapply star2_refl.
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + eexists (ExternI f l 0); eexists; try (now (econstructor; eauto)).
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply IHs; eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + intros. inv H2. eexists. split.
      * econstructor; eauto. congruence.
      * left. eapply IHs; eauto. eapply agree_on_update_same; eauto.
        eapply agree_on_incl; eauto.
    + eapply sim'Err; try eapply star2_refl; simpl; eauto.
      stuck2.
  - pfold. econstructor; try eapply plus2O.
    econstructor; eauto. reflexivity.
    econstructor; eauto. reflexivity.
    simpl. left. eapply IHs2; eauto.
    + simpl in *; eapply agree_on_incl; eauto.
    + eapply simL_mon; eauto. eapply simL_extension'; eauto.
      * hnf; intros. hnf in H3. hnf in H2. dcr; subst.
        eapply IHs1; eauto.
        eapply agree_on_update_filter'; eauto.
      * split; reflexivity.
      * hnf; intros; eauto.
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

Fixpoint compile_live (s:stmt) (a:ann (set var)) : ann (set var) :=
  match s, a with
    | stmtExp x e s, ann1 lv an as a =>
      if [x ∈ getAnn an] then ann1 lv (compile_live s an)
                         else compile_live s an
    | stmtIf e s t, ann2 lv ans ant =>
      if [exp2bool e = Some true] then
        compile_live s ans
      else if [exp2bool e = Some false ] then
        compile_live t ant
      else
        ann2 lv (compile_live s ans) (compile_live t ant)
    | stmtGoto f Y, ann0 lv as a => a
    | stmtReturn x, ann0 lv as a => a
    | stmtExtern x f Y s, ann1 lv an as a =>
      ann1 lv (compile_live s an)
    | stmtLet Z s t, ann2 lv ans ant =>
      let ans' := compile_live s ans in
      ann2 lv (setTopAnn (ans')
                           (getAnn ans' ∪
                                   of_list (List.filter (fun x => B[x ∈ getAnn ans]) Z)))
                           (compile_live t ant)
    | _, a => a
  end.


Lemma compile_live_incl i LV s lv
  : true_live_sound i LV s lv
    -> getAnn (compile_live s lv) ⊆ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto; try reflexivity.
  - destruct if; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
  - repeat destruct if; simpl; try reflexivity.
    + etransitivity; eauto.
    + etransitivity; eauto.
Qed.

Definition compile_LV (LV:list (set var *params)) :=
  List.map (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                      (fst lvZ, Z')) LV.

Lemma dve_live i LV s lv
  : true_live_sound i LV s lv
    -> live_sound i (compile_LV LV) (compile LV s lv) (compile_live s lv).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - destruct if; eauto. econstructor; eauto.
    rewrite compile_live_incl; eauto.
  - repeat destruct if; eauto.
    + econstructor; eauto; rewrite compile_live_incl; eauto.
  - econstructor. eapply (map_get_1 (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                      (fst lvZ, Z')) H); eauto.
    simpl. rewrite <- H0. rewrite minus_inter_empty. reflexivity.
    cset_tac; intuition. eapply filter_incl2; eauto.
    eapply filter_in; eauto. intuition. hnf. destruct if; eauto.
    simpl. eapply get_nth in H. erewrite H. simpl.
    erewrite filter_filter_by_length. reflexivity. congruence.
    intros. eapply get_nth in H. erewrite H in H3. simpl in *.
    edestruct filter_by_get as [? [? [? []]]]; eauto; dcr.
    eapply argsLive_live_exp_sound; eauto. simpl in *.
    decide (x0 ∈ blv); intuition.
  - econstructor; eauto.
    rewrite compile_live_incl; eauto.
  - econstructor; simpl in *.
    eapply live_sound_monotone. eapply live_sound_monotone2.
    eapply IHtrue_live_sound1. cset_tac; intuition.
    econstructor; simpl.
    simpl. rewrite getAnn_setTopAnn, compile_live_incl.
    split; eauto. rewrite filter_incl. cset_tac; intuition.
    eauto. eapply PIR2_refl. hnf; intuition.
    eapply live_sound_monotone. eapply IHtrue_live_sound2.
    econstructor; simpl.
    rewrite getAnn_setTopAnn, compile_live_incl.
    split; eauto. rewrite filter_incl. cset_tac; intuition. eauto.
    eapply PIR2_refl. hnf; intuition.
    rewrite getAnn_setTopAnn. cset_tac; intuition.
    destruct i; eauto. rewrite getAnn_setTopAnn.
    rewrite compile_live_incl; eauto.
    rewrite union_comm. rewrite union_minus_remove.
    rewrite <- H1.
    rewrite minus_inter_empty. reflexivity.
    cset_tac; intuition. eapply filter_incl2; eauto.
    eapply filter_in; eauto. intuition. hnf. destruct if; eauto.
    rewrite compile_live_incl; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
