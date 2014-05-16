Require Import CSet Le.
Require Import Plus Util AllInRel Map.

Require Import Val Var Env EnvTy IL Annotation.
Require Import Sim SimApx Fresh Filter Liveness Filter MoreExp.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint compile (LV:list (set var * params)) (s:stmt) (a:ann (set var)) :=
  match s, a with
    | stmtExp x e s, ann1 lv an =>
      if [x ∈ getAnn an] then stmtExp x e (compile LV s an)
                         else compile LV s an
    | stmtIf e s t, ann2 _ ans ant => stmtIf e (compile LV s ans) (compile LV t ant)
    | stmtGoto f Y, ann0 lv =>
      let lvZ := nth (counted f) LV (∅,nil) in
      stmtGoto f (filter_by (fun y => B[y ∈ fst lvZ]) (snd lvZ) Y)
    | stmtReturn x, ann0 _ => stmtReturn x
    | stmtLet Z s t, ann2 lv ans ant =>
      let LV' := (getAnn ans,Z)::LV in
      stmtLet (List.filter (fun x => B[x ∈ getAnn ans]) Z)
              (compile LV' s ans) (compile LV' t ant)
    | s, _ => s
  end.

Definition ArgRel (G:(set var * params)) (VL VL': list val) : Prop :=
  VL' = (filter_by (fun x => B[x ∈ (fst G)]) (snd G) VL) /\
  length (snd G) = length VL.

Definition ParamRel (G:(set var * params)) (Z Z' : list var) : Prop :=
  Z' = (List.filter (fun x => B[x ∈ (fst G)]) Z) /\ snd G = Z.

Lemma agree_on_update_filter X `{OrderedType X} Y `{Equivalence (option Y)}
      (lv:set X) (V: X -> option Y) Z VL
: length Z = length VL
  -> agree_on lv
             (V [Z <-- List.map Some VL])
             (V [List.filter (fun x => B[x ∈ lv]) Z <--
                             List.map Some (filter_by (fun x => B[x ∈ lv]) Z VL)]).
Proof.
  intros. eapply length_length_eq in H1.
  general induction H1.
  - eapply agree_on_refl.
  - simpl. destruct if. simpl. eapply agree_on_update_same.
    eapply agree_on_incl. eapply IHlength_eq. cset_tac; intuition.
    eapply agree_on_update_dead; eauto.
Qed.

Lemma agree_on_update_filter' X `{OrderedType X} Y `{Equivalence (option Y)} (lv:set X) (V V':X -> option Y) Z VL
: length Z = length VL
  -> agree_on (lv \ of_list Z) V V'
  -> agree_on lv
             (V [Z <-- List.map Some VL])
             (V' [(List.filter (fun x => B[x ∈ lv]) Z) <-- (List.map Some
                             (filter_by (fun x => B[x ∈ lv]) Z VL))]).
Proof.
  intros.
  eapply agree_on_trans.
  eapply update_with_list_agree; eauto. rewrite map_length; eauto.
  eapply agree_on_update_filter. eauto.
Qed.

Definition blockRel (AL:list (set var*params)) L (L':F.labenv) := (forall n blk lvZ, get AL n lvZ -> get L n blk -> block_Z blk = snd lvZ).

Lemma sim_DVE' r L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> paco2 (@psimapx F.state _ F.state _) r (L,V, s) (L',V', compile LV s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if.
    - pfold. econstructor; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      left. eapply IHs; eauto. eapply agree_on_update_same.
      eapply agree_on_incl; eauto.
    - eapply simapx_expansion_closed;
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - pfold. econstructor 3; [| eapply star_refl|]; eauto. stuck.
  + remember (exp_eval V e). symmetry in Heqo.
    exploit exp_eval_live_agree; eauto.
    destruct o. case_eq (val2bool v); intros.
    pfold; econstructor; try eapply plusO.
    econstructor; eauto. econstructor; eauto.
    left; eapply IHs1; eauto using agree_on_incl.
    pfold; econstructor; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    left; eapply IHs2; eauto using agree_on_incl.
    pfold. econstructor 2; try eapply star_refl; eauto.
    stuck. stuck.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
    remember (omap (exp_eval V) Y). symmetry in Heqo.
    exploit (get_nth); try eapply H4; eauto. rewrite X; simpl.
    destruct o.
    exploit omap_filter_by; eauto.
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply sim_drop_shift. eapply H21; eauto.
    eapply omap_exp_eval_live_agree; eauto.
    inv H0.
    eapply argsLive_liveSound; eauto.
    hnf; split; eauto. simpl. exploit omap_length; try eapply Heqo; eauto.
    congruence.
    pfold; eapply psimErr; try eapply star_refl; eauto; stuck.
    pfold; eapply psimErr; try eapply star_refl; eauto; stuck.
    hnf in H1.
    edestruct AIR5_nth2 as [? [? [? []]]]; eauto; dcr.
  + pfold. econstructor 2; try eapply star_refl.
    simpl. erewrite <- exp_eval_live_agree; eauto using agree_on_sym.
    stuck. stuck.
  + pfold. econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. left. eapply IHs2; eauto.
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_mon; eauto. eapply simL_extension'; eauto.
      hnf; intros. hnf in H3. hnf in H2. dcr; subst.
      split; eauto. eapply filter_filter_by_length; eauto.
      hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. dcr; subst. simpl.
        eapply agree_on_update_filter'; eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.

Lemma sim_DVE V V' s lv
: agree_on (getAnn lv) V V'
-> true_live_sound nil s lv
-> @simapx F.state _ F.state _ (nil,V, s) (nil,V', compile nil s lv).
Proof.
  intros. eapply psimapxd_simapx.
  eapply sim_DVE'; eauto. hnf. econstructor.
Qed.

Print Assumptions sim_DVE.

Fixpoint compile_live (s:stmt) (a:ann (set var)) : ann (set var) :=
  match s, a with
    | stmtExp x e s, ann1 lv an as a =>
      if [x ∈ getAnn an] then ann1 lv (compile_live s an)
                         else compile_live s an
    | stmtIf x s t, ann2 lv ans ant =>
      ann2 lv (compile_live s ans) (compile_live t ant)
    | stmtGoto f Y, ann0 lv as a => a
    | stmtReturn x, ann0 lv as a => a
    | stmtLet Z s t, ann2 lv ans ant =>
      let ans' := compile_live s ans in
      ann2 lv (setTopAnn (ans')
                           (getAnn ans' ∪
                                   of_list (List.filter (fun x => B[x ∈ getAnn ans]) Z)))
                           (compile_live t ant)
    | _, a => a
  end.


Lemma compile_live_incl LV s lv
  : true_live_sound LV s lv
    -> getAnn (compile_live s lv) ⊆ getAnn lv.
Proof.
  intros. general induction H; simpl; eauto; try reflexivity.
  - destruct if; simpl; try reflexivity.
    rewrite IHtrue_live_sound. rewrite <- H1. cset_tac; intuition.
Qed.

Definition compile_LV (LV:list (set var *params)) :=
  List.map (fun lvZ => let Z' := List.filter (fun x => B[x ∈ fst lvZ]) (snd lvZ) in
                      (fst lvZ, Z')) LV.

(* TODO: move to CSetGet *)
Lemma get_in_incl X `{OrderedType X} (L:list X) s
: (forall n x, get L n x -> x ∈ s)
  -> of_list L ⊆ s.
Proof.
  intros. general induction L; simpl.
  - cset_tac; intuition.
  - exploit H0; eauto using get.
    exploit IHL; intros; eauto using get.
    cset_tac; intuition. rewrite <- H2; eauto.
Qed.

(*TODO move to CSetBasic *)
Lemma minus_inter_empty X `{OrderedType X} s t u
: s ∩ t [=] s ∩ u
  -> s \ t [=] s \ u.
Proof.
  intros. cset_tac; intuition.
  hnf in H0. eapply H3. eapply H0; eauto.
  eapply H3. eapply H0. eauto.
Qed.

Lemma dve_live LV s lv
  : true_live_sound LV s lv
    -> live_sound (compile_LV LV) (compile LV s lv) (compile_live s lv).
Proof.
  intros. general induction H; simpl; eauto using live_sound, compile_live_incl.
  - destruct if; eauto. econstructor; eauto.
    rewrite compile_live_incl; eauto.
  - econstructor; eauto; rewrite compile_live_incl; eauto.
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
    rewrite getAnn_setTopAnn.
    rewrite compile_live_incl; eauto.
    rewrite union_comm. rewrite union_minus_remove.
    rewrite <- H1.
    rewrite minus_inter_empty. reflexivity.
    cset_tac; intuition. eapply filter_incl2; eauto.
    eapply filter_in; eauto. intuition. hnf. destruct if; eauto.
    rewrite compile_live_incl; eauto.
Qed.

(*
Lemma sim_DVE L L' V V' s LV lv
: agree_on (getAnn lv) V V'
-> true_live_sound LV s lv
-> simL' r ArgRel ParamRel LV L L'
-> @simapx F.state _ F.state _ (L,V, s) (L',V', compile s lv).
Proof.
  general induction s; simpl; inv H0; simpl in * |- *.
  + case_eq (exp_eval V e); intros. destruct if.
    - eapply simS; try eapply plusO.
      econstructor; eauto.
      econstructor; eauto. instantiate (1:=v).
      erewrite exp_eval_live; eauto using agree_on_sym.
      eapply IHs; eauto. eapply agree_on_update_same.
      eapply agree_on_incl; eauto.
    - eapply simapx_expansion_closed;
      [ | eapply S_star; [ econstructor; eauto | eapply star_refl ]
        | eapply star_refl].
      eapply IHs; eauto. eapply agree_on_update_dead; eauto.
      eapply agree_on_incl; eauto. rewrite <- H9. cset_tac; intuition.
    - eapply simErr; [| eapply star_refl|]; eauto. stuck.
  + case_eq (val2bool (V x)); intros.
    eapply simS; try eapply plusO.
    econstructor; eauto. econstructor; eauto.
    rewrite <- H; eauto. eapply IHs1; eauto using agree_on_incl.
    eapply simS; try eapply plusO.
    econstructor 3; eauto. econstructor 3; eauto.
    rewrite <- H; eauto. eapply IHs2; eauto using agree_on_incl.
  + destruct (get_dec L (counted l)) as [[[bE bZ bs]]|].
(*    hnf in H2. exploit H2; eauto. simpl in *. subst bZ. *)
    decide (length Z = length Y).
    unfold simL in H1.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    edestruct AIR5_nth as [?[? [?]]]; try eassumption; dcr.
    simpl in *. repeat get_functional; subst.
    inv H16. hnf in H20. dcr; simpl in *. subst bZ.
    eapply simS; try eapply plusO.
    econstructor; eauto. simpl. congruence.
    econstructor; eauto. simpl. hnf in H21. dcr. simpl in *. subst.
    simpl.
    eapply argsLive_filter_length; eauto.
    simpl in * |- *.
    unfold updE. eapply H21.
    hnf. simpl.
    rewrite <- lookup_list_filter_by_commute.
    exploit argsLive_filter_filter_by; eauto.
    rewrite <- X. eapply lookup_list_agree.
    eapply agree_on_incl; eauto using agree_on_sym.
    eapply filter_incl; eauto.
    congruence.
    rewrite lookup_list_length; congruence.
    subst. rewrite lookup_list_length.
    eapply argsLive_filter_length; eauto.
    eapply simE; try eapply star_refl; eauto; stuck.
    eapply simE; try eapply star_refl; eauto; stuck; eauto.
    edestruct AIR5_length; try eassumption; dcr.
    edestruct get_length_eq; try eassumption.
    simpl in *. repeat get_functional; subst.

  + eapply simE; try eapply star_refl.
    simpl. rewrite H; eauto. simpl.
    stuck. stuck.
  + econstructor; try eapply plusO.
    econstructor; eauto.
    econstructor; eauto.
    simpl. eapply IHs2; eauto.
    - simpl in *; eapply agree_on_incl; eauto.
    - eapply simL_extension; eauto. hnf; intros.
      eapply IHs1; eauto.
      * hnf in H2. subst. simpl.
        eapply agree_on_update_filter'. eauto.
        eapply agree_on_incl; eauto.
      * split; reflexivity.
Qed.
*)

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
