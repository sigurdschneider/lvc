Require Import Util LengthEq AllInRel Map SetOperations.
Require Import Var Val EqDec Computable Var Env IL Annotation AppExpFree.
Require Import Liveness.Liveness LabelsDefined.
Require Import SimF Fresh Filter ReplaceIf ListToStmt.

Set Implicit Arguments.
Unset Printing Records.


Fixpoint compile s {struct s}
  : stmt  :=
  match s with
    | stmtLet x e s => stmtLet x e (compile s)
    | stmtIf x s t => stmtIf x (compile s) (compile t)
    | stmtApp l Y  =>
      let Y' := List.filter NotVar Y in
      let xl := @fresh_list var _
                           fresh
                           (list_union (List.map Op.freeVars Y)) (length Y') in
      list_to_stmt xl Y' (stmtApp l (replace_if NotVar Y (Var ⊝ xl)))
    | stmtReturn x => stmtReturn x
    | stmtFun F t => stmtFun (List.map (fun Zs => (fst Zs, compile (snd Zs))) F) (compile t)
  end.

Instance SR : PointwiseProofRelationF params := {
   ParamRelFP G VL VL' :=   VL = VL' /\ length VL = length G;
   ArgRelFP E E' G Z Z' := Z = Z' /\ length Z = length G
}.

Lemma sim_EAE' r L L' V s
  : labenv_sim Sim (sim r) SR (block_Z ⊝ L) L L'
    -> ❬L❭ = ❬L'❭
    -> sim r Sim (L, V, s) (L',V, compile s).
Proof.
  revert_except s.
  sind s; destruct s; simpl; intros; simpl in * |- *.
  - destruct e.
    + eapply (sim_let_op il_statetype_F); eauto.
    + eapply (sim_let_call il_statetype_F); eauto.
  - eapply (sim_cond il_statetype_F); eauto.
  - case_eq (omap (op_eval V) (List.filter NotVar Y)); intros.
    + destruct (get_dec L (counted l)) as [[[bE bZ bs n]]|].
      * decide (length Y = length bZ).
        -- eapply sim_expansion_closed;
             [
             | eapply star2_refl
             | eapply list_to_stmt_correct;
               eauto using fresh_spec, fresh_list_nodup, fresh_list_spec
             ]; eauto.
           ++ eapply labenv_sim_app; eauto. simpl.
             intros; split; intros; eauto; dcr; subst.
             case_eq (omap (op_eval V) (List.filter IsVar Y)); intros.
             ** exploit (omap_filter_partitions _ _ _ H4 H1).
                intros; repeat cases; eauto.
                exists Yv; repeat split; eauto with len.
                erewrite omap_replace_if.
                --- rewrite <- H7; eauto.
                --- erewrite omap_op_eval_agree; eauto.
                    rewrite <-  update_with_list_agree';
                      eauto using fresh_spec, fresh_list_nodup,
                      fresh_list_spec with len.
                    eapply agree_on_incl.
                    symmetry.
                    eapply update_with_list_agree_minus; eauto.
                    eapply not_incl_minus. reflexivity.
                    symmetry.
                    eapply disj_2_incl.
                    eapply fresh_list_spec; eauto using fresh_spec.
                    eapply list_union_incl; intros; eauto with cset.
                    inv_get.
                    eapply incl_list_union; eauto using map_get_1.
                    eapply fresh_list_nodup; eauto using fresh_spec.
                --- erewrite omap_op_eval_agree; [ eapply H1 | | ].
                    Focus 2.
                    rewrite omap_lookup_vars;
                      eauto using fresh_list_nodup, fresh_spec with len.
                    eapply fresh_list_nodup; eauto using fresh_spec.
                    rewrite <-  update_with_list_agree';
                      eauto using fresh_spec, fresh_list_nodup,
                      fresh_list_spec with len. reflexivity.
                    eapply fresh_list_nodup; eauto using fresh_spec.
             ** exfalso. eapply omap_filter_none in H4. congruence.
           ++ eauto with len.
           ++ eapply fresh_list_nodup; eauto using fresh_spec.
           ++ eapply disj_2_incl.
             eapply fresh_list_spec; eauto using fresh_spec.
             eapply list_union_incl; intros; eauto with cset.
             inv_get. eapply incl_list_union; eauto using map_get_1.
        -- perr.
      * perr.
    + perr.
      erewrite omap_filter_none in def; eauto. congruence.
  - pno_step.
  - pone_step.
    left. eapply IH; eauto 20 with len.
    + rewrite List.map_app.
      eapply labenv_sim_extension_ptw; eauto with len.
      * intros; hnf; intros; inv_get; simpl in *; dcr; subst.
        get_functional. eapply IH; eauto 20 with len.
        rewrite List.map_app. eauto.
      * hnf; intros; simpl in *; subst; inv_get; simpl; eauto.
Qed.

Lemma sim_EAE V s
  : @sim _ statetype_F _ statetype_F bot3 Sim (nil, V, s) (nil,V, compile s).
Proof.
  eapply sim_EAE'; eauto.
  eapply labenv_sim_nil.
Qed.

Lemma EAE_app_expfree s
  : app_expfree (compile s).
Proof.
  sind s; destruct s; simpl; eauto using app_expfree.
  - eapply list_to_stmt_app_expfree.
    intros.
    eapply replace_if_get_inv in H as [A [B [[C D]|[C D]]]].
    + dcr; subst; inv_get; eauto using isVar.
    + subst. cases in C; isabsurd. decide (isVar A); eauto.
      exfalso; eauto.
  - econstructor; intros; inv_get; eauto using app_expfree.
Qed.

Lemma EAE_paramsMatch_app Y'' L f Y Y'
  :  get L (counted f) (❬Y''❭ + ❬Y❭)
     -> disj (of_list Y') (list_union (Op.freeVars ⊝ Y)
                                     ∪ list_union (Op.freeVars ⊝ Y''))
     -> NoDupA _eq Y'
     -> ❬Y'❭ = ❬List.filter NotVar Y❭
     -> paramsMatch
         (list_to_stmt Y'
            (List.filter NotVar Y)
            (stmtApp f (Y'' ++ replace_if NotVar Y (Var ⊝ Y')))) L.
Proof.
  intros. general induction Y.
  - simpl. destruct Y'; isabsurd.
    econstructor; eauto with len.
  - simpl in *; cases.
    destruct Y'; isabsurd; simpl.
    econstructor.
    + rewrite cons_app. rewrite app_assoc.
      eapply IHY.
      * rewrite app_length; simpl. rewrite <- plus_assoc; eauto.
      * rewrite List.map_app. rewrite list_union_app.
        simpl in *.
        rewrite <- union_assoc.
        rewrite disj_app.
        split.
        eapply (disj_incl H0).
        eauto with cset.
        setoid_rewrite list_union_start_swap at 3.
        clear. cset_tac.
        hnf; intros. invt NoDupA.
        rewrite of_list_1 in H3.
        revert H4 H7 H3. clear. cset_tac.
      * eauto.
      * eauto.
    + rewrite cons_app, app_assoc.
      eapply IHY.
      * rewrite app_length; simpl. rewrite <- plus_assoc; eauto.
      * rewrite List.map_app. rewrite list_union_app.
        simpl in *.
        rewrite <- union_assoc.
        rewrite disj_app.
        split.
        eapply (disj_incl H0).
        eauto with cset.
        setoid_rewrite list_union_start_swap at 3.
        clear. cset_tac.
        eapply disj_2_incl; eauto.
        rewrite list_union_start_swap.
        clear; cset_tac.
      * eauto.
      * eauto.
Qed.

Lemma EAE_paramsMatch s L
  : paramsMatch s L
    -> paramsMatch (compile s) L.
Proof.
  intros.
  general induction H; simpl; eauto using paramsMatch.
  - eapply (EAE_paramsMatch_app nil); eauto.
    + simpl. eapply disj_2_incl.
      eapply fresh_list_spec; eauto using fresh_spec with cset.
      eauto with cset.
    + eapply fresh_list_nodup; eauto using fresh_spec.
    + eauto with len.
  - econstructor; intros; inv_get; rewrite !map_map in *; simpl; eauto.
Qed.

Lemma freeVars_filter_Var Y
  : list_union (Op.freeVars ⊝ Y) [=]
               list_union (Op.freeVars ⊝ List.filter NotVar Y)
               ∪ list_union (Op.freeVars ⊝ List.filter IsVar Y).
Proof.
  general induction Y; simpl; norm_lunion; eauto with cset.
  - repeat cases; simpl; norm_lunion; try now (exfalso; eauto).
    + rewrite IHY. rewrite !union_assoc. reflexivity.
    + rewrite IHY. clear IHY n.
      cset_tac.
Qed.

Ltac norm_lunion :=
 repeat match goal with
      | [ |- context [ fold_left union ?A ?B ]] =>
        match B with
          | empty => fail 1
          | _ => rewrite (list_union_start_swap A B)
        end
      | [ H : context [ fold_left union ?A ?B ] |- _ ] =>
        match B with
          | empty => fail 1
          | _ => rewrite (list_union_start_swap A B) in H
        end
    end.

Ltac clr_prtct :=
        repeat match goal with
               | [ H : protected_setin_fnc _ _ |- _ ] => clear H
               | [ H : protected _ |- _ ] => clear H
               end.

Lemma freeVars_replaceIf Y (xl:list var) (Len:❬List.filter NotVar Y❭ = ❬xl❭)
      (Disj:disj (of_list xl) (list_union (Op.freeVars ⊝ Y)))
  : list_union (Op.freeVars ⊝ replace_if NotVar Y (Var ⊝ xl)) \ of_list xl
               [=] list_union (Op.freeVars ⊝ List.filter IsVar Y).

Proof.
  rewrite freeVars_filter_Var in Disj.
  general induction Y; simpl in *; eauto with cset.
  - cset_tac.
  - do 2 cases; simpl in *; try now (exfalso; eauto).
    + destruct xl; simpl in *; clear_trivial_eqs;
      norm_lunion; simpl in *.
      * rewrite minus_dist_union.
        setoid_rewrite minus_minus_add at 2.
        rewrite IHY; eauto.
        -- revert Disj; clear; cset_tac.
        -- eapply disj_incl; eauto.
           eauto with cset.
           clear. cset_tac.
    + norm_lunion.
      rewrite minus_dist_union.
      rewrite (IHY (xl)); eauto.
      * revert Disj; clear; cset_tac.
      * eapply disj_incl; eauto.
        clear; cset_tac.
Qed.


Lemma EAE_freeVars s
  : freeVars (compile s) [=] freeVars s.
Proof.
  sind s; destruct s; simpl;
    try rewrite !IH; eauto with cset.
  - rewrite list_to_stmt_freeVars; eauto with len.
    + simpl.
      setoid_rewrite freeVars_filter_Var at 5.
      eapply eq_union_lr; eauto.
      rewrite freeVars_replaceIf; eauto.
      rewrite fresh_list_length; eauto.
      eapply fresh_list_spec, fresh_spec.
    + eapply disj_2_incl.
      eapply fresh_list_spec.
      eapply fresh_spec.
      setoid_rewrite freeVars_filter_Var at 2; eauto with cset.
  - eapply eq_union_lr; eauto.
    eapply list_union_eq; eauto with len.
    intros; inv_get; simpl.
    rewrite IH; eauto.
Qed.

(*
Fixpoint compile_live (LV:list (set var)) (s:stmt) (a:ann (set var)) : ann (set var) :=
  match s, a with
  | stmtLet x e s, ann1 lv an as a =>
    let an' := compile_live LV s an in
    ann1 (getAnn an' \ singleton x) an'
  | stmtIf e s t, ann2 lv ans ant =>
    let ans' := compile_live LV s ans in
    let ant' := compile_live LV t ant in
    ann2 (getAnn ans' ∪ getAnn ant') ans' ant'
  | stmtApp f Y, ann0 lv =>
    let lv := nth (counted f) LV ∅ in
    ann0 (list_union (Op.freeVars ⊝ Y) ∪ lv)
  | stmtReturn e, ann0 lv => ann0 (Op.freeVars e)
  | stmtFun F t, annF lv ans ant =>
    let ans' := zip (fun Zs a => compile_live (getAnn ⊝ ans ++ LV) (snd Zs) a) F ans in
    annF lv ans' (compile_live (getAnn ⊝ ans ++ LV) t ant)
  | _, a => a
  end.
*)

(*
Fixpoint live_for_stmts (Y:list op) (xl:list var) (lv:set var) : ann (set var) :=
  match Y, xl with
  | e::Y, x::xl =>
    let an' := live_for_stmts Y xl lv in
    ann1 (Op.freeVars e ∪ (getAnn an' \ singleton x)) an'
  | _, _ => ann0 lv
  end.

Fixpoint compile_live (LV:list (set var)) (s:stmt) (a:ann (set var)) : ann (set var) :=
  match s, a with
  | stmtLet x e s, ann1 lv an as a => ann1 lv (compile_live LV s an)
  | stmtIf e s t, ann2 lv ans ant =>
    ann2 lv (compile_live LV s ans) (compile_live LV t ant)
  | stmtApp f Y, ann0 lv =>
    let lv_f := nth (counted f) LV ∅ in
    let Y' := (List.filter NotVar Y) in
    let xl := (fresh_list fresh (list_union (List.map Op.freeVars Y)) (length Y')) in
    let lv' := list_union (Op.freeVars ⊝ (List.filter IsVar Y)) ∪ of_list xl ∪ lv_f in
    setTopAnn (live_for_stmts Y' xl lv') lv
  | stmtReturn e, ann0 lv => ann0 lv
  | stmtFun F t, annF lv ans ant =>
    let ans' := zip (fun Zs a => compile_live (getAnn ⊝ ans ++ LV) (snd Zs) a) F ans in
    annF lv ans' (compile_live (getAnn ⊝ ans ++ LV) t ant)
  | _, a => a
  end.

Lemma compile_live_getAnn LV s a
  : getAnn (compile_live LV s a) [=] getAnn a.
Proof.
  general induction s; destruct a; simpl; eauto.
  rewrite getAnn_setTopAnn; eauto.
Qed.

Lemma incl_set_right (X : Type) `{H : OrderedType X} s t
  : s [=] t -> t ⊆ s.
Proof.
  intros. rewrite H0. reflexivity.
Qed.

Lemma EAE_live i ZL Lv s lv
  : live_sound i ZL Lv s lv
    -> live_sound i ZL Lv (compile s) (compile_live Lv s lv).
Proof.
  intros.
  general induction H; simpl;
    eauto 20 using live_sound, compile_live_getAnn.
  - econstructor; eauto; rewrite compile_live_getAnn; eauto.
  - econstructor; eauto; rewrite compile_live_getAnn; eauto.
  -
  - econstructor; eauto.
    + rewrite !map_map; simpl.
      eapply live_sound_monotone; eauto.
      eapply PIR2_get; intros; inv_get; eauto with len.
      rewrite map_zip in H5.
      eapply get_app_cases in H6. destruct H6; dcr; inv_get.
      rewrite get_app_lt in H5; eauto with len. inv_get.
      rewrite compile_live_getAnn. eauto.
      rewrite get_app_ge in H5; eauto with len.
      rewrite zip_length2 in H5; eauto. rewrite map_length in H7.
      rewrite H0 in H5. inv_get. eauto.
      rewrite zip_length2; eauto. rewrite map_length in H8. omega.
    + eauto with len.
    + intros; inv_get. simpl.
      rewrite !map_map; simpl.
      eapply live_sound_monotone; eauto.
      eapply PIR2_get; intros; inv_get; eauto with len.
      rewrite map_zip in H5.
      eapply get_app_cases in H8. destruct H8; dcr; inv_get.
      rewrite get_app_lt in H5; eauto with len. inv_get.
      rewrite compile_live_getAnn. eauto.
      rewrite get_app_ge in H5; eauto with len.
      rewrite zip_length2 in H5; eauto. rewrite map_length in H9.
      rewrite H0 in H5. inv_get. eauto.
      rewrite zip_length2; eauto. rewrite map_length in H10. omega.
    + intros; inv_get; simpl.
      exploit H3; eauto; dcr.
      destruct i; simpl in *; rewrite compile_live_getAnn; eauto.
    + rewrite compile_live_getAnn; eauto.
Qed.
*)