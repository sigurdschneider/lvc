Require Import CSet Le.

Require Import Plus Util AllInRel InRel Map MapUpdate MapDefined.
Require Import Val Var Envs IL NoParams Annotation SimI Fresh.
Require Import Liveness.Liveness Status InfinitePartition AppExpFree.
Require compcert.lib.Parmov.

Set Implicit Arguments.
Unset Printing Records.

(** * Parallel Moves

   This code is based on the ril-cv-12 repo and the validator
   part its initial version was developed by Tobias Tebbi.
*)

Definition moves_source_set (p:Parmov.moves var) : set var
  := fold_right (fun p s => s \ singleton (snd p) ∪ singleton (fst p)) ∅ p.

Definition moves_dest_set (p:Parmov.moves var) : set var
  := of_list (snd ⊝ p).

Lemma moves_source_set_app mv1 mv2
  : moves_source_set (mv1 ++ mv2) [=]
                     moves_source_set mv1 ∪ moves_source_set mv2 \ moves_dest_set mv1.
Proof.
  unfold moves_dest_set.
  general induction mv1; simpl.
  - cset_tac.
  - rewrite IHmv1. clear. cset_tac.
Qed.

Lemma moves_source_set_incl p
  : moves_source_set p ⊆ of_list (fst ⊝ p).
Proof.
  general induction p; simpl.
  - eauto with cset.
  - rewrite IHp; clear. cset_tac.
Qed.

Lemma of_list_rev X `{OrderedType X} L
  : of_list (rev L) [=] of_list L.
Proof.
  general induction L; simpl; eauto.
  rewrite of_list_app; simpl; rewrite IHL.
  cset_tac.
Qed.

Section ParmovSourceSet.
  Import Parmov.

  Definition st_source_set (st:state var) :=
    match st with
    | State mv1 mv2 mvs => of_list (fst ⊝ (mv1 ++ mv2)) \ moves_dest_set mvs ∪ moves_source_set (rev mvs)
    end.

  Tactic Notation "stsmpl" :=
    repeat (rewrite List.map_app || rewrite of_list_app
            || simpl || rewrite moves_source_set_app || unfold moves_dest_set || rewrite map_rev
            || rewrite of_list_rev).

  Lemma dtransition_source_set t st st'
    : dtransition var t st st' ->
      st_source_set st' ⊆ st_source_set st.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto; stsmpl.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
    - cset_tac.
  Qed.

  Lemma dtransitions_source_set t st st'
    : dtransitions var t st st' ->
      st_source_set st' ⊆ st_source_set st.
  Proof.
    intros TR.
    general induction TR; simpl in *; eauto using dtransition_source_set.
    - etransitivity; eauto.
  Qed.

  Lemma parmove_src_set t mu
    : moves_source_set (parmove var var_dec t mu) ⊆ of_list (fst ⊝ mu).
  Proof.
    pose proof (parmove_aux_transitions _ var_dec t (State _ mu nil nil)).
    eapply dtransitions_source_set in H.
    simpl in *. revert H; stsmpl.
    unfold parmove. cset_tac.
  Qed.

End ParmovSourceSet.

Lemma eq_dec_comm X (x y:X)
  : { x = y } + { ~ x = y }
    -> { y = x } + { ~ y = x } .
Proof.
  firstorder.
Qed.

Notation "f [ // p ]" := (@Parmov.exec_seq var var_dec _ p f) (at level 29, left associativity).

Lemma Parmov_update_eq M x y
  : Parmov.update var var_dec (؟ val) x y M = M [x <- y].
Proof.
  unfold Parmov.update, update.
  eapply FunctionalExtensionality.functional_extensionality.
  intros. repeat cases; eauto. eapply var_eq_eq in COND. exfalso; eauto.
Qed.

Section GlueCode.
  Fixpoint list_to_stmt (p : list (var * var)) (s : stmt) {struct p} : stmt :=
    match p with
      | nil => s
      | (x, y) :: p' => stmtLet y (Operation (var_to_op x)) (list_to_stmt p' s)
    end.

  Lemma list_to_stmt_correct (p:Parmov.moves var) s (M:onv val) K
        (Def:defined_on (moves_source_set p) M)
    : star2 I.step (K, M, list_to_stmt p s) nil
        (K, M [ // p ], s).
  Proof.
    general induction p.
    - firstorder using star2.
    - destruct a as [x y]. simpl in *.
      edestruct (Def x); eauto with cset.
      exploit (var_to_op_correct M x).
      eapply star2_silent.
      + constructor; eauto.
      + rewrite H.
        rewrite Parmov_update_eq.
        eapply IHp; eauto using defined_on_update_some,
                    defined_on_incl with cset.
  Qed.

  Lemma exec_par_eq p (E:onv val)
    : Parmov.exec_par var var_dec _ p E =
      E [ snd ⊝ p <-- lookup_list E (fst ⊝ p) ].
  Proof.
    general induction p; simpl; eauto.
    cases; subst; simpl.
    rewrite IHp. simpl.
    intros. eapply Parmov_update_eq.
  Qed.

  Lemma NoDup_is_mill m
    : NoDupA eq (snd ⊝ m)
      -> Parmov.is_mill var m.
  Proof.
    intros ND. hnf. unfold Parmov.dests.
    general induction m; invt NoDupA; simpl;
      eauto using Coqlib.list_norepet.
    econstructor; eauto.
    intro; eapply H1.
    eapply In_InA; eauto.
  Qed.

  Lemma list_to_stmt_correct' D (m:Parmov.moves var) (M M':onv val) x
        (ND:NoDupA eq (snd ⊝ m))
        (NOTIN : Parmov.move_no_temp var (fun _ => x) m)
    : agree_on eq (D \ singleton x)
               (M[ // Parmov.parmove var var_dec (fun _ => x) m])
               (M [ snd ⊝ m <-- lookup_list M (fst ⊝ m) ]).
  Proof.
    intros.
    exploit (@Parmov.parmove_correctness var var_dec (fun _ => x) (option val) m).
    - eauto.
    - eapply NoDup_is_mill; eauto.
    - rewrite <- exec_par_eq.
      hnf; intros.
      rewrite <- H.
      + reflexivity.
      + hnf; cset_tac.
  Qed.

End GlueCode.

Section Implementation.
Fixpoint onlyVars (Y:args) : params :=
  match Y with
    | nil => nil
    | (Var x)::Y => x::onlyVars Y
    | _::Y => onlyVars Y
  end.
(*
Lemma onlyVars_defined (E:onv val) Y Y' v
  : onlyVars Y = Y'
    -> omap (op_eval E) Y = Some v
    -> forall x, x ∈ of_list Y' -> E x <> None.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - inv H; simpl in *. cset_tac; intuition.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *.
    cset_tac; congruence.
Qed.

Lemma onlyVars_defined_on (E:onv val) Y Y' v
  : onlyVars Y = Success Y'
    -> omap (op_eval E) Y = Some v
    -> defined_on (of_list Y') E.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  - inv H; simpl in *. hnf; cset_tac.
  - destruct a; isabsurd. monadS_inv H. monad_inv H0.
    simpl in * |- *.
    exploit IHY; eauto.
    hnf; cset_tac.
Qed.
 *)

Lemma onlyVars_lookup (E:onv val) Y v
      (AEF:forall (n : nat) (y : op), get Y n y -> isVar y)
  : omap (op_eval E) Y = Some v
    -> lookup_list E (onlyVars Y) = List.map Some v.
Proof.
  intros. general induction Y; simpl in * |- *; eauto.
  monad_inv H.
  exploit AEF as IV; eauto using get. inv IV; eauto; simpl.
  simpl in *.
  f_equal; eauto. eapply IHY; eauto using get.
Qed.


Lemma onlyVars_length Y
      (AEF:forall (n : nat) (y : op), get Y n y -> isVar y)
  : ❬onlyVars Y❭ = ❬Y❭.
Proof.
  general induction Y; simpl; eauto.
  exploit AEF; eauto using get. inv H; simpl.
  rewrite IHY; eauto using get.
Qed.

Lemma onlyVars_eq Y
      (AEF:forall (n : nat) (y : op), get Y n y -> isVar y)
  : Y = Var ⊝ onlyVars Y.
Proof.
  general induction Y; simpl; eauto.
  exploit AEF; eauto using get. inv H; simpl.
  rewrite <- IHY; eauto using get.
Qed.

Hint Resolve onlyVars_length : len.


Fixpoint lower (p:inf_partition var) (DL:〔⦃var⦄ * params〕) s (an:ann (set var))
  : stmt :=
  match s, an with
    | stmtLet x e s, ann1 lv ans => stmtLet x e (lower p DL s ans)
    | stmtIf x s t, ann2 lv ans ant => stmtIf x (lower p DL s ans) (lower p DL t ant)
    | stmtApp l Y, ann0 lv  =>
      let '(lv', Z) := nth_default (∅, nil) DL (counted l) in
      let x := least_fresh_P (part_2 p) (lv' ∪ lv) in
      let mvs := Parmov.parmove2 var var_dec (fun _ => x) (onlyVars Y) Z in
      list_to_stmt mvs (stmtApp l nil)
    | stmtReturn x, ann0 lv => stmtReturn x
    | stmtFun F t, annF lv ans ant =>
      let DL' := pair ⊜ (getAnn ⊝ ans) (fst ⊝ F) in
      let s' := zip (fun Zs a => lower p (DL' ++ DL) (snd Zs) a) F ans in
      let t' := lower p (DL' ++ DL) t ant in
      (stmtFun ((fun s => (nil, s)) ⊝ s') t')
    | _, _ => s
  end.

Inductive approx
: list (set var) -> list I.block -> list I.block -> ⦃var⦄ -> I.block -> I.block -> Prop :=
  approxI L L' DL Z s s' lv n p
  (al:ann (set var))
  (LS:live_sound Imperative (I.block_Z ⊝ L) DL s al)
  (AL:(of_list Z) ⊆ lv)
  (AEF:app_expfree s)
  (ND:NoDupA eq Z)
  (INCL:getAnn al \ of_list Z ⊆ lv)
  (spm:lower p (zip pair DL (I.block_Z ⊝ L)) s al = s')
  : approx DL L L' lv (I.blockI Z s n) (I.blockI nil s' n).


Lemma omap_var_defined_on Za E vl
: omap (op_eval E) (List.map Var Za) = Some vl
  -> defined_on (of_list Za) E.
Proof.
  intros. general induction Za; simpl.
  - hnf; intros. cset_tac.
  - simpl in *.
    monad_inv H.
    exploit IHZa; eauto.
    hnf; intros. cset_tac.
Qed.

Lemma correct p Lv L L' s (E E':onv val) (al: ann (set var))
      (LS:live_sound Imperative (I.block_Z ⊝ L) Lv s al)
      (AEF:app_expfree s)
 (LA:inRel approx Lv L L')
 (EEQ:agree_on eq (getAnn al) E E')
  : sim bot3 Sim (L,E,s) (L', E', lower p (zip pair Lv (I.block_Z ⊝ L))  s al).
Proof.
  revert_all. pcofix pmSim_sim; intros.
  inv LS; inv AEF; simpl in *.
  - invt live_exp_sound.
    + eapply (sim_let_op il_statetype_I);
        eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
    + eapply (sim_let_call il_statetype_I); eauto 10 using agree_on_update_same, agree_on_incl.
        erewrite <- omap_op_eval_live_agree; eauto. eapply agree_on_sym; eauto.
  - eapply (sim_cond il_statetype_I);
      eauto 20 using op_eval_live, agree_on_update_same, agree_on_incl.
  - rewrite nth_default_eq. erewrite get_nth; eauto using zip_get; simpl.
    inRel_invs.
    inv_get. simpl in *.
    case_eq (omap (op_eval E) Y); intros.
    + exploit onlyVars_length as Len; eauto.
      exploit (Parmov.srcs_dests_combine _ (onlyVars Y) Z0) as Eq; eauto with len.
      destruct Eq as [SrcEq DstEq]. unfold Parmov.srcs, Parmov.dests in *.
      exploit omap_op_eval_live_agree; try eassumption.
      exploit (@list_to_stmt_correct
                 (Parmov.parmove2 var var_dec (fun _ => least_fresh_P (part_2 p) (blv ∪ lv)) (onlyVars Y) Z0)
                 (stmtApp l nil) E' L').

      unfold Parmov.parmove2.
      rewrite parmove_src_set. rewrite SrcEq.
      rewrite (onlyVars_eq H5) in H6.
      eapply omap_var_defined_on; eauto.
      pfold. eapply SimSilent.
      * eapply plus2O. econstructor; eauto. simpl. reflexivity.
      * eapply star2_plus2_plus2 with (A:=nil) (B:=nil); eauto.
        eapply plus2O. econstructor; eauto. reflexivity. reflexivity.
      * right; eapply pmSim_sim; try eapply LA1; eauto; simpl.
        -- eapply (inRel_drop LA H4).
        -- assert (getAnn al ⊆ blv) by eauto with cset.
           symmetry. etransitivity.
           eapply agree_on_incl.
           eapply (@list_to_stmt_correct' (getAnn al)); eauto.
           ++ rewrite DstEq. eauto.
           ++ assert (of_list (onlyVars Y) ⊆ lv). {
               eapply Ops.freeVars_live_list in H3.
               rewrite <- H3. rewrite (onlyVars_eq H5) at 2.
               rewrite of_list_freeVars_vars. reflexivity.
             }
             hnf; intros ? ? IN.
             split.
             eapply in_combine_l in IN.
             hnf. intros.
             intro; subst.
             eapply In_InA in IN.
             eapply of_list_1 in IN.
             rewrite H9 in IN. rewrite (incl_right _ lv blv) in IN at 2.
             eapply least_fresh_P_full_spec in IN; eauto. eauto.
             eapply in_combine_r in IN.
             hnf. intros.
             intro; subst.
             eapply In_InA in IN.
             eapply of_list_1 in IN.
             rewrite AL in IN. rewrite (incl_left _ blv lv) in IN at 2.
             eapply least_fresh_P_full_spec in IN; eauto. eauto.
           ++ rewrite disj_minus_eq; eauto.
             rewrite H8; clear.
             intro; hnf; intros.
             eapply (incl_left _ blv lv) in H.
             eapply (least_fresh_P_full_spec (part_2 p) (blv ∪ lv)).
             cset_tac.
           ++ rewrite SrcEq, DstEq.
             erewrite onlyVars_lookup; eauto.
             eapply update_with_list_agree; eauto with len.
             symmetry.
             eapply agree_on_incl; eauto. eauto with cset.
    + perr.
  - pno_step. simpl. eauto using op_eval_live.
  - pone_step. right.
    rewrite <- zip_app in *; eauto with len.
    assert (EQ:fst ⊝ F ++ I.block_Z ⊝ L = I.block_Z ⊝ (mapi I.mkBlock F ++ L)). {
      unfold mapi. generalize 0.
      clear. general induction F; simpl; f_equal; eauto.
    }
    rewrite EQ in *.
    eapply pmSim_sim; try eapply H; eauto using agree_on_incl.
    econstructor; eauto.
    eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
    intros; inv_get.
    econstructor; eauto.
    + exploit H2; eauto.
    + eapply H2; eauto.
    + simpl. reflexivity.
Qed.

End Implementation.

Lemma list_to_stmt_noParams pm s
      (NP:noParams s)
  : noParams (list_to_stmt pm s).
Proof.
  general induction pm; simpl;
    repeat let_pair_case_eq; eauto using noParams.
Qed.

Lemma pm_lower_noParams p ZL Lv s al
      (LS:live_sound Imperative ZL Lv s al)
  : noParams (lower p (zip pair Lv ZL) s al).
Proof.
  general induction LS; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; eauto using noParams.
  - eauto using list_to_stmt_noParams, noParams.
  - econstructor; intros; inv_get; simpl;
      try rewrite <- zip_app; eauto using noParams with len.
Qed.
