Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env IL Sim Coherence Fresh Annotation DecSolve SetOperations LabelsDefined.

Require Import Liveness.Liveness Eqn ValueOpts RenamedApart.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint copyPropagate (ϱ:var -> var) (s:stmt) : stmt :=
  match s with
   | stmtLet x (Operation e) s =>
     if [ isVar e] then
       stmtLet x (Operation e) (copyPropagate (ϱ[x <- ϱ (getVar e)]) s)
     else
       stmtLet x (Operation (rename_op ϱ e)) (copyPropagate (ϱ[x <- x]) s)
   | stmtLet x (Call f Y) s =>
     stmtLet x (Call f (List.map (rename_op ϱ) Y)) (copyPropagate (ϱ[x <- x]) s)
   | stmtIf e s1 s2 => stmtIf (rename_op ϱ e)
                             (copyPropagate ϱ s1)
                             (copyPropagate ϱ s2)
   | stmtApp l Y => stmtApp l (List.map (rename_op ϱ) Y)
   | stmtReturn e => stmtReturn (rename_op ϱ e)
   | stmtFun F s2 =>
     stmtFun (List.map (fun '(Z, s) => (Z, copyPropagate (ϱ[Z <-- Z]) s)) F) (copyPropagate ϱ s2)
   end.

Definition cp_eqn (ϱ:var -> var) (x:var) := EqnApx (Var x) (Var (ϱ x)).

Instance cq_eqn_proper f
  : Proper (_eq ==> _eq) (cp_eqn f).
Proof.
  unfold Proper, respectful, _eq, cp_eqn; intros; subst. simpl in *; subst.
  reflexivity.
Qed.

Lemma cp_moreDefined ϱ D e
  : Op.freeVars e[<=]D
    -> entails (map (cp_eqn ϱ) D) {EqnApx e (rename_op ϱ e)}.
Proof.
  general induction e; simpl.
  - eapply entails_eqns_apx_refl.
  - eapply entails_subset. simpl in *.
    rewrite <- H. cset_tac.
  - simpl in H.
    exploit (IHe ϱ); eauto.
    hnf; intros. eapply H0 in H1.
    eapply satisfies_single.
    eapply satisfies_single' in H1.
    simpl in *. inv H1; simpl.
    + econstructor.
    + reflexivity.
  - simpl in H.
    exploit (IHe1 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac.
    exploit (IHe2 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac.
    hnf; intros.
    specialize (H0 _ H2). specialize (H1 _ H2).
    eapply satisfies_single.
    eapply satisfies_single' in H0.
    eapply satisfies_single' in H1.
    simpl in *. inv H0; inv H1; simpl; try econstructor.
    reflexivity.
Qed.


Lemma cp_moreDefinedArgs ϱ D Y
  : list_union (List.map Op.freeVars Y) [<=]D
    -> entails (map (cp_eqn ϱ) D) (list_EqnApx Y (List.map (rename_op ϱ) Y)).
Proof.
  general induction Y; simpl.
  - eapply entails_empty.
  - assert (Op.freeVars a ⊆ D). {
      rewrite <- H. eapply incl_list_union.
      - simpl; econstructor.
      - reflexivity.
    }
    exploit (cp_moreDefined ϱ); eauto.
    unfold list_EqnApx; simpl.
    eapply entails_union'.
    rewrite add_union_singleton; reflexivity.
    eauto.
    eapply IHY.
    rewrite <- H. simpl.
    setoid_rewrite (list_union_start_swap) at 2.
    cset_tac.
Qed.


Lemma cp_eqns_agree_incl E E' lv
: agree_on eq lv E E'
  -> map (cp_eqn E) lv ⊆ map (cp_eqn E') lv.
Proof.
  intros; hnf; intros.
  eapply map_iff in H0; eauto. dcr.
  eapply map_iff; eauto.
  eexists; split; eauto.
  unfold cp_eqn; rewrite <- H; eauto.
Qed.


Lemma cp_eqns_agree E E' lv
: agree_on eq lv E E'
  -> map (cp_eqn E) lv [=] map (cp_eqn E') lv.
Proof.
  intros. eapply incl_eq; eauto using cp_eqns_agree_incl.
  symmetry in H; eauto using cp_eqns_agree_incl.
Qed.


Lemma cp_eqns_add_update ϱ D x y
: x ∉ D
  -> map (cp_eqn (ϱ [x <- y])) ({x; D })
            [=] {EqnApx (Var x) (Var y); map (cp_eqn ϱ) D}.
Proof.
  intros.
  rewrite map_add; eauto.
  unfold cp_eqn at 1.
  lud; isabsurd.
  rewrite cp_eqns_agree with (E':=ϱ).
  reflexivity.
  eapply agree_on_update_dead; eauto.
Qed.


Lemma cp_eqns_freeVars ϱ D
: lookup_set ϱ D ⊆ D
  -> eqns_freeVars (map (cp_eqn ϱ) D) ⊆ D.
Proof.
  intros. unfold eqns_freeVars.
  hnf; intros. eapply incl_fold_union in H0.
  destruct H0 as [[? [? ?]]|]; isabsurd.
  eapply map_iff in H0; eauto using freeVars_Proper.
  dcr.
  eapply map_iff in H3; eauto. dcr.
  invc H5. unfold cp_eqn in *; simpl in *.
  rewrite H4 in H1. cset_tac'.
  eapply H. eapply lookup_set_spec; eauto.
Qed.


Lemma single_in_cp_eqns x ϱ D
: x ∈ D
  -> {{ EqnApx (Var x) (Var (ϱ x)) }} ⊆ map (cp_eqn ϱ) D.
Proof.
  intros. hnf; intros.
  eapply map_iff; eauto.
  eexists x; split; eauto. cset_tac.
Qed.


Lemma entails_cp_eqns_trivial ϱ Z
: entails {} (map (cp_eqn (ϱ [Z <-- Z])) (of_list Z)).
Proof.
  hnf; intros. hnf; intros.
  eapply map_iff in H0; eauto.
  dcr. invc H3.
  unfold cp_eqn.
  rewrite lookup_update_same; eauto.
  simpl; reflexivity.
Qed.


Lemma entails_eqns_trans' Gamma e e' e''
: EqnEq e e' ∈ Gamma
  -> EqnApx e' e'' ∈ Gamma
  -> entails Gamma {EqnApx e e''}.
Proof.
  intros. hnf; intros.
  hnf; intros. cset_tac'. rewrite <- H2.
  simpl. exploit (H1 _ H); eauto.
  exploit (H1 _ H0); eauto.
  simpl in *. inv H3; inv H4; try now (econstructor; eauto).
  - congruence.
  - econstructor; eauto. congruence.
Qed.


Lemma entails_cpenv ϱ x v (D:set var)
      (IN:v ∈ D)
  : entails (singleton (EqnEq (Var x) (Var v)) ∪ map (cp_eqn ϱ) D)
            {EqnApx (Var x) (Var (ϱ v))}.
Proof.
  eapply entails_eqns_trans'. cset_tac. cset_tac.
Qed.

Lemma lookup_set_id_add_upd_incl X `{OrderedType X} ϱ (x:X) D
      `{Proper _ (_eq ==> _eq) ϱ}
      (NOTIN:x ∉ D)
      (Incl:lookup_set ϱ D [<=] D)
  : lookup_set (ϱ [x <- x]) {x; D} [<=] {x; D}.
Proof.
  rewrite lookup_set_add_update; eauto.
  rewrite Incl. reflexivity.
Qed.

Lemma lookup_set_rename_op_incl e ϱ (D:set var)
      (Incl:lookup_set ϱ D [<=] D)
      (FV:Op.freeVars e [<=] D)
  : Op.freeVars (rename_op ϱ e) [<=] D.
Proof.
  rewrite rename_op_freeVars; eauto.
  rewrite <- Incl. eapply lookup_set_incl; eauto.
Qed.


Lemma lookup_set_rename_op_list_incl Y ϱ (D:set var)
      (Incl:lookup_set ϱ D [<=] D)
      (FV:list_union (Op.freeVars ⊝ Y) [<=] D)
  : list_union (Op.freeVars ⊝ rename_op ϱ ⊝ Y) ⊆ D.
Proof.
  rewrite rename_op_list_freeVars; eauto.
  rewrite <- Incl. eapply lookup_set_incl; eauto.
Qed.

Local Hint Resolve lookup_set_id_add_upd_incl lookup_set_rename_op_incl
      lookup_set_rename_op_list_incl.


Lemma copyPropagate_sound_eqn ZL Delta s ang ϱ
      (RA:renamedApart s ang)
      (Incl: lookup_set ϱ (fst (getAnn ang)) ⊆ (fst (getAnn ang)))
(LD: labelsDefined s (length ZL))
(EQE: (forall n a, get Delta n a -> a [=] ∅))
 (Len1: ❬ZL❭ = ❬Delta❭)
  : eqn_sound ZL Delta
              s (copyPropagate ϱ s)
              (map (cp_eqn ϱ) (fst (getAnn ang)))
              ang.
Proof.
  intros. general induction RA; invt labelsDefined; simpl in *; pe_rewrite.
  - destruct e.
    + cases.
      * inv COND; simpl in *.
        econstructor.
        -- eapply eqn_sound_entails_monotone; eauto.
           ++ eapply IHRA; eauto.
             rewrite lookup_set_add_update; eauto.
             assert (v ∈ D) by cset_tac.
             pose proof (lookup_set_single H3 Incl); eauto.
             revert Incl H4. clear_all. cset_tac.
           ++ rewrite cp_eqns_add_update; eauto.
             rewrite add_union_singleton.
             eapply entails_union'.
             ** rewrite add_union_singleton; reflexivity.
             ** eapply entails_cpenv; eauto.
             ** eapply entails_monotone; [ reflexivity | ].
                cset_tac.
        -- hnf; intros.
           eapply satisfies_single.
           simpl. reflexivity.
      *  econstructor; eauto.
         eapply eqn_sound_entails_monotone; eauto.
         -- rewrite cp_eqns_add_update; eauto.
            eapply entails_union'.
            ++ rewrite add_union_singleton; reflexivity.
            ++ eapply entails_eqns_apx_refl.
            ++ eapply entails_monotone. reflexivity.
              cset_tac.
         -- eapply cp_moreDefined; eauto.
    + econstructor.
      * eapply eqn_sound_entails_monotone; eauto.
        rewrite cp_eqns_add_update; eauto.
        eapply entails_union'.
        rewrite add_union_singleton; reflexivity.
        eapply entails_eqns_apx_refl.
        eapply entails_subset; eauto with cset.
      * eauto using cp_moreDefinedArgs.
      * simpl in *.
        rewrite rename_op_list_freeVars; eauto.
        rewrite H0; eauto.
      * eauto with len.
  - econstructor; intros.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply entails_monotone; eauto.
      reflexivity. cset_tac.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply entails_monotone; try reflexivity; cset_tac; intuition.
    + eapply cp_moreDefined; eauto.
  - econstructor; eauto using cp_moreDefined.
  - edestruct get_in_range as [a ?]; eauto.
    inv_get.
    econstructor; eauto with len.
    + erewrite (EQE _ _ H1). eapply entails_empty.
    + eapply cp_moreDefinedArgs; eauto.
  - eapply EqnFun with (ΓF:= List.map (fun _=> ∅) F);
      eauto with len.
    + intros; inv_get; eauto.
    + intros; inv_get. exploit H0; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      eapply (H1 _ _ _ H6 H11); eauto.
      * edestruct H2; eauto; dcr; simpl in *.
        rewrite H9.
        rewrite lookup_set_union; eauto.
        rewrite update_with_list_lookup_set_incl; eauto; try reflexivity.
        rewrite lookup_set_update_with_list_in_union; eauto.
        simpl in *. rewrite Incl.
        clear_all; cset_tac.
      * intros. eapply get_app_cases in H9. destruct H9; dcr.
        -- inv_get; eauto.
        -- eapply EQE; eauto.
      * eauto with len.
      * edestruct H2; eauto; dcr; simpl in *.
        rewrite H9.
        rewrite map_app; eauto.
        rewrite (@cp_eqns_agree (ϱ [Z <-- Z]) ϱ D).
        -- eapply entails_union'.
           ++ reflexivity.
           ++ eapply entails_monotone.
             eapply entails_cp_eqns_trivial. eapply incl_left.
           ++ eapply entails_monotone. reflexivity. eapply incl_right.
        -- assert (EQ:D [=] D \ of_list Z). {
             revert H15. clear_all; cset_tac.
           }
           rewrite EQ. eapply update_with_list_agree_minus; eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHRA; simpl; eauto.
      * intros ? ? GET. eapply get_app_cases in GET. destruct GET; dcr.
        -- inv_get; eauto.
        -- eapply EQE; eauto.
      * eauto with len.
      * pe_rewrite. reflexivity.
    + intros; inv_get.
      eapply incl_empty.
Qed.


Lemma copyPropagation_renamedApart s ang ϱ
      (RA:renamedApart s ang)
      (Incl: lookup_set ϱ (fst (getAnn ang)) ⊆ (fst (getAnn ang)))
  : renamedApart (copyPropagate ϱ s) ang.
Proof.
  general induction RA; simpl in *; pe_rewrite; eauto using renamedApart.
  - destruct e; simpl in *.
    + cases.
      * inv COND. econstructor; eauto. eapply IHRA. simpl.
        rewrite lookup_set_add_update; eauto.
        simpl in *.
        assert (v ∈ D) by cset_tac.
        pose proof (lookup_set_single H3 Incl); eauto.
        revert Incl H4. clear_all. cset_tac.
      * econstructor; simpl; eauto.
    + econstructor; simpl; eauto.
  - econstructor; intros; inv_get; eauto with len.
    + destruct x; simpl. exploit H1; eauto.
      edestruct H2; eauto; dcr; simpl in *.
      rewrite H8.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      rewrite union_comm. eapply incl_union_lr; eauto.
      rewrite lookup_set_incl; eauto. clear; cset_tac.
    + hnf; intros. inv_get. destruct x.
      edestruct H2; eauto; dcr; simpl in *.
      econstructor; eauto.
    + hnf; intros; inv_get. destruct x3, x1.
      exploit H3; eauto using zip_get.
    + rewrite <- H5. eapply eq_union_lr; eauto.
      eapply list_union_eq; eauto with len.
      intros; inv_get. destruct x.
      unfold defVars; simpl. reflexivity.
Qed.