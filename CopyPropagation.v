Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Sim Coherence Fresh Annotation DecSolve SetOperations LabelsDefined.

Require Import Liveness Eqn ValueOpts RenamedApart.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint copyPropagate (ϱ:var -> var) (s:stmt) : stmt :=
  match s with
   | stmtLet x e s =>
     if [ isVar e] then
       stmtLet x e (copyPropagate (ϱ[x <- ϱ (getVar e)]) s)
     else
       stmtLet x (rename_exp ϱ e) (copyPropagate (ϱ[x <- x]) s)
   | stmtIf e s1 s2 => stmtIf (rename_exp ϱ e)
                             (copyPropagate ϱ s1)
                             (copyPropagate ϱ s2)
   | stmtApp l Y => stmtApp l (List.map (rename_exp ϱ) Y)
   | stmtReturn e => stmtReturn (rename_exp ϱ e)
   | stmtExtern x f Y s => stmtExtern x f (List.map (rename_exp ϱ) Y) (copyPropagate (ϱ[x <- x]) s)
   | stmtFun Z s1 s2 =>
     stmtFun Z (copyPropagate (ϱ[Z <-- Z]) s1) (copyPropagate ϱ s2)
   end.

Definition cp_eqn (ϱ:var -> var) (x:var) := EqnApx (Var x) (Var (ϱ x)).


Lemma cp_moreDefined ϱ D e
  : Exp.freeVars e[<=]D
    -> entails (map (cp_eqn ϱ) D) {EqnApx e (rename_exp ϱ e)}.
Proof.
  general induction e; simpl.
  - eapply entails_eqns_apx_refl.
  - eapply entails_subset.
    eapply incl_singleton.
    eapply map_iff; intuition.
    eexists v; split; eauto.
    rewrite <- H; simpl; cset_tac; eauto.
  - simpl in H.
    exploit (IHe ϱ); eauto.
    hnf; intros; hnf; intros. cset_tac. rewrite <- H1.
    exploit X; eauto.
    exploit X0. cset_tac; reflexivity.
    simpl. inv X1; simpl; eauto.
    + econstructor.
    + reflexivity.
  - simpl in H.
    exploit (IHe1 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac; intuition.
    exploit (IHe2 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac; intuition.
    hnf; intros; hnf; intros. cset_tac. invc H1. simpl.
    exploit X; eauto. exploit X1; eauto. cset_tac; reflexivity.
    exploit X0; eauto. exploit X3; eauto. cset_tac; reflexivity.
    simpl in *.
    inv X2; inv X4; try now econstructor.
    simpl. reflexivity.
Qed.


Lemma cp_moreDefinedArgs ϱ D Y
  : list_union (List.map Exp.freeVars Y) [<=]D
    -> entails (map (cp_eqn ϱ) D) (list_EqnApx Y (List.map (rename_exp ϱ) Y)).
Proof.
  general induction Y; simpl.
  - eapply entails_empty.
  - assert (Exp.freeVars a ⊆ D). {
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
    rewrite <- H.
    unfold list_union. simpl.
    rewrite (list_union_start_swap _ _ ({} ++ Exp.freeVars a)).
    cset_tac; intuition.
Qed.


Lemma cp_eqns_agree_incl E E' lv
: agree_on eq lv E E'
  -> map (cp_eqn E) lv ⊆ map (cp_eqn E') lv.
Proof.
  intros; hnf; intros.
  eapply map_iff in H0; intuition. dcr.
  eapply map_iff; intuition.
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
  rewrite map_add; intuition.
  unfold cp_eqn at 1.
  lud; isabsurd. rewrite cp_eqns_agree with (E':=ϱ).
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
  eapply map_iff in H3; intuition. dcr.
  invc H5. unfold cp_eqn in *; simpl in *.
  rewrite H4 in H1. cset_tac; intuition.
  invc H0; eauto.
  eapply H. eapply lookup_set_spec; eauto.
Qed.


Lemma single_in_cp_eqns x ϱ D
: x ∈ D
  -> {{ EqnApx (Var x) (Var (ϱ x)) }} ⊆ map (cp_eqn ϱ) D.
Proof.
  intros. hnf; intros.
  eapply map_iff; intuition.
  eexists x; split; eauto. cset_tac; intuition.
Qed.


Lemma entails_cp_eqns_trivial ϱ Z
: entails {} (map (cp_eqn (ϱ [Z <-- Z])) (of_list Z)).
Proof.
  hnf; intros. hnf; intros.
  eapply map_iff in H0; intuition.
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
  hnf; intros. cset_tac. rewrite <- H2.
  simpl. exploit (H1 _ H); eauto.
  exploit (H1 _ H0); eauto.
  simpl in *. inv X; inv X0.
  - congruence.
  - econstructor; eauto. congruence.
Qed.


Lemma copyPropagate_sound_eqn s ang Es ϱ
: renamedApart s ang
  -> lookup_set ϱ (fst (getAnn ang)) ⊆ (fst (getAnn ang))
  -> labelsDefined s (length Es)
  -> (forall n a, get Es n a -> snd a [=] ∅)
  -> eqn_sound Es
              s (copyPropagate ϱ s)
              (map (cp_eqn ϱ) (fst (getAnn ang)))
              ang.
Proof.
  intros. general induction H; invt labelsDefined; simpl.
  - cases.
    + inv i; simpl in *. econstructor; eauto.
      * { eapply eqn_sound_entails_monotone; eauto.
          - eapply IHrenamedApart; eauto.
            rewrite H2; simpl.
            rewrite lookup_set_add_update; eauto.
            assert (v ∈ D) by (cset_tac; intuition).
            pose proof (lookup_set_single H7 H4); eauto.
            revert H4 H8; clear_all; cset_tac; intuition.
          - rewrite H2; simpl.
            rewrite cp_eqns_add_update; eauto.
            rewrite add_union_singleton.
            eapply entails_union'.
            + rewrite add_union_singleton; reflexivity.
            + eapply entails_eqns_trans' with (e':=Var v).
              cset_tac; intuition.
              rewrite <- (@single_in_cp_eqns v).
              cset_tac; intuition.
              cset_tac; intuition.
            + eapply entails_monotone; [ reflexivity | ].
              cset_tac; intuition.
        }
      * hnf; intros; hnf; intros. cset_tac; intuition. rewrite <- H8.
        simpl. reflexivity.
    + econstructor; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      * eapply IHrenamedApart; eauto. rewrite H2; simpl.
        intros.
        rewrite lookup_set_add_update; eauto. simpl in *.
        rewrite H4. reflexivity.
      * rewrite H2; simpl. rewrite cp_eqns_add_update; eauto.
        eapply entails_union'.
        rewrite add_union_singleton; reflexivity.
        eapply entails_eqns_apx_refl.
        eapply entails_monotone. reflexivity.
        cset_tac; intuition.
      * eapply cp_moreDefined; eauto.
      * rewrite rename_exp_freeVars; eauto. rewrite H0; eauto.
  - econstructor; intros. eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHrenamedApart1; eauto.
      * rewrite H4; simpl; eauto.
      * rewrite H4; simpl.
        eapply entails_monotone; try reflexivity; cset_tac; intuition.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHrenamedApart2; eauto.
      * rewrite H5; simpl; eauto.
      * rewrite H5; simpl.
        eapply entails_monotone; try reflexivity; cset_tac; intuition.
    + eapply cp_moreDefined; eauto.
  - econstructor; eauto using cp_moreDefined.
  - edestruct get_in_range as [a ?]; eauto.
    destruct a as [[[]]].
    exploit H3; eauto. simpl in *; dcr.
    econstructor; eauto.
    + rewrite map_length; eauto.
    + rewrite X. eapply entails_empty.
    + eapply cp_moreDefinedArgs; eauto.
  - econstructor.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHrenamedApart; eauto.
      * rewrite H2; simpl.
        rewrite lookup_set_add_update; eauto.
        simpl in *. rewrite H4; reflexivity.
      * rewrite H2; simpl.
        rewrite cp_eqns_add_update; eauto.
        eapply entails_union'.
        rewrite add_union_singleton; reflexivity.
        eapply entails_eqns_apx_refl.
        reflexivity.
    + eauto using cp_moreDefinedArgs.
    + simpl in *.
      hnf; intros ? A.
      unfold list_union in A.
      eapply list_union_get in A. destruct A as [[n [t []]]|]; isabsurd.
      edestruct map_get_4; eauto; dcr. subst.
      edestruct map_get_4; try eapply H9; eauto; dcr; subst.
      exploit (get_list_union_map _ _ Exp.freeVars); try eapply H10; eauto.
      rewrite H0 in X.
      rewrite rename_exp_freeVars in H8; eauto. rewrite X in H8. eauto.
    + rewrite map_length; reflexivity.
  - econstructor. instantiate (1:=map (cp_eqn ϱ) D). instantiate (1:=∅).
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHrenamedApart1; eauto. rewrite H3; simpl.
      * rewrite lookup_set_union; eauto.
        rewrite update_with_list_lookup_set_incl; eauto; try reflexivity.
        rewrite lookup_set_update_with_list_in_union; eauto.
        simpl in *. rewrite H7. clear_all; cset_tac; intuition.
      * intros. inv H10; simpl in *. reflexivity.
        eapply H9; eauto.
      * rewrite H3; simpl.
        rewrite map_app; [| clear_all; intuition].
        rewrite (@cp_eqns_agree (ϱ [Z <-- Z]) ϱ D).
        eapply entails_union'.
        reflexivity.
        eapply entails_monotone.
        eapply entails_cp_eqns_trivial. eapply incl_left.
        eapply entails_monotone. reflexivity. eapply incl_right.
        assert (D [=] D \ of_list Z). revert H.
        clear_all; cset_tac; intuition; eauto.
        rewrite H10. eapply update_with_list_agree_minus; eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHrenamedApart2; simpl; eauto.
      * rewrite H5. simpl. eauto.
      * intros. inv H10; simpl in *. reflexivity.
        eapply H9; eauto.
      * rewrite H5. simpl. reflexivity.
    + eapply incl_empty.
    + rewrite cp_eqns_freeVars; eauto; reflexivity.
    + reflexivity.
Qed.
