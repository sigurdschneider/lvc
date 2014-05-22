Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Sim Alpha Coherence Fresh Annotation DecSolve SetOperations LabelsDefined.

Require Import Liveness ValueOpts.

Set Implicit Arguments.
Unset Printing Records.

Fixpoint copyPropagate (ϱ:var -> var) (s:stmt) : ann (list exp) :=
  match s with
   | stmtExp x e s =>
     if [ isVar e] then
         ann1 (e::nil) (copyPropagate (ϱ[x <- ϱ (getVar e)]) s)
     else
       ann1 (rename_exp ϱ e::nil) (copyPropagate (ϱ[x <- x]) s)
   | stmtIf e s1 s2 => ann2 (rename_exp ϱ e::nil)
                           (copyPropagate ϱ s1)
                           (copyPropagate ϱ s2)
   | stmtGoto l Y => ann0 (List.map (rename_exp ϱ) Y)
   | stmtReturn e => ann0 (rename_exp ϱ e::nil)
   | stmtExtern x f Y s => ann1 (List.map (rename_exp ϱ) Y) (copyPropagate (ϱ[x <- x]) s)
   | stmtLet Z s1 s2 =>
     ann2 nil (copyPropagate (ϱ[Z <-- Z]) s1) (copyPropagate ϱ s2)
   end.

Definition cp_eqn (ϱ:var->var) x := {{(Var x, Var (ϱ x))}}.

Definition cp_eqns (ϱ:var -> var) (lv:set var) : eqns :=
  fold union (map (cp_eqn ϱ) lv) ∅.

Instance cp_eqns_morphism_equal E
: Proper (Equal ==> Equal) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_subset E
: Proper (Subset ==> Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite H. reflexivity.
Qed.

Instance cp_eqns_morphism_flip_subset E
: Proper (flip Subset ==> flip Subset) (cp_eqns E).
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite <- H. reflexivity.
Qed.

Lemma cp_eqns_union E lv lv'
: cp_eqns E (lv ∪ lv') [=] cp_eqns E lv ∪ cp_eqns E lv'.
Proof.
  unfold Proper, respectful, cp_eqns; intros.
  rewrite map_app.
  rewrite fold_union_app. reflexivity.
  intuition.
Qed.

Lemma cp_eqns_in ϱ D x
 : x ∈ cp_eqns ϱ D
   -> exists x', x' ∈ D /\ x ∈ cp_eqn ϱ x'.
Proof.
  intros. unfold cp_eqns in H.
  eapply incl_fold_union in H. destruct H as [[? [? ?]]|]; isabsurd.
  eapply map_iff in H; intuition.
  destruct H as [? [? ?]]. eexists x1; split; eauto. rewrite H1 in H0. eauto.
Qed.

Lemma in_cp_eqns ϱ D x
 : (exists x', x' ∈ D /\ x ∈ cp_eqn ϱ x')
   -> x ∈ cp_eqns ϱ D.
Proof.
  intros. destruct H; dcr.
  eapply fold_union_incl; eauto.
  eapply map_iff; eauto. intuition.
Qed.

Lemma cp_eqns_agree_1 E E' lv
: agree_on eq lv E E'
  -> cp_eqns E lv ⊆ cp_eqns E' lv.
Proof.
  intros; hnf; intros.
  edestruct cp_eqns_in; eauto; dcr.
  eapply in_cp_eqns. eexists; split; eauto.
  unfold cp_eqn in *. rewrite <- H; eauto.
Qed.

Lemma cp_eqns_agree E E' lv
: agree_on eq lv E E'
  -> cp_eqns E lv [=] cp_eqns E' lv.
Proof.
  intros. eapply incl_eq; eauto using cp_eqns_agree_1.
  symmetry in H; eauto using cp_eqns_agree_1.
Qed.


Lemma cp_moreDefined ϱ D e
  : Exp.freeVars e[<=]D
    -> moreDefined (cp_eqns ϱ D) (cp_eqns ϱ D) e (rename_exp ϱ e).
Proof.
  general induction e; simpl.
  - reflexivity.
  - hnf; intros.
    assert ((Var v, Var (ϱ v)) ∈ cp_eqns ϱ D). {
      eapply in_cp_eqns; eexists v; split; eauto.
      - rewrite <- H; simpl; cset_tac; eauto.
      - unfold cp_eqn; simpl. cset_tac; eauto.
    }
    exploit H1; eauto.
    exploit H2; eauto. unfold satisfies in *; simpl in *.
    inv X; inv X0; try now econstructor.
    exfalso. exploit exp_eval_onvLe; eauto.
    instantiate (2:=Var v); simpl. symmetry; eauto. simpl in *. congruence.
    exploit (H0 v). symmetry. eauto. constructor. congruence.
  - simpl in H.
    exploit (IHe1 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac; intuition.
    exploit (IHe2 ϱ); eauto. instantiate (1:=D). rewrite <- H. cset_tac; intuition.
    hnf; intros.
    exploit X; eauto. exploit X0; eauto.
    simpl. inv X1; inv X2; simpl; try econstructor.
    destruct (binop_eval b y y0); econstructor; eauto.
Qed.

Lemma cp_moreDefinedArgs ϱ D Y
  : list_union (List.map Exp.freeVars Y) [<=]D
    -> moreDefinedArgs (cp_eqns ϱ D) (cp_eqns ϱ D) Y (List.map (rename_exp ϱ) Y).
Proof.
  general induction Y; simpl.
  - econstructor; eauto.
  - hnf; intros. simpl.
    assert (Exp.freeVars a ⊆ D). {
      rewrite <- H. eapply incl_list_union.
      - simpl; econstructor.
      - reflexivity.
    }
    exploit (cp_moreDefined ϱ); eauto.
    exploit X; eauto. inv X0.
    + econstructor.
    + simpl. exploit (IHY ϱ D); eauto.
      rewrite <- H. simpl.
      unfold list_union. simpl.
      rewrite (list_union_start_swap _ _ ({} ++ Exp.freeVars a)).
      cset_tac; intuition.
      exploit X1; eauto.
      inv X2; try econstructor; eauto.
Qed.

Lemma cp_eqns_add_update ϱ D x y
: x ∉ D
  -> cp_eqns (ϱ [x <- y]) (D ++ {x; {}})
            [=] {{(Var x, Var y)}} ∪ cp_eqns ϱ D.
Proof.
  intros. rewrite cp_eqns_union.
  rewrite cp_eqns_agree. Focus 2.
  instantiate (1:=ϱ). hnf; intros. lud. cset_tac.
  rewrite union_comm. unfold cp_eqns.
  rewrite map_single. rewrite fold_single.
  unfold cp_eqn. lud. cset_tac; intuition.
  exfalso. intuition. eapply Equal_ST. eapply union_m.
  eapply transpose_union. intuition.
Qed.

Lemma cp_eqns_freeVars ϱ D
: lookup_set ϱ D ⊆ D
  -> eqns_freeVars (cp_eqns ϱ D) ⊆ D.
Proof.
  intros. unfold eqns_freeVars.
  hnf; intros. eapply incl_fold_union in H0.
  destruct H0 as [[? [? ?]]|]; isabsurd.
  eapply map_iff in H0; eauto using freeVars_Proper.
  destruct H0; dcr.
  eapply cp_eqns_in in H2. destruct H2; dcr.
  unfold cp_eqn in *. cset_tac.
  rewrite H4 in H3. simpl in *. rewrite H3 in H1. cset_tac.
  destruct H1. rewrite <- H0; eauto.
  rewrite <- H0, <- H. eapply lookup_set_spec; eauto.
Qed.

Print Instances Proper.




Lemma single_in_cp_eqns x ϱ D
: x ∈ D
  -> {{ (Var x, Var (ϱ x)) }} ⊆ cp_eqns ϱ D.
Proof.
  intros. hnf; intros.
  eapply in_cp_eqns. cset_tac.
  eexists x; split; eauto.
  unfold cp_eqn. cset_tac; eauto.
Qed.



Lemma entails_cp_eqns_trivial ϱ Z
: entails {} (cp_eqns (ϱ [Z <-- Z]) (of_list Z)).
Proof.
  hnf; intros. hnf; intros.
  hnf; intros.
  eapply cp_eqns_in in H0.
  destruct H0; dcr. unfold cp_eqn in H2.
  intros.
  rewrite lookup_update_same in H2; eauto. cset_tac. rewrite H2.
  reflexivity.
Qed.

Lemma copyPropagate_sound_eqn s ang Es ϱ
: ssa s ang
  -> lookup_set ϱ (fst (getAnn ang)) ⊆ (fst (getAnn ang))
  -> labelsDefined s Es
  -> (forall n a, get Es n a -> snd a [=] ∅ /\ snd (fst (fst a)) [=] ∅)
  -> eqn_sound Es
              s
              (cp_eqns ϱ (fst (getAnn ang)))
              (cp_eqns ϱ (fst (getAnn ang)))
              ang
              (copyPropagate ϱ s).
Proof.
  intros. general induction H; invt labelsDefined; simpl.
  - destruct if.
    + inv i; simpl in *. econstructor; eauto.
      * { eapply eqn_sound_entails_monotone; eauto.
          - eapply IHssa; eauto.
            rewrite H2; simpl.
            rewrite lookup_set_add_update, H3; eauto.
            rewrite lookup_set_single; eauto; cset_tac; intuition.
          - rewrite H2; simpl.
            rewrite cp_eqns_add_update; eauto.
            eapply entails_union; split.
            + eapply entails_eqns_trans with (e':=Var v).
              cset_tac; intuition.
              rewrite <- (@single_in_cp_eqns v). cset_tac; intuition.
              cset_tac; intuition.
            + eapply entails_monotone. reflexivity.
              cset_tac; intuition.
          - rewrite H2; simpl.
            rewrite cp_eqns_add_update; eauto.
            eapply entails_union; split.
            + eapply entails_eqns_trans with (e':=Var v).
              cset_tac; intuition.
              rewrite <- (@single_in_cp_eqns v). cset_tac; intuition.
              cset_tac; intuition.
            + eapply entails_monotone. reflexivity.
              cset_tac; intuition.
        }
      * reflexivity.
    + econstructor; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      * eapply IHssa; eauto. rewrite H2; simpl.
        intros.
        rewrite lookup_set_add_update; eauto. rewrite H3. reflexivity.
      * rewrite H2; simpl. rewrite cp_eqns_add_update; eauto.
        eapply entails_union; split.
        eapply entails_eqns_refl.
        eapply entails_monotone. reflexivity.
        cset_tac; intuition.
      * rewrite H2; simpl. rewrite cp_eqns_add_update; eauto.
        eapply entails_union; split.
        eapply entails_eqns_refl.
        eapply entails_monotone. reflexivity.
        cset_tac; intuition.
      * eapply cp_moreDefined; eauto.
      * rewrite rename_exp_freeVars; eauto. rewrite H0; eauto.
  - econstructor; eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa1; eauto.
      * rewrite H4; simpl; eauto.
      * rewrite H4; simpl. reflexivity.
      * rewrite H4; simpl. reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa2; eauto.
      * rewrite H5; simpl; eauto.
      * rewrite H5; simpl. reflexivity.
      * rewrite H5; simpl. reflexivity.
    + eapply cp_moreDefined; eauto.
  - econstructor; eauto using cp_moreDefined.
  - destruct a as [[[[[]]]]].
    exploit H3; eauto. simpl in *; dcr.
    econstructor; eauto.
    + rewrite map_length; eauto.
    + rewrite H5. eapply entails_empty.
    + rewrite H4. eapply entails_empty.
    + eapply cp_moreDefinedArgs; eauto.
  - econstructor.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa; eauto.
      * rewrite H2; simpl.
        rewrite lookup_set_add_update; eauto.
        rewrite H3; reflexivity.
      * rewrite H2; simpl.
        rewrite cp_eqns_add_update; eauto.
        eapply entails_union; split; try reflexivity.
        hnf; intros. hnf; intros. hnf; intros.
        cset_tac. rewrite H7. reflexivity.
      * rewrite H2; simpl.
        rewrite cp_eqns_add_update; eauto.
        eapply entails_union; split; try reflexivity.
        hnf; intros. hnf; intros. hnf; intros.
        cset_tac. rewrite H7. reflexivity.
    + eauto using cp_moreDefinedArgs.
    + hnf; intros ? A.
      unfold list_union in A.
      eapply list_union_get in A. destruct A as [[n [t []]]|]; isabsurd.
      edestruct map_get_4; eauto; dcr. subst.
      edestruct map_get_4; try eapply H8; eauto; dcr; subst.
      exploit (get_list_union_map _ _ Exp.freeVars); try eapply H9; eauto.
      rewrite H0 in X.
      rewrite rename_exp_freeVars in H7; eauto. rewrite X in H7. eauto.
  - econstructor. instantiate (1:=cp_eqns ϱ D).  instantiate (1:=∅).
    instantiate (1:=cp_eqns ϱ D).
    instantiate (1:=∅).
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa1; eauto. rewrite H3; simpl.
      * rewrite lookup_set_union; eauto.
        rewrite update_with_list_lookup_set_incl; eauto; try reflexivity.
        rewrite lookup_set_update_with_list_in_union; eauto.
        simpl in *. rewrite H6. clear_all; cset_tac; intuition.
      * eapply labelsDefined_any; try eapply H13; reflexivity.
      * intros. inv H9; simpl in *. split; reflexivity.
        eapply H8; eauto.
      * rewrite H3; simpl.
        rewrite cp_eqns_union.
        rewrite (@cp_eqns_agree (ϱ [Z <-- Z]) ϱ D).
        eapply entails_union; split.
        eapply entails_monotone.
        eapply entails_cp_eqns_trivial. eapply incl_left.
        eapply entails_monotone. reflexivity. eapply incl_right.
        assert (D [=] D \ of_list Z). revert H.
        clear_all; cset_tac; intuition; eauto.
        rewrite H9. eapply update_with_list_agree_minus; eauto. reflexivity.
      * rewrite H3; simpl.
        rewrite cp_eqns_union.
        rewrite (@cp_eqns_agree (ϱ [Z <-- Z]) ϱ D).
        eapply entails_union; split.
        eapply entails_monotone.
        eapply entails_cp_eqns_trivial. eapply incl_left.
        eapply entails_monotone. reflexivity. eapply incl_right.
        assert (D [=] D \ of_list Z). revert H.
        clear_all; cset_tac; intuition; eauto.
        rewrite H9. eapply update_with_list_agree_minus; eauto. reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa2.
      * rewrite H5. simpl. eauto.
      * eapply labelsDefined_any; try eapply H14; reflexivity.
      * intros. inv H9; simpl in *. split; reflexivity.
        eapply H8; eauto.
      * rewrite H5. simpl. reflexivity.
      * rewrite H5. reflexivity.
    + eapply incl_empty.
    + eapply incl_empty.
    + rewrite cp_eqns_freeVars; eauto; reflexivity.
    + eapply cp_eqns_freeVars; eauto.
    + reflexivity.
    + reflexivity.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
