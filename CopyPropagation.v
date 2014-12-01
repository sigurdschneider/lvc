Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Sim Coherence Fresh Annotation DecSolve SetOperations LabelsDefined.

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

Definition cp_eqn (ϱ:var->var) x :=
  EqnApx (Var x) (Var (ϱ x)).

Definition cp_eqns (ϱ:var -> var) (lv:set var) : eqns :=
  map (cp_eqn ϱ) lv.

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
  rewrite map_app. reflexivity.
  (* rewrite fold_union_app. reflexivity. *)
  intuition.
Qed.

Lemma cp_eqns_in ϱ D x
 : x ∈ cp_eqns ϱ D
   -> exists x', x' ∈ D /\ x = cp_eqn ϱ x'.
Proof.
  intros. unfold cp_eqns in H.
  eapply map_iff in H; intuition.
Qed.

Lemma in_cp_eqns ϱ D x
 : (exists x', x' ∈ D /\ x = cp_eqn ϱ x')
   -> x ∈ cp_eqns ϱ D.
Proof.
  intros. destruct H; dcr.
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
    -> entails (cp_eqns ϱ D) {EqnApx e (rename_exp ϱ e)}.
Proof.
  general induction e; simpl.
  - hnf; intros; hnf; intros. cset_tac; intuition. rewrite <- H1.
    constructor. reflexivity.
  - hnf; intros.
    assert (EqnApx (Var v) (Var (ϱ v)) ∈ cp_eqns ϱ D). {
      eapply in_cp_eqns; eexists v; split; eauto.
      - rewrite <- H; simpl; cset_tac; eauto.
    }
    exploit H0; eauto.
    hnf; intros. cset_tac; intuition. rewrite <- H2; eauto.
  - simpl in H.
    exploit (IHe ϱ); eauto.
    hnf; intros; hnf; intros. cset_tac. rewrite <- H1. exploit X; eauto.
    exploit X0. cset_tac; reflexivity.
    simpl. inv X1; simpl. inv H3.
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
    simpl.
    reflexivity.
Qed.

Lemma cp_moreDefinedArgs ϱ D Y
  : list_union (List.map Exp.freeVars Y) [<=]D
    -> moreDefinedArgs (cp_eqns ϱ D) Y (List.map (rename_exp ϱ) Y).
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
    exploit X; eauto. exploit X0. cset_tac; reflexivity. inv X1.
    inv H3.
    + econstructor.
    + simpl. exploit (IHY ϱ D); eauto.
      rewrite <- H. simpl.
      unfold list_union. simpl.
      rewrite (list_union_start_swap _ _ ({} ++ Exp.freeVars a)).
      cset_tac; intuition.
      exploit X2; eauto.
      inv X3; try econstructor; eauto.
Qed.

Lemma cp_eqns_add_update ϱ D x y
: x ∉ D
  -> cp_eqns (ϱ [x <- y]) (D ++ {x; {}})
            [=] {EqnApx (Var x) (Var y); cp_eqns ϱ D}.
Proof.
  intros. rewrite cp_eqns_union.
  rewrite cp_eqns_agree. Focus 2.
  instantiate (1:=ϱ). hnf; intros. lud. cset_tac.
  rewrite union_comm. unfold cp_eqns.
  rewrite map_single.
  unfold cp_eqn. lud. cset_tac; intuition.
  intuition. intuition.
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
  rewrite H3 in H1. simpl in *. cset_tac.
  destruct H1. rewrite <- H0; eauto.
  rewrite <- H0, <- H. eapply lookup_set_spec; eauto.
Qed.

Lemma single_in_cp_eqns x ϱ D
: x ∈ D
  -> {{ EqnApx (Var x) (Var (ϱ x)) }} ⊆ cp_eqns ϱ D.
Proof.
  intros. hnf; intros.
  eapply in_cp_eqns. cset_tac.
  eexists x; split; eauto.
Qed.



Lemma entails_cp_eqns_trivial ϱ Z
: entails {} (cp_eqns (ϱ [Z <-- Z]) (of_list Z)).
Proof.
  hnf; intros. hnf; intros.
  hnf; intros.
  eapply cp_eqns_in in H0.
  destruct H0; dcr. unfold cp_eqn in H2.
  intros.
  rewrite lookup_update_same in H2; eauto. cset_tac.
  reflexivity.
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
: ssa s ang
  -> lookup_set ϱ (fst (getAnn ang)) ⊆ (fst (getAnn ang))
  -> labelsDefined s (length Es)
  -> (forall n a, get Es n a -> snd a [=] ∅)
  -> eqn_sound Es
              s
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
            eapply entails_union.
            + rewrite add_union_singleton; reflexivity.
            + eapply entails_eqns_trans' with (e':=Var v).
              cset_tac; intuition.
              rewrite <- (@single_in_cp_eqns v).
              eapply incl_right; cset_tac; intuition.
              cset_tac; intuition.
            + eapply entails_monotone. reflexivity.
              eapply incl_right.
        }
      * hnf; intros; hnf; intros. cset_tac; intuition. rewrite <- H7.
        simpl. reflexivity.
    + econstructor; eauto.
      eapply eqn_sound_entails_monotone; eauto.
      * eapply IHssa; eauto. rewrite H2; simpl.
        intros.
        rewrite lookup_set_add_update; eauto. rewrite H3. reflexivity.
      * rewrite H2; simpl. rewrite cp_eqns_add_update; eauto.
        eapply entails_union.
        rewrite add_union_singleton; reflexivity.
        eapply entails_eqns_apx_refl.
        eapply entails_monotone. reflexivity.
        cset_tac; intuition.
      * eapply cp_moreDefined; eauto.
      * rewrite rename_exp_freeVars; eauto. rewrite H0; eauto.
  - econstructor; intros. eauto.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa1; eauto.
      * rewrite H4; simpl; eauto.
      * rewrite H4; simpl.
        eapply entails_monotone; try reflexivity; try eapply incl_right.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa2; eauto.
      * rewrite H5; simpl; eauto.
      * rewrite H5; simpl.
        eapply entails_monotone; try reflexivity; try eapply incl_right.
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
      eapply IHssa; eauto.
      * rewrite H2; simpl.
        rewrite lookup_set_add_update; eauto.
        rewrite H3; reflexivity.
      * rewrite H2; simpl.
        rewrite cp_eqns_add_update; eauto.
        eapply entails_union.
        rewrite add_union_singleton; reflexivity.
        admit. (* better provide a lemma here *)
        reflexivity.
    + eauto using cp_moreDefinedArgs.
    + hnf; intros ? A.
      unfold list_union in A.
      eapply list_union_get in A. destruct A as [[n [t []]]|]; isabsurd.
      edestruct map_get_4; eauto; dcr. subst.
      edestruct map_get_4; try eapply H8; eauto; dcr; subst.
      exploit (get_list_union_map _ _ Exp.freeVars); try eapply H9; eauto.
      rewrite H0 in X.
      rewrite rename_exp_freeVars in H7; eauto. rewrite X in H7. eauto.
  - econstructor. instantiate (1:=cp_eqns ϱ D). instantiate (1:=∅).
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa1; eauto. rewrite H3; simpl.
      * rewrite lookup_set_union; eauto.
        rewrite update_with_list_lookup_set_incl; eauto; try reflexivity.
        rewrite lookup_set_update_with_list_in_union; eauto.
        simpl in *. rewrite H6. clear_all; cset_tac; intuition.
      * intros. inv H9; simpl in *. reflexivity.
        eapply H8; eauto.
      * rewrite H3; simpl.
        rewrite cp_eqns_union.
        rewrite (@cp_eqns_agree (ϱ [Z <-- Z]) ϱ D).
        eapply entails_union.
        reflexivity.
        eapply entails_monotone.
        eapply entails_cp_eqns_trivial. eapply incl_left.
        eapply entails_monotone. reflexivity. eapply incl_right.
        assert (D [=] D \ of_list Z). revert H.
        clear_all; cset_tac; intuition; eauto.
        rewrite H9. eapply update_with_list_agree_minus; eauto. reflexivity.
    + eapply eqn_sound_entails_monotone; eauto.
      eapply IHssa2; simpl; eauto.
      * rewrite H5. simpl. eauto.
      * intros. inv H9; simpl in *. reflexivity.
        eapply H8; eauto.
      * rewrite H5. simpl. reflexivity.
    + eapply incl_empty.
    + rewrite cp_eqns_freeVars; eauto; reflexivity.
    + reflexivity.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
