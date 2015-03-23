Require Import CSet Le.

Require Import Plus Util Map DecSolve.
Require Import Env EnvTy IL Annotation Liveness Coherence Alpha Restrict RenamedApart.
Require Import Rename RenamedApart_Liveness.

Set Implicit Arguments.

(** * Local Injectivity *)

(** ** Inductive definition of local injectivity of a renaming rho *)

Inductive locally_inj (rho:env var) : stmt -> ann (set var) -> Prop :=
| RNOpr x b lv e (al:ann (set var))
  :  locally_inj rho b al
  -> injective_on lv rho
(*  -> injective_on (getAnn al ∪ {{x}}) rho *)
  -> locally_inj rho (stmtLet x e b) (ann1 lv al)
| RNIf x b1 b2 lv (alv1 alv2:ann (set var))
  :  injective_on lv rho
  -> locally_inj rho b1 alv1
  -> locally_inj rho b2 alv2
  -> locally_inj rho (stmtIf x b1 b2) (ann2 lv alv1 alv2)
| RNGoto l Y lv
  : injective_on lv rho
  -> locally_inj rho (stmtApp l Y) (ann0 lv)
| RNReturn x lv
  : injective_on lv rho
  -> locally_inj rho (stmtReturn x) (ann0 lv)
| RNExtern x f Y b lv (al:ann (set var))
  : locally_inj rho b al
  -> injective_on lv rho
(*  -> injective_on (getAnn al ∪ {{x}}) rho *)
  -> locally_inj rho (stmtExtern x f Y b) (ann1 lv al)
| RNLet s Z b lv (alvs alvb:ann (set var))
  : locally_inj rho s alvs
  -> locally_inj rho b alvb
  -> injective_on lv rho
(*  -> injective_on (getAnn alvs ∪ of_list Z) rho *)
  -> locally_inj rho (stmtFun Z s b) (ann2 lv alvs alvb).

(** ** Some Properties *)

(** local injectivity can only hold if [lv] is a valid annotation *)

Lemma locally_inj_annotation (ϱ:env var) (s:stmt) (lv:ann (set var))
: locally_inj ϱ s lv -> annotation s lv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

(** local injectivity respects functional equivalence (if the function itself is injective wrt. the underlying equivalence) *)

Global Instance locally_inj_morphism
  : Proper (@fpeq _ _ eq _ _ ==> eq ==> eq ==> impl) locally_inj.
Proof.
  unfold Proper, respectful, impl; intros; subst.
  general induction H2; assert (FEQ:x ≡ y) by first [eapply H0 | eapply H1 | eapply H2];  econstructor; eauto;
  try rewrite <- FEQ; eauto.
Qed.

(** local injectivity means injectivity on the live variables *)
Lemma locally_injective s (slv:ann (set var)) ϱ
  : locally_inj ϱ s slv
  -> injective_on (getAnn slv) ϱ.
Proof.
  intros. general induction H; eauto.
Qed.

(** ** local injectivity is decidable *)

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  general induction s; destruct lv; try (now exfalso; inv an).
  + decide(injective_on a ϱ);
    (*decide(injective_on (getAnn lv ∪ {{x}}) ϱ);*) try dec_solve;
    edestruct IHs; eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct IHs1; eauto; try inv an; eauto; try dec_solve;
    edestruct IHs2; eauto; try inv an; eauto; try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ);
    (* decide(injective_on (getAnn lv ∪ {{x}}) ϱ); *) try dec_solve;
    edestruct IHs; eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ);
    (* decide (injective_on (getAnn lv1 ∪ of_list Z) ϱ); *) try dec_solve;
    edestruct IHs1; eauto; try inv an; eauto; try dec_solve;
    edestruct IHs2; eauto; try inv an; eauto; try dec_solve.
Defined.

Instance locally_inj_dec_inst (ϱ:env var) (s:stmt) (lv:ann (set var))
         `{Computable (annotation s lv)}
  : Computable (locally_inj ϱ s lv).
Proof.
  destruct H as [].
  hnf; eauto using locally_inj_dec.
  right; intro; eauto using locally_inj_annotation.
Defined.

(** ** Renaming with a locally injective renaming yields a coherent program *)

Lemma rename_renamedApart_srd s ang ϱ (alv:ann (set var)) Lv
  : renamedApart s ang
  -> (getAnn alv) ⊆ fst (getAnn ang)
  -> live_sound FunctionalAndImperative Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_globals Lv) (fst (getAnn ang))
  -> srd (map_lookup ϱ (restrict (live_globals Lv) (getAnn alv)))
        (rename ϱ s)
        (mapAnn (lookup_set ϱ) alv).
Proof.
  intros SSA INCL LS RI.
  general induction RI; inv LS; subst; inv SSA; simpl.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. simpl in *. rewrite H12; simpl.
        cset_tac; intuition. decide (x === a); intuition. right. eapply INCL.
        eapply H9. cset_tac; intuition.
        rewrite H12. simpl in *.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H9. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition.
        assert (getAnn al [=] getAnn al ++ {x; {}}). cset_tac; intuition.
        invc H2; eauto. rewrite <- H1. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor. simpl in *.
    + eapply srd_monotone.
      eapply IHRI1; eauto using Subset_trans, lookup_set_incl; eauto;
                           try (now eapply Subset_trans; eauto).
      rewrite H15; simpl; etransitivity; eauto.
      rewrite H15; simpl; eauto.
      eapply list_eq_fstNoneOrR_incl; eauto.
    + eapply srd_monotone.
      eapply IHRI2; eauto; try (now eapply Subset_trans; eauto).
      rewrite H16; simpl; etransitivity; eauto.
      rewrite H16; simpl; eauto.
      eapply list_eq_fstNoneOrR_incl; eauto.
  - econstructor.
    instantiate (1:= lookup_set ϱ (blv \ of_list Z)).
    unfold live_globals.
    pose proof (map_get_1 live_global H4).
    pose proof (map_get_1 (restr lv) H1).
    pose proof (map_get_1 (lookup_set_option ϱ) H2).
    assert (restr lv (live_global (blv, Z)) = Some (blv \ of_list Z)).
    eapply restr_iff; intuition. rewrite H10 in H5.
    eapply H5.
  - econstructor.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. simpl in *. rewrite H13; simpl.
        cset_tac; intuition. decide (a === x); intuition. right. eapply INCL.
        eapply H10. cset_tac; intuition.
        rewrite H13. simpl in *.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H10. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition.
        assert (getAnn al [=] getAnn al ++ {x; {}}). cset_tac; intuition.
        invc H2; eauto. rewrite <- H1. eauto using locally_injective.
        cset_tac; intuition.
  - assert (injective_on (getAnn alvs ++ of_list Z) ϱ). {
      eapply injective_on_incl. eapply locally_injective. eapply RI1.
      cset_tac; intuition.
    }
    econstructor; eauto.
    + eapply srd_monotone.
      * eapply IHRI1; eauto. simpl in *. rewrite H13; simpl.
        rewrite <- INCL. rewrite <- H11. eapply incl_union_minus.
        simpl. split. simpl in *. rewrite H11, H13; simpl. cset_tac; intuition.
        rewrite H13; simpl. rewrite <- incl_right; eauto.
      * Opaque restrict. simpl. unfold live_global. rewrite restrict_incl. simpl.
        simpl. rewrite restrict_incl. constructor. constructor.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_eq; eauto; intuition.
        intuition.
        erewrite (@restrict_incl_ext _ (getAnn alvs)); eauto.
        instantiate (1:=getAnn alvs \ of_list Z).
        eapply list_eq_special; eauto.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_incl_inj; eauto; intuition. intuition.
        simpl. simpl in *.
        cset_tac; intuition; eauto. reflexivity.
        eapply incl_minus.
    + eapply srd_monotone. simpl in * |- *.
      eapply IHRI2; eauto.
      rewrite H16; simpl in * |- *; eauto. transitivity lv; eauto.
      rewrite H16; simpl.
      split; eauto. eapply Subset_trans; eauto.
      simpl. decide (getAnn alvs \ of_list Z ⊆ getAnn alvb).
      unfold live_global. simpl.
      rewrite restrict_incl; eauto. simpl. econstructor. econstructor; eauto.
      rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
      eapply lookup_set_minus_eq; eauto; intuition. intuition.
      eapply list_eq_fstNoneOrR_incl; eauto.
      unfold live_global. simpl. rewrite restrict_not_incl; eauto. simpl.
      econstructor. econstructor. eapply list_eq_fstNoneOrR_incl; eauto.
Qed.

Lemma locally_inj_subset ϱ s alv alv'
: locally_inj ϱ s alv
  -> ann_R Subset alv' alv
  -> locally_inj ϱ s alv'.
Proof.
  intros.
  general induction H; invt @ann_R; simpl in *; eauto 20 using locally_inj, injective_on_incl.
Qed.

Lemma bounded_disjoint Lv u v
: bounded (live_globals Lv) u
  -> disj u v
  -> disjoint (live_globals Lv) v.
Proof.
  general induction Lv; simpl in * |- *; eauto; isabsurd; dcr.
  - hnf; intros. inv H. rewrite H1; eauto.
    exploit IHLv; eauto.
Qed.

Lemma meet1_incl2 a b
: Subset1 (meet1 a b) b.
Proof.
  destruct b; simpl. cset_tac; intuition.
Qed.

Lemma meet1_Subset1 s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset1 (mapAnn2 meet1 alv ang) ang.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl2.
Qed.

Lemma rename_renamedApart_srd' s ang ϱ (alv:ann (set var)) Lv
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_globals Lv) (fst (getAnn ang))
  -> LabelsDefined.noUnreachableCode s
  -> srd
        (map_lookup ϱ
           (restrict (live_globals Lv) (getAnn (mapAnn2 meet1 alv ang))))
        (rename ϱ s) (mapAnn (lookup_set ϱ) (mapAnn2 meet1 alv ang)).
Proof.
  intros.
  exploit live_sound_renamedApart_minus; eauto.
  eapply renamedApart_live_imperative_is_functional in X; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply rename_renamedApart_srd in X; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
  destruct (getAnn ang); simpl; cset_tac; intuition.
Qed.

Require Import LabelsDefined.

(** ** Theorem 6 from the paper. *)
(** The generalization to the paper version is
    that we do not bound by the free variables, but by a set that that contains
    the free variables and is disjoint with any variables occuring in binding
    positions in [s]; this set is [fst (getAnn ang)] *)

Lemma rename_renamedApart_srd'' s ang ϱ (alv:ann (set var)) Lv
  : renamedApart s ang
    -> live_sound Imperative Lv s alv
    -> ann_R Subset1 alv ang
    -> locally_inj ϱ s alv
    -> bounded (live_globals Lv) (fst (getAnn ang))
    -> noUnreachableCode s
    -> srd (map_lookup ϱ (restrict (live_globals Lv) (getAnn alv)))
          (rename ϱ s)
          (mapAnn (lookup_set ϱ) alv).
Proof.
  intros SSA LS INCL RI BOUND UNREACH.
  general induction RI; inv LS; subst; inv SSA; inv INCL; inv UNREACH; simpl.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto.
        rewrite H11. simpl in *.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H8. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition.
        assert (getAnn al [=] getAnn al ++ {x; {}}). cset_tac; intuition.
        invc H2; eauto. rewrite <- H0. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor. simpl in *.
    + eapply srd_monotone.
      eapply IHRI1; eauto using Subset_trans, lookup_set_incl; eauto;
                           try (now eapply Subset_trans; eauto).
      rewrite H14; simpl; eauto.
      eapply list_eq_fstNoneOrR_incl; eauto.
    + eapply srd_monotone.
      eapply IHRI2; eauto; try (now eapply Subset_trans; eauto).
      rewrite H15; simpl; eauto.
      eapply list_eq_fstNoneOrR_incl; eauto.
  - econstructor.
    instantiate (1:= lookup_set ϱ (blv \ of_list Z)).
    unfold live_globals.
    pose proof (map_get_1 live_global H3).
    pose proof (map_get_1 (restr lv) H0).
    pose proof (map_get_1 (lookup_set_option ϱ) H1).
    assert (restr lv (live_global (blv, Z)) = Some (blv \ of_list Z)).
    eapply restr_iff; intuition. rewrite H10 in H9.
    eapply H9.
  - econstructor.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. simpl in *. rewrite H12; simpl.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H9. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition.
        assert (getAnn al [=] getAnn al ++ {x; {}}). cset_tac; intuition.
        invc H2; eauto. rewrite <- H0. eauto using locally_injective.
        cset_tac; intuition.
  - assert (injective_on (getAnn alvs ++ of_list Z) ϱ). {
      eapply injective_on_incl. eapply locally_injective. eapply RI1.
      cset_tac; intuition.
    }
    exploit renamedApart_globals_live; eauto.
    hnf; intros. inv H1. pe_rewrite.
    eapply renamedApart_disj in H13. pe_rewrite; eauto.
    eapply ann_R_get in H20. pe_rewrite. rewrite H20.
    revert H13; unfold disj; clear_all; cset_tac; intuition; eauto.
    eapply bounded_disjoint; eauto.
    eapply renamedApart_disj in H13. pe_rewrite; eauto.
    destruct X; dcr. invc H2; simpl in *.
    econstructor; eauto.
    + eapply srd_monotone.
      * eapply IHRI1; eauto. simpl in *. rewrite H12; simpl.
        rewrite H22.
        simpl. split. rewrite H11. rewrite H17. eapply incl_right.
        rewrite <- incl_right; eauto.
      * Opaque restrict. simpl. unfold live_global. rewrite restrict_incl. simpl.
        simpl. rewrite restrict_incl. constructor. constructor.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_eq; eauto; intuition.
        intuition.
        erewrite (@restrict_incl_ext _ (getAnn alvs)); eauto.
        instantiate (1:=getAnn alvs \ of_list Z).
        eapply list_eq_special; eauto. rewrite H22; eauto.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_incl_inj; eauto; intuition. intuition.
        simpl. simpl in *.
        cset_tac; intuition; eauto. reflexivity.
        eapply incl_minus.
    + eapply srd_monotone. simpl in * |- *.
      eapply IHRI2; eauto.
      rewrite H15; simpl in * |- *; eauto. split; eauto.
      transitivity lv; eauto. etransitivity; eauto.
      simpl.
      unfold live_global. simpl.
      rewrite restrict_incl; eauto. simpl. econstructor. econstructor; eauto.
      rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
      eapply lookup_set_minus_eq; eauto; intuition. intuition.
      eapply list_eq_fstNoneOrR_incl; eauto.
Qed.


Open Scope set_scope.

(** ** Renaming with a locally injective renaming yields an α-equivalent program *)

Lemma renamedApart_locally_inj_alpha s ϱ ϱ' DL (slv:ann (set var)) ang
  : renamedApart s ang
  -> locally_inj ϱ s slv
  -> live_sound Functional DL s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros. general induction H; simpl; invt locally_inj; invt live_sound.
  - econstructor. simpl in *. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). {
      rewrite update_id; eauto.
    }
    rewrite H7. eapply IHrenamedApart; eauto.
    assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
    split; intuition. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H11.
    cset_tac; intuition. invc H9; eauto.
  - econstructor; eauto. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    now eapply IHrenamedApart1; eauto using inverse_on_incl.
    now eapply IHrenamedApart2; eauto using inverse_on_incl.

  - econstructor; eauto. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.

  - econstructor; eauto. rewrite map_length. eauto.
    intros. edestruct map_get_4; eauto; dcr; subst.
    get_functional; eauto; subst.
    eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.

  - econstructor.
    + rewrite map_length; eauto.
    + intros. edestruct map_get_4; eauto; dcr; subst.
      get_functional; eauto; subst.
      eapply alpha_exp_rename_injective.
      eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    +
      assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). {
        rewrite update_id; eauto.
      }
      rewrite H7. eapply IHrenamedApart; eauto.
      assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
        split; intuition. rewrite update_id. reflexivity. intuition.
      }
      eapply locally_inj_morphism; eauto.
      eapply inverse_on_update_minus; eauto using inverse_on_incl,
                                      locally_injective.
      eapply injective_on_incl. eapply locally_injective, H12.
      cset_tac; intuition. invc H9; eauto.
  - constructor.
    + rewrite lookup_list_length; eauto.
    + rewrite update_with_list_lookup_list.
      eapply IHrenamedApart1; eauto.
      assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
      simpl in H6.
      eapply inverse_on_update_with_list; try intuition.
      eapply injective_on_incl. eapply locally_injective, H13.
      cset_tac; intuition.
      eapply inverse_on_incl; eauto; intuition. intuition.
    + eapply IHrenamedApart2; eauto using inverse_on_incl.
Qed.

Lemma renamedApart_locally_inj_alpha' s ϱ ϱ' Lv alv ang
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_globals Lv) (fst (getAnn ang))
  -> LabelsDefined.noUnreachableCode s
  -> inverse_on (getAnn alv) ϱ ϱ'
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros.
  exploit live_sound_renamedApart_minus; eauto.
  eapply renamedApart_live_imperative_is_functional in X; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in X.
  eapply renamedApart_locally_inj_alpha in X; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply inverse_on_incl; eauto.
  erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
  destruct (getAnn ang); simpl; cset_tac; intuition.
Qed.

(** ** Theorem 7 from the paper *)
(** the generalization is analogous to the generalization in Theorem 6 *)

Lemma renamedApart_locally_inj_alpha'' s ϱ ϱ' DL (slv:ann (set var)) ang
  : renamedApart s ang
  -> locally_inj ϱ s slv
  -> live_sound Imperative DL s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> ann_R Subset1 slv ang
  -> bounded (live_globals DL) (fst (getAnn ang))
  -> noUnreachableCode s
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros. general induction H; simpl; invt locally_inj; invt live_sound;
          invt @ann_R; invt noUnreachableCode.
  - econstructor. simpl in *. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). {
      rewrite update_id; eauto.
    }
    rewrite H10. eapply IHrenamedApart; eauto.
    assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
    split; intuition. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H14.
    cset_tac; intuition. invc H16; eauto.
    pe_rewrite; simpl in *. rewrite <- incl_add'; eauto.
  - econstructor; eauto. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    eapply IHrenamedApart1; eauto using inverse_on_incl.
    pe_rewrite; eauto.
    eapply IHrenamedApart2; eauto using inverse_on_incl.
    pe_rewrite; eauto.

  - econstructor; eauto. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.

  - econstructor; eauto. rewrite map_length. eauto.
    intros. edestruct map_get_4; eauto; dcr; subst.
    get_functional; eauto; subst.
    eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.

  - econstructor.
    + rewrite map_length; eauto.
    + intros. edestruct map_get_4; eauto; dcr; subst.
      get_functional; eauto; subst.
      eapply alpha_exp_rename_injective.
      eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    +
      assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). {
        rewrite update_id; eauto.
      }
      rewrite H10. eapply IHrenamedApart; eauto.
      assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
        split; intuition. rewrite update_id. reflexivity. intuition.
      }
      eapply locally_inj_morphism; eauto.
      eapply inverse_on_update_minus; eauto using inverse_on_incl,
                                      locally_injective.
      eapply injective_on_incl. eapply locally_injective, H15.
      cset_tac; intuition. invc H14; eauto.
      pe_rewrite; eauto. rewrite <- incl_add'; eauto.
  - exploit renamedApart_globals_live; eauto.
    hnf; intros. inv H13. pe_rewrite.
    eapply renamedApart_disj in H4. pe_rewrite; eauto.
    eapply ann_R_get in H28. pe_rewrite. rewrite H28.
    revert H4; unfold disj; clear_all; cset_tac; intuition; eauto.
    eapply bounded_disjoint; eauto. simpl.
    eapply renamedApart_disj in H4. pe_rewrite; eauto.
    destruct X; dcr. invc H14; simpl in *.
    constructor.
    + rewrite lookup_list_length; eauto.
    + rewrite update_with_list_lookup_list.
      eapply IHrenamedApart1; eauto.
      assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
      simpl in H6.
      eapply inverse_on_update_with_list; try intuition.
      eapply injective_on_incl. eapply locally_injective, H16.
      cset_tac; intuition.
      eapply inverse_on_incl; eauto; intuition.
      eapply inverse_on_incl; eauto; intuition.
      simpl. split; pe_rewrite. rewrite H15, H27, H20. eapply incl_right.
      rewrite <- incl_right; eauto. intuition.
    + eapply IHrenamedApart2; eauto using inverse_on_incl.
      simpl. split; pe_rewrite. rewrite H15, H27, H20. reflexivity.
      eauto.
Qed.


(** ** local injectivity only looks at variables occuring in the program *)

Lemma locally_inj_live_agree s ϱ ϱ' ara alv LV
      (LS:live_sound FunctionalAndImperative LV s alv)
      (sd: renamedApart s ara)
      (inj: locally_inj ϱ s alv)
      (agr: agree_on eq (fst (getAnn ara) ∪ snd (getAnn ara)) ϱ ϱ')
      (incl:getAnn alv ⊆ fst (getAnn ara))
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction inj; invt renamedApart; invt live_sound; simpl in *.
  - econstructor; eauto.
    + eapply IHinj; eauto.
      rewrite H8 in agr.
      rewrite H7; simpl. eapply agree_on_incl; eauto. cset_tac; intuition.
      rewrite H7; simpl.
      rewrite <- incl, <- H13.
      clear_all; cset_tac; intuition.
      decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; try eapply agr.
      rewrite H8. rewrite incl. eapply incl_left.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto. rewrite incl. eapply incl_left.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite incl. eapply incl_left.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite incl. eapply incl_left.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H8; simpl; eauto.
      eapply agree_on_incl; eauto. rewrite H9.
      clear_all; cset_tac; intuition.
      rewrite H8. simpl. rewrite <- incl, <- H14.
      clear_all; cset_tac; intuition.
      decide (x === a); intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite incl. eapply incl_left.
  - econstructor; eauto.
    + eapply IHinj1; eauto.
      eapply agree_on_incl; eauto.
      rewrite H7; simpl. rewrite <- H5. clear_all; cset_tac; intuition.
      rewrite H7; simpl. rewrite <- incl. rewrite <- H18.
      clear_all; cset_tac; intuition.
    + eapply IHinj2; eauto.
      eapply agree_on_incl; eauto.
      rewrite H10. simpl. rewrite <- H5. cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl. rewrite <- H19. reflexivity.
    +  eapply injective_on_agree; eauto.
       eapply agree_on_incl; eauto.
       rewrite incl. eapply incl_left.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
