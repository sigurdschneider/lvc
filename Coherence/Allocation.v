Require Import CSet Le.

Require Import Plus Util Map DecSolve.
Require Import Env EnvTy IL Annotation Liveness Coherence Alpha Restrict RenamedApart.

Set Implicit Arguments.

(** Renaming respects function equivalence *)

Global Instance rename_morphism
  : Proper (@feq _ _ _eq ==> eq ==> eq) rename.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; f_equal; eauto; try (now rewrite H; eauto);
  eauto using rename_exp_ext, map_ext_get_eq; eauto.
Qed.

(** Inductive definition of local injectivity of a renaming rho *)

Inductive locally_inj (rho:env var) : stmt -> ann (set var) -> Prop :=
| RNOpr x b lv e (al:ann (set var))
  :  locally_inj rho b al
  -> injective_on lv rho
  -> injective_on (getAnn al ∪ {{x}}) rho
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
  -> injective_on (getAnn al ∪ {{x}}) rho
  -> locally_inj rho (stmtExtern x f Y b) (ann1 lv al)
| RNLet s Z b lv (alvs alvb:ann (set var))
  : locally_inj rho s alvs
  -> locally_inj rho b alvb
  -> injective_on lv rho
  -> injective_on (getAnn alvs ∪ of_list Z) rho
  -> locally_inj rho (stmtFun Z s b) (ann2 lv alvs alvb).

(** local injectivity is decidable *)

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  general induction s; destruct lv; try (now exfalso; inv an).
  + decide(injective_on a ϱ);
    decide(injective_on (getAnn lv ∪ {{x}}) ϱ); try dec_solve;
    edestruct IHs; eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct IHs1; eauto; try inv an; eauto; try dec_solve;
    edestruct IHs2; eauto; try inv an; eauto; try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ);
    decide(injective_on (getAnn lv ∪ {{x}}) ϱ); try dec_solve;
    edestruct IHs; eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ);
    decide (injective_on (getAnn lv1 ∪ of_list Z) ϱ); try dec_solve;
    edestruct IHs1; eauto; try inv an; eauto; try dec_solve;
    edestruct IHs2; eauto; try inv an; eauto; try dec_solve.
Defined.

(** local injectivity can only hold if [lv] is a valid annotation *)

Lemma locally_inj_annotation (ϱ:env var) (s:stmt) (lv:ann (set var))
: locally_inj ϱ s lv -> annotation s lv.
Proof.
  intros. general induction H; econstructor; eauto.
Qed.

(** local injectivity is decidable *)

Instance locally_inj_dec_inst (ϱ:env var) (s:stmt) (lv:ann (set var))
         `{Computable (annotation s lv)}
  : Computable (locally_inj ϱ s lv).
Proof.
  destruct H as [].
  hnf; eauto using locally_inj_dec.
  right; intro; eauto using locally_inj_annotation.
Defined.

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
        cset_tac; intuition. decide (a === x); intuition. right. eapply INCL.
        eapply H10. cset_tac; intuition.
        rewrite H12. simpl in *.
        assert (D ⊆ {x; D}) by (cset_tac; intuition).
        rewrite H2 in H1; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H10. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        reflexivity. rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition. eauto.
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
        eapply H11. cset_tac; intuition.
        rewrite H13. simpl in *.
        assert (D ⊆ {x; D}). cset_tac; intuition.
        rewrite H2 in H1; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H11. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        reflexivity. rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus. intuition. eauto.
        cset_tac; intuition.
  - econstructor; eauto.
    + eapply srd_monotone.
      * eapply IHRI1; eauto. simpl in *. rewrite H14; simpl.
        rewrite <- INCL. rewrite <- H12. eapply incl_union_minus.
        simpl. split. simpl in *. rewrite H12, H14; simpl. cset_tac; intuition.
        assert (D ⊆ of_list Z ∪ D) by (cset_tac; intuition).
        rewrite H14. simpl. rewrite <- H2; eauto.
      * Opaque restrict. simpl. unfold live_global. rewrite restrict_incl. simpl.
        simpl. rewrite restrict_incl. constructor. constructor.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_eq; eauto; intuition. intuition.
        erewrite (@restrict_incl_ext _ (getAnn alvs)); eauto.
        instantiate (1:=getAnn alvs \ of_list Z).
        eapply list_eq_special; eauto.
        rewrite getAnn_mapAnn. rewrite of_list_lookup_list.
        eapply lookup_set_minus_incl_inj; eauto; intuition. intuition.
        simpl. simpl in *.
        cset_tac; intuition. eauto. reflexivity.
        eapply incl_minus.

    + eapply srd_monotone. simpl in * |- *.
      eapply IHRI2; eauto.
      rewrite H17; simpl in * |- *; eauto. transitivity lv; eauto.
      rewrite H17; simpl.
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


Open Scope set_scope.

Lemma ssa_locally_inj_alpha s ϱ ϱ' DL (slv:ann (set var)) ang
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
  - constructor.
    + rewrite lookup_list_length; eauto.
    + rewrite update_with_list_lookup_list.
      eapply IHrenamedApart1; eauto.
      assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
      simpl in H6.
      eapply inverse_on_update_with_list; try intuition.
      eapply inverse_on_incl; eauto; intuition. intuition.
    + eapply IHrenamedApart2; eauto using inverse_on_incl.
Qed.

Fixpoint norm_rho ra s s' : env var :=
  match s, s' with
    | stmtLet x e s, stmtLet x' e' s' => norm_rho (ra[x<- x']) s s'
    | stmtIf _ s t, stmtIf _ s' t' => norm_rho (norm_rho ra s s') t t'
    | stmtFun Z s t, stmtFun Z' s' t' => norm_rho (norm_rho (ra [Z <-- Z']) s s') t t'
    | _, _ => ra
  end.

(*

Lemma ssa_rename_alpha C C' s s' ra ira
  : ssa C s C' -> alpha ra ira s s' ->
    rename (norm_rho ra s s') s = s'.
Proof.
  intros. general induction H0; simpl in *.
  + rewrite H; eauto.
  + f_equal. eauto.


Lemma ssa_rename_alpha C C' s s' ra ira
  : ssa C s C' -> alpha ra ira s s' ->
    locally_inj (norm_rho ra s s') s .
Proof.
*)

(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
