Require Import CSet Le.

Require Import Plus Util Map DecSolve.
Require Import Env EnvTy IL Liveness Coherence Alpha ParamsMatch Restrict.
 
Set Implicit Arguments.

(** Renaming respects function equivalence *) 

Global Instance rename_morphism 
  : Proper (feq ==> eq ==> eq) rename.
Proof.
  unfold Proper, respectful; intros; subst.
  general induction y0; simpl; f_equal; eauto; try (now rewrite H; eauto).
  eapply rename_exp_ext; eauto.
Qed.

(* renaming preserves correspondence of parameters and arguments *)

Lemma rename_parameters_match {B} `{BlockType B} (L:list B) ϱ s
  : labenv_parameters_match L
 -> parameters_match (labenvZ L) s
 -> parameters_match (labenvZ L) (rename ϱ s).
Proof.
  intros. general induction s; simpl; inv H1; eauto using parameters_match.
  + econstructor; eauto. rewrite lookup_list_length; eauto.
  + edestruct (block_ctor s1 Z); dcr; subst.
    assert (labenv_parameters_match (x::L)).
    hnf; intros. inv H2; eauto.
    econstructor; rewrite lookup_list_length.
    eapply (IHs1 _ _ _ _ H2); eauto.
    eapply (IHs2 _ _ _ _ H2); eauto.
Qed.

Lemma rename_params_match {B} `{BlockType B} (L:list B) ϱ s
  : params_match L s 
    -> params_match L (rename ϱ s).
Proof.
  intros [A A']; split; eauto. 
  eapply rename_parameters_match; eauto.
Qed.

(** Inductive definition of local injectivity of a renaming rho *)

Inductive locally_inj (rho:env var) : stmt -> ann (set var) -> Prop :=
| RNOpr x b lv e (al:ann (set var))
  :  locally_inj rho b al
  -> injective_on lv rho
  -> injective_on (getAnn al ∪ {{x}}) rho
  -> locally_inj rho (stmtExp x e b) (annExp lv al)
| RNIf x b1 b2 lv (alv1 alv2:ann (set var))
  :  injective_on lv rho
  -> locally_inj rho b1 alv1
  -> locally_inj rho b2 alv2
  -> locally_inj rho (stmtIf x b1 b2) (annIf lv alv1 alv2)
| RNGoto l Y lv 
  : injective_on lv rho
  -> locally_inj rho (stmtGoto l Y) (annGoto lv)
| RNReturn x lv
  : injective_on lv rho
  -> locally_inj rho (stmtReturn x) (annReturn lv)
| RNLet s Z b lv (alvs alvb:ann (set var))
  : locally_inj rho s alvs
  -> locally_inj rho b alvb
  -> injective_on lv rho
  -> injective_on (getAnn alvs ∪ of_list Z) rho
  -> inj_mapping (lookup_set rho (getAnn alvs\of_list Z)) Z (lookup_list rho Z)
  -> locally_inj rho (stmtLet Z s b) (annLet lv alvs alvb).

(** local injectivity is decidable *)

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  general induction s; destruct lv; try (now exfalso; inv an). 
  + destruct_prop(injective_on a ϱ);
    destruct_prop(injective_on (getAnn lv ∪ {{x}}) ϱ); try dec_solve;
    edestruct IHs; eauto; try dec_solve; inv an; eauto.
  + destruct_prop(injective_on a ϱ); try dec_solve;
    edestruct IHs1; eauto; try inv an; eauto; try dec_solve;
    edestruct IHs2; eauto; try inv an; eauto; try dec_solve.
  + destruct_prop(injective_on a ϱ); try dec_solve.
  + destruct_prop(injective_on a ϱ); try dec_solve.
  + destruct_prop(injective_on a ϱ);
    destruct_prop (injective_on (getAnn lv1 ∪ of_list Z) ϱ);
    destruct_prop (inj_mapping (lookup_set ϱ (getAnn lv1 \ of_list Z)) Z (lookup_list ϱ Z)); try dec_solve;
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
  destruct H as [[]].
  econstructor; eauto using locally_inj_dec.
  constructor; right; intro; eauto using locally_inj_annotation.
Defined.

(** local injectivity respects functional equivalence (if the function itself is injective wrt. the underlying equivalence) *)

Global Instance locally_inj_morphism
  : Proper (fpeq ==> eq ==> eq ==> impl) locally_inj.
Proof.    
  unfold Proper, respectful, impl; intros; subst.
  general induction H2; assert (FEQ:x ≡ y) by first [eapply H0 | eapply H1 | eapply H2];  econstructor; eauto;
  try rewrite <- FEQ; eauto. 
  assert (lookup_set y (getAnn alvs \ of_list Z) [=] lookup_set x (getAnn alvs \ of_list Z)).
  rewrite H2. reflexivity.
  rewrite H3. assert (lookup_list y Z = lookup_list x Z).
  rewrite FEQ; eauto. rewrite H4. eauto.
Qed.

(** local injectivity means injectivity on the live variables *)
Lemma locally_injective s (slv:ann (set var)) ϱ
  : locally_inj ϱ s slv
  -> injective_on (getAnn slv) ϱ.
Proof.
  intros. general induction H; eauto.
Qed.

Lemma rename_ssa_srd C C' s ϱ (alv:ann (set var)) Lv 
  : ssa C s C'
  -> (getAnn alv) ⊆ C 
  -> live_sound Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_globals Lv) C
  -> srd (map_lookup ϱ (restrict (live_globals Lv) (getAnn alv)))
        (rename ϱ s)
        (mapAnn (lookup_set ϱ) alv).
Proof. 
  intros SSA INCL LS RI.
  general induction RI; inv LS; subst; inv SSA; simpl.
  + econstructor. 
    - eapply srd_monotone. 
      * eapply IHRI; eauto. simpl in *. 
        cset_tac; intuition. destruct_prop (a === x); intuition. left. eapply INCL.
        eapply H10. cset_tac; intuition.
        assert (C ⊆ C ∪ {{x}}). cset_tac; intuition.
        rewrite H2 in H1; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special. rewrite <- H10. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        reflexivity. rewrite lookup_set_singleton; intuition. 
        rewrite meet_comm. eapply meet_minus. intuition. eauto.
        cset_tac; intuition. inversion 1; subst. intuition.
  + econstructor. simpl in *. 
    - eapply srd_monotone. eapply IHRI1; eauto using Subset_trans, lookup_set_incl; eauto;
                           try (now eapply Subset_trans; eauto).
      eapply list_eq_fstNoneOrR_incl; eauto. 
    - eapply srd_monotone. eapply IHRI2; eauto; try (now eapply Subset_trans; eauto).
      eapply list_eq_fstNoneOrR_incl; eauto. 
  + econstructor. 
    instantiate (1:= lookup_set ϱ (blv \ of_list Z)).
    unfold live_globals. 
    pose proof (map_get_1 live_global H4).  
    pose proof (map_get_1 (restr lv) H1).
    pose proof (map_get_1 (lookup_set_option ϱ) H2).
    assert (restr lv (live_global (blv, Z)) = Some (blv \ of_list Z)).
    eapply restr_iff; intuition. rewrite H9 in H3. eapply H3.
    eapply lookup_set_incl; intuition.
  + econstructor.

  + econstructor; eauto.
    eapply srd_monotone. eapply IHRI1; eauto. simpl in *.
    rewrite <- INCL. rewrite <- H13. eapply incl_union_minus.
    simpl. split. rewrite H13. cset_tac; intuition. 
    assert (C ⊆ of_list Z ∪ C) by (cset_tac; intuition). rewrite <- H3; eauto.
    Opaque restrict. simpl. unfold live_global. rewrite restrict_incl. simpl. 
    simpl. rewrite restrict_incl. constructor. constructor.
    rewrite getAnn_mapAnn. admit.
    erewrite (@restrict_incl_ext _ (getAnn alvs)); eauto.
    instantiate (1:=getAnn alvs \ of_list Z).
    eapply list_eq_special; eauto.
    rewrite getAnn_mapAnn. admit. 
    cset_tac; intuition. eapply H4; eauto. reflexivity.
    eapply incl_minus. 
    
    eapply srd_monotone. eapply IHRI2; eauto. transitivity lv; eauto.
    simpl. split; eauto. eapply Subset_trans; eauto.
    simpl. 
    simpl. destruct_prop (getAnn alvs \ of_list Z ⊆ getAnn alvb). 
    unfold live_global. simpl.
    rewrite restrict_incl; eauto. simpl. econstructor. econstructor; eauto.
    rewrite getAnn_mapAnn. admit.
    eapply list_eq_fstNoneOrR_incl; eauto.
    unfold live_global. simpl. rewrite restrict_not_incl; eauto. simpl.
    econstructor. econstructor. eapply list_eq_fstNoneOrR_incl; eauto.
Qed.

Open Scope set_scope.

Lemma ssa_locally_inj_alpha G G' s ϱ ϱ' DL (slv:ann live)
  : ssa G s G'
  -> locally_inj ϱ s slv
  -> live_sound DL s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros. general induction H; simpl. 
  inv H2. inv H3.
  econstructor. simpl in *. eapply alpha_exp_rename_injective. 
  eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
  assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). { 
    rewrite update_id; eauto. intuition. 
  } 
  rewrite H5. eapply IHssa; eauto. assert (fpeq ϱ (update ϱ x (ϱ x))).
  split; intuition. rewrite update_id. reflexivity. intuition.
  eapply locally_inj_morphism; eauto.
  eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.

  inv H5. inv H4.
  econstructor; eauto. eapply H6; eauto.
  now eapply IHssa1; eauto using inverse_on_incl.
  now eapply IHssa2; eauto using inverse_on_incl.

  econstructor; eauto. eapply H3. now inv H2; eauto.
  econstructor; eauto. inv H2. inv H1.
  pose proof (inverse_on_lookup_list Y H3 H11); eauto.
  eapply list_eq_eq. eapply H4.
  
  inv H5; inv H4.
  constructor. rewrite lookup_list_length; eauto.
  rewrite update_with_list_lookup_list.
  eapply IHssa1; eauto.
  assert (fpeq ϱ ϱ). split. reflexivity. split; intuition.
  simpl in H6. 
  eapply inverse_on_update_with_list; try intuition.
  eapply inverse_on_incl; eauto; intuition. intuition.
  eapply IHssa2; eauto using inverse_on_incl.
Qed.

(*
Lemma ssa_rename_alpha C C' s s' ra ira 
  : ssa C s C' -> alpha ra ira s s' -> 
    rename (norm_rho ra s) s = s'.
Proof.
  intros. general induction H0; simpl in *.
  + rewrite H. eauto.
  + f_equal. eauto.
  + inversion H1. subst C C' x0 e0 s0.
    f_equal. 
    eexists (x0 [x <- y]). simpl. 
    f_equal. lud. exfalso; eauto.
    assert (agree_on (Exp.freeVars e) (x0[x<-y]) x0).
    eapply agree_on_update_dead; eauto. reflexivity.

    assert (agree_on (freeVars s) (x0[x<-y]) x0).
    eapply agree_on_update_dead. eapply ssa_freeVars in H9.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*) 

