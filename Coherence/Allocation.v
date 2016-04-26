Require Import CSet Le.

Require Import Plus Util Map DecSolve AllInRel.
Require Import Env EnvTy IL Annotation Liveness Coherence Alpha Restrict RenamedApart.
Require Import Rename RenamedApart_Liveness.

Set Implicit Arguments.

(** * Local Injectivity *)

(** ** Inductive definition of local injectivity of a renaming rho *)

Inductive locally_inj (rho:env var) : stmt -> ann (set var) -> Prop :=
| RNOpr x b lv e (al:ann (set var))
  :  locally_inj rho b al
     -> injective_on lv rho
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
    -> locally_inj rho (stmtExtern x f Y b) (ann1 lv al)
| RNLet F b lv alvs alvb
  : length F = length alvs
    -> (forall n Zs alv, get F n Zs -> get alvs n alv -> locally_inj rho (snd Zs) alv)
    -> locally_inj rho b alvb
    -> injective_on lv rho
    -> locally_inj rho (stmtFun F b) (annF lv alvs alvb).

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
  general induction H2;
    assert (FEQ:x [-] y) by first [eapply H0 | eapply H1 | eapply H2 | eapply H4 ];  econstructor; eauto;
    try rewrite <- FEQ; eauto.
Qed.

(** local injectivity means injectivity on the live variables *)
Lemma locally_injective s (slv:ann (set var)) ϱ
  : locally_inj ϱ s slv
  -> injective_on (getAnn slv) ϱ.
Proof.
  intros. general induction H; eauto.
Qed.

(** ** Renaming with a locally injective renaming yields a coherent program *)

Lemma live_globals_bounded F alvs lv
: ( forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
      get F n Zs ->
      get alvs n a ->
      of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
  -> bounded
      (live_global ⊝ (zip pair (getAnn ⊝ alvs) (fst ⊝ F))) lv.
Proof.
  intros.
  rewrite map_zip.
  eapply get_bounded; intros; inv_get.
  edestruct H; eauto.
Qed.

Lemma map_lookup_app L L' ϱ
: map_lookup ϱ (L ++ L') = map_lookup ϱ L ++ map_lookup ϱ L'.
Proof.
  unfold map_lookup. rewrite List.map_app. reflexivity.
Qed.

Ltac norm_map_zip :=
  unfold map_lookup, restrict;
  repeat (progress (repeat rewrite List.map_app;
                    repeat rewrite List.map_map;
                    repeat rewrite map_zip;
                    repeat rewrite zip_map_l;
                    repeat rewrite zip_map_r)).

Lemma PIR2_rename Lv ϱ alvs F ans Dt D lv x0 x n x1
      (H0 : forall (n : nat) (Zs : params * stmt) (alv : ann (set var)),
              get F n Zs -> get alvs n alv -> locally_inj ϱ (snd Zs) alv)
      (H8 : Indexwise.indexwise_R (funConstr D Dt) F ans)
      (H13 : forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
               get F n Zs ->
               get alvs n a ->
               of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
      (H19 :get alvs n x0)
      (H17 :get F n x)
      (H20 : get ans n x1)
      (H11 : length F = length alvs)
      (BND:bounded (live_global ⊝ Lv) D)
      (INCL: lv ⊆ D)
: PIR2 (fstNoneOrR Equal)
                (map_lookup ϱ
                            (restrict (live_global ⊝ (zip pair (getAnn ⊝ alvs) (fst ⊝ F) ++ Lv))
                                      (getAnn x0)))
                (restrict
                   (oglobals
                      (List.map
                         (fun Zs : params * stmt =>
                            (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) F)
                      (List.map (mapAnn (lookup_set ϱ)) alvs) ++
                      map_lookup ϱ (restrict (live_global ⊝ Lv) lv))
                   (getAnn (mapAnn (lookup_set ϱ) x0) \
                           of_list (fst (lookup_list ϱ (fst x), rename ϱ (snd x))))).
Proof.
  simpl.
  rewrite map_app.
  repeat rewrite restrict_app.
  rewrite map_lookup_app.
  eapply PIR2_app.
  rewrite getAnn_mapAnn.
  rewrite of_list_lookup_list; eauto.
  erewrite (@restrict_incl_ext _ (getAnn x0)); eauto.
  instantiate (1:=getAnn x0 \ of_list (fst x)).
  - norm_map_zip.
    eapply PIR2_get; [ intros; inv_get | eauto with len].
    rewrite getAnn_mapAnn. unfold lminus; simpl.
    repeat cases; simpl; try now econstructor.
    + econstructor.
      rewrite of_list_lookup_list; eauto.
      eapply lookup_set_minus_eq; eauto.
      exploit H13 as A; eauto. simpl in *; dcr.
      exploit H0 as INJ; eauto. eapply locally_injective in INJ.
      eapply injective_on_incl; eauto with cset.
    + exfalso. eapply NOTCOND.
      rewrite of_list_lookup_list; eauto.
      repeat rewrite <- lookup_set_minus_eq; eauto.
      eapply lookup_set_incl; eauto.
      exploit H13; try eapply H19; eauto. simpl in *; dcr.
      exploit H0 as INJ; try eapply H19; eauto. eapply locally_injective in INJ.
      eapply injective_on_incl; eauto with cset.
      exploit H13; eauto. simpl in *; dcr.
      exploit H0 as INJ; eauto. eapply locally_injective in INJ.
      eapply injective_on_incl; eauto with cset.
  - instantiate (1:=D).
    simpl in H13. simpl in *. rewrite <- INCL.
    eapply live_globals_bounded; eauto.
  - edestruct H8; eauto; dcr.
    revert H4; clear_all; cset_tac; eauto.
  - simpl.
    erewrite (@restrict_incl_ext _ (getAnn x0)); eauto.
    instantiate (1:=getAnn x0 \ of_list (fst x)).
    eapply list_eq_special; eauto.
    edestruct H13; eauto.
    rewrite getAnn_mapAnn. rewrite of_list_lookup_list; eauto.
    eapply lookup_set_minus_incl_inj; eauto.
    + exploit H0; try eapply H19; eauto.
      eapply locally_injective in H.
      eapply injective_on_incl; eauto with cset.
      exploit H13; eauto; dcr. eauto with cset.
    + edestruct H8; eauto; dcr.
      revert H4; clear_all; cset_tac.
Qed.


Instance fstNoneOrR_flip_Subset_trans2 {X} `{OrderedType X} :
  Transitive (fstNoneOrR Equal).
Proof.
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Lemma PIR2_map_lookup ϱ A B
  : PIR2 (fstNoneOrR (flip Subset)) A B ->
    PIR2 (fstNoneOrR (flip Subset)) (map_lookup ϱ A) (map_lookup ϱ B).
Proof.
  intros. general induction H; simpl; eauto using PIR2.
  econstructor; eauto.
  inv pf; simpl; econstructor. unfold flip in *. rewrite H0; eauto.
Qed.


Lemma PIR2_oglobals ϱ F alvs Lv (alvb:ann(set var)) lv
      (LEN:length F = length alvs) (A:getAnn alvb ⊆ lv)
  : PIR2 (fstNoneOrR (flip Subset))
     (map_lookup ϱ
        (restrict (live_global ⊝ (pair ⊜ (getAnn ⊝ alvs) (fst ⊝ F) ++ Lv))
           (getAnn alvb)))
     (oglobals ((fun Zs : params * stmt =>
                 (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) ⊝ F)
      (mapAnn (lookup_set ϱ) ⊝ alvs) ++
      map_lookup ϱ (restrict (live_global ⊝ Lv) lv)).
Proof.
  rewrite map_app. rewrite restrict_app.
  rewrite map_lookup_app. eapply PIR2_app; eauto using list_eq_fstNoneOrR_incl.
  - norm_map_zip.
    eapply AllInRel.PIR2_get; intros; inv_get; eauto with len.
    unfold lookup_set_option, restr, live_global; simpl.
    cases; eauto using @fstNoneOrR.
    + rewrite getAnn_mapAnn. econstructor. unfold flip, lminus.
      rewrite of_list_lookup_list; eauto. eapply lookup_set_minus_incl; eauto.
  - eapply PIR2_map_lookup. eapply restrict_subset2; eauto.
Qed.

Lemma rename_renamedApart_srd s ang ϱ (alv:ann (set var)) Lv
  : renamedApart s ang
    -> (getAnn alv) ⊆ fst (getAnn ang)
    -> live_sound FunctionalAndImperative Lv s alv
    -> locally_inj ϱ s alv
    -> bounded (live_global ⊝ Lv) (fst (getAnn ang))
    -> srd (map_lookup ϱ (restrict (live_global ⊝ Lv) (getAnn alv)))
          (rename ϱ s)
          (mapAnn (lookup_set ϱ) alv).
Proof.
  intros SSA INCL LS RI.
  general induction RI; inv LS; subst; inv SSA; simpl in * |- *; pe_rewrite.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto; pe_rewrite.
        rewrite <- INCL; eauto with cset.
        eauto using bounded_incl with cset.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ singleton x).
        eapply list_eq_special; eauto with cset.
        rewrite lookup_set_minus_incl_inj; eauto. rewrite <- minus_inane_set.
        instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; eauto. eapply lookup_set_incl; eauto.
        rewrite lookup_set_singleton'; eauto.
        rewrite meet_comm. eapply meet_minus.
        assert (getAnn al [=] getAnn al ∪ singleton x). cset_tac; intuition.
        rewrite <- H1. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor. simpl in *.
    + eapply srd_monotone.
      eapply IHRI1; eauto using Subset_trans, lookup_set_incl; eauto;
      try (now eapply Subset_trans; eauto); pe_rewrite.
      etransitivity; eauto.
      eauto using bounded_incl.
      eapply list_eq_fstNoneOrR_incl; eauto.
    + eapply srd_monotone.
      eapply IHRI2; eauto; pe_rewrite; eauto with cset.
      eapply list_eq_fstNoneOrR_incl; eauto.
  - econstructor.
    instantiate (1:= lookup_set ϱ (blv \ of_list Z)).
    pose proof (map_get_1 live_global H4).
    pose proof (map_get_1 (restr lv) H1).
    pose proof (map_get_1 (lookup_set_option ϱ) H2).
    assert (RESTR:restr lv (live_global (blv, Z)) = Some (blv \ of_list Z)) by
        (eapply restr_iff; eauto).
    rewrite RESTR in H5. eauto.
  - econstructor.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. pe_rewrite. eauto with cset.
        pe_rewrite. eauto with cset.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ singleton x).
        eapply list_eq_special. rewrite <- H10. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; eauto. eapply lookup_set_incl; eauto.
        rewrite lookup_set_singleton'; eauto.
        rewrite meet_comm. eapply meet_minus. intuition.
        assert (getAnn al [=] getAnn al ∪ singleton x). cset_tac; intuition.
        rewrite <- H1. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor; eauto with len.
    + intros.
      inv_map H4. inv_map H5.
      edestruct (get_length_eq _ H17 H6).
      eapply srd_monotone.
      * edestruct H8; eauto; dcr.
        eapply (H1 _ _ _ H17 H19); eauto. simpl in *.
        rewrite H21. exploit H13; eauto; dcr. rewrite <- INCL, <- H27.
        clear_all; cset_tac; intuition.
        rewrite H21. rewrite List.map_app.
        rewrite <- incl_right.
        rewrite bounded_app. simpl in *. split; eauto.
        eapply get_bounded; intros; inv_get; simpl in *.
        exploit H13; eauto; dcr. eauto with cset.
      * eapply PIR2_rename; eauto.
    + eapply srd_monotone2. simpl in * |- *.
      * eapply IHRI; eauto; pe_rewrite; eauto with cset.
        rewrite List.map_app.
        rewrite bounded_app; split; eauto.
        eapply get_bounded; intros; inv_get; simpl in *.
        exploit H13; eauto; dcr. eauto with cset.
      * eapply PIR2_oglobals; eauto.
Qed.

Lemma locally_inj_subset ϱ s alv alv'
: locally_inj ϱ s alv
  -> ann_R Subset alv' alv
  -> locally_inj ϱ s alv'.
Proof.
  intros.
  general induction H; invt @ann_R; simpl in *; eauto 20 using locally_inj, injective_on_incl.
  - econstructor; eauto using injective_on_incl; try congruence.
    + intros. edestruct get_length_eq; eauto.
Qed.

Lemma bounded_disjoint Lv u v
: bounded (live_global ⊝ Lv) u
  -> disj u v
  -> disjoint (live_global ⊝ Lv) v.
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

Hint Resolve meet1_incl2 : cset.

Lemma meet1_Subset1 s alv ang
: annotation s alv
  -> annotation s ang
  -> ann_R Subset1 (mapAnn2 meet1 alv ang) ang.
Proof.
  intros AN1 AN2; general induction AN1; inv AN2; simpl; eauto using @ann_R, meet1_incl2.
  - econstructor; eauto with cset len.
    + intros; inv_get.
      symmetry in H. edestruct get_length_eq; try eapply H; eauto.
Qed.

Lemma rename_renamedApart_srd' s ang ϱ (alv:ann (set var)) Lv
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_global ⊝ Lv) (fst (getAnn ang))
  -> LabelsDefined.noUnreachableCode s
  -> srd
        (map_lookup ϱ
           (restrict (live_global ⊝ Lv) (getAnn (mapAnn2 meet1 alv ang))))
        (rename ϱ s) (mapAnn (lookup_set ϱ) (mapAnn2 meet1 alv ang)).
Proof.
  intros.
  exploit live_sound_renamedApart_minus; eauto.
  eapply renamedApart_live_imperative_is_functional in H4; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply rename_renamedApart_srd in H4; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
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
    -> bounded (live_global ⊝ Lv) (fst (getAnn ang))
    -> noUnreachableCode s
    -> srd (map_lookup ϱ (restrict (live_global ⊝ Lv) (getAnn alv)))
          (rename ϱ s)
          (mapAnn (lookup_set ϱ) alv).
Proof.
  intros SSA LS INCL RI BOUND UNREACH.
  general induction RI; inv LS; subst; inv SSA; inv INCL; inv UNREACH; simpl.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. pe_rewrite.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ singleton x).
        eapply list_eq_special. rewrite <- H8. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; eauto. eapply lookup_set_incl; eauto.
        rewrite lookup_set_singleton'; eauto.
        rewrite meet_comm. eapply meet_minus. eauto.
        assert (getAnn al [=] getAnn al ∪ singleton x). cset_tac; intuition.
        rewrite <- H0. eauto using locally_injective.
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
    pose proof (map_get_1 live_global H3).
    pose proof (map_get_1 (restr lv) H0).
    pose proof (map_get_1 (lookup_set_option ϱ) H1).
    assert (restr lv (live_global (blv, Z)) = Some (blv \ of_list Z)).
    eapply restr_iff; intuition. rewrite H10 in H9.
    eapply H9.
  - econstructor.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. simpl in *. pe_rewrite.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ singleton x).
        eapply list_eq_special. rewrite <- H9. cset_tac; intuition.
        rewrite lookup_set_minus_incl_inj. rewrite <- minus_inane_set.
        instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; eauto. eapply lookup_set_incl; eauto.
        rewrite lookup_set_singleton'; eauto.
        rewrite meet_comm. eapply meet_minus. eauto.
        assert (getAnn al [=] getAnn al ∪ singleton x). cset_tac; intuition.
        rewrite <- H0. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor; eauto.
    + repeat rewrite map_length; eauto.
    + intros. inv_map H3. inv_map H4.
      edestruct get_length_eq; try eapply H5; eauto.
      eapply srd_monotone.
      * eapply H1; eauto. simpl in *. edestruct H7; eauto; dcr. rewrite H27.
        rewrite map_app.
        rewrite bounded_app; split; eauto using bounded_incl with cset.
        eapply live_globals_bounded.
        intros. split. eapply H12; eauto.
        edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H36.
        destruct (getAnn x2); simpl in *. rewrite H36.
        rewrite H34. clear_all; cset_tac; intuition.
      * eapply PIR2_rename; eauto.
        simpl in *.
        split. eapply H12; eauto.
        edestruct get_length_eq; eauto.
        edestruct H7; eauto; dcr.
        exploit H19; eauto using get_range.
        edestruct renamedApart_globals_live; eauto.
        hnf; intros. pe_rewrite.
        eapply renamedApart_disj in H14. pe_rewrite; eauto.
        exploit H23; eauto. eapply ann_R_get in H36.
        rewrite map_app in H33.
        eapply get_app_cases in H33. destruct H33; dcr.
        rewrite map_zip in H33. inv_get.
        edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto; dcr.
        exploit H23; eauto. eapply ann_R_get in H10.
        destruct (getAnn x3); simpl in *.
        rewrite H10. rewrite H4. eapply disj_1_incl; try eapply H14.
        clear_all; cset_tac; intuition.
        eapply disj_1_incl. eapply H14.
        eapply bounded_get in H37. eapply H37. eauto.
        dcr; simpl in *.
        eapply get_app_lt_1 in H36; eauto.
        inv_get.
        simpl in H37. rewrite H37. eauto.
        eauto with len.
    + eapply srd_monotone2. simpl in * |- *.
      eapply IHRI; eauto.
      rewrite H15; simpl in * |- *; eauto.
      rewrite map_app. rewrite bounded_app. split; eauto.
      eapply live_globals_bounded; intros; split.
      * eapply H12; eauto.
      * edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H27.
        destruct (getAnn x); simpl in *. rewrite H27.
        rewrite H25. clear_all; cset_tac; intuition.
      * eapply PIR2_oglobals; eauto.
Qed.


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
    split; eauto. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H11.
    cset_tac; intuition.
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
        split; eauto. rewrite update_id. reflexivity. intuition.
      }
      eapply locally_inj_morphism; eauto.
      eapply inverse_on_update_minus; eauto using inverse_on_incl,
                                      locally_injective.
      eapply injective_on_incl. eapply locally_injective, H12.
      cset_tac; intuition.
  - constructor.
    + rewrite map_length; eauto.
    + intros. inv_map H11; simpl. rewrite lookup_list_length; eauto.
    + intros. inv_map H11. simpl.
      rewrite update_with_list_lookup_list; eauto.
      edestruct get_length_eq; try eapply H; eauto.
      edestruct get_length_eq; try eapply H12; eauto.
      eapply H1; eauto.
      eapply inverse_on_update_with_list; eauto.
      * eapply injective_on_incl. eapply locally_injective.
        eapply H13; eauto.
        edestruct H23; eauto. simpl in *.
        eauto with cset.
      * eapply inverse_on_incl; try eassumption. simpl.
        edestruct H23; eauto.
    + eapply IHrenamedApart; eauto using inverse_on_incl.
Qed.

Lemma renamedApart_locally_inj_alpha' s ϱ ϱ' Lv alv ang
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (live_global ⊝ Lv) (fst (getAnn ang))
  -> LabelsDefined.noUnreachableCode s
  -> inverse_on (getAnn alv) ϱ ϱ'
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros.
  exploit live_sound_renamedApart_minus; eauto.
  eapply renamedApart_live_imperative_is_functional in H5; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in H5.
  eapply renamedApart_locally_inj_alpha in H5; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply inverse_on_incl; eauto.
  erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
  destruct (getAnn ang); simpl; cset_tac; intuition.
Qed.

Lemma funConstr_disjoint_globals F ans alvs D Dt
  : length F = length ans
    -> length F = length alvs
    -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
          get alvs n a -> get ans n b -> ann_R Subset1 a b)
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj D Dt
    -> disjoint (live_global ⊝ (pair ⊜ (getAnn ⊝ alvs) (fst ⊝ F))) Dt.
Proof.
  intros. norm_map_zip. hnf; intros.
  inv_zip H4. invc H7; simpl in *.
  edestruct get_length_eq; try eapply H; eauto.
  edestruct H2; eauto; dcr.
  exploit H1; eauto. eapply ann_R_get in H9.
  destruct (getAnn x1); simpl in *.
  rewrite H9, H8. eapply disj_1_incl; try eapply H3; eauto.
  clear_all; cset_tac; intuition.
Qed.

Lemma live_globals_bounded2 F alvs ans D Dt lv i
: length F = length alvs
  -> length F = length ans
  -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
        get alvs n a -> get ans n b -> ann_R Subset1 a b)
  -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
        get F n Zs ->
        get alvs n a ->
        of_list (fst Zs)[<=]getAnn a /\
        (if isFunctional i
         then getAnn a \ of_list (fst Zs)[<=]lv
         else True))
  -> Indexwise.indexwise_R (funConstr D Dt) F ans
   -> bounded
       (live_global ⊝ (pair ⊜ (getAnn ⊝ alvs) (fst ⊝ F))) D.
Proof.
  intros LEN1 LEN2 ANNR ZINCL FUNC. norm_map_zip.
  eapply get_bounded. intros.
  inv_zip H. invc H2.
  edestruct get_length_eq; try eapply LEN2; eauto.
  exploit ANNR; eauto; dcr. eapply ann_R_get in H3.
  edestruct ZINCL; eauto; dcr.
  edestruct FUNC; eauto; dcr.
  destruct (getAnn x); simpl in *.
  rewrite H3, H6. clear_all; cset_tac; intuition.
Qed.

(** ** Theorem 7 from the paper *)
(** the generalization is analogous to the generalization in Theorem 6 *)

Lemma renamedApart_locally_inj_alpha'' s ϱ ϱ' DL (slv:ann (set var)) ang
  : renamedApart s ang
  -> locally_inj ϱ s slv
  -> live_sound Imperative DL s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> ann_R Subset1 slv ang
  -> bounded (live_global ⊝ DL) (fst (getAnn ang))
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
    split; eauto. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H14.
    cset_tac; intuition.
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
        split; eauto. rewrite update_id. reflexivity. intuition.
      }
      eapply locally_inj_morphism; eauto.
      eapply inverse_on_update_minus; eauto using inverse_on_incl,
                                      locally_injective.
      eapply injective_on_incl. eapply locally_injective, H15.
      cset_tac; intuition.
      pe_rewrite; eauto. rewrite <- incl_add'; eauto.

  - constructor.
    + rewrite map_length; eauto.
    + intros. inv_map H14. simpl. rewrite lookup_list_length; eauto.
    + intros. inv_map H14. simpl. rewrite update_with_list_lookup_list; eauto.
      edestruct get_length_eq; try eapply H; eauto.
      edestruct get_length_eq; try eapply H24; eauto.
      eapply H1; eauto.
      * assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
        eapply inverse_on_update_with_list; try eauto.
        eapply injective_on_incl. eapply locally_injective.
        eapply H16; eauto.
        simpl. edestruct H26; eauto; simpl in *. eauto with cset.
        eapply inverse_on_incl; try eassumption. simpl.
        exploit H21; eauto using get_range.
        edestruct renamedApart_globals_live; eauto; dcr.
        {
          pe_rewrite. rewrite map_app.
          simpl in *. eapply renamedApart_disj in H4. pe_rewrite.
          rewrite disjoint_app; split; eauto using bounded_disjoint.
          eapply funConstr_disjoint_globals; eauto.
        }
        simpl in *. eapply get_app_lt_1 in H36.
        inv_get.
        rewrite H37; eauto. eauto with len.
      * {
          edestruct H2; eauto; dcr. rewrite H33.
          rewrite map_app.
          rewrite bounded_app; split; eauto using bounded_incl with cset.
          eapply live_globals_bounded; intros.
          edestruct get_length_eq; eauto.
          edestruct H2; eauto; dcr.
          exploit H30; eauto. eapply ann_R_get in H41.
          exploit H26; eauto. simpl in *; dcr.
          split; eauto.
          destruct (getAnn x1); simpl in *.
          rewrite H41, H40. clear_all; cset_tac; intuition.
        }
    + eapply IHrenamedApart; eauto using inverse_on_incl.
      pe_rewrite. rewrite map_app. rewrite bounded_app; split; eauto.
      eapply live_globals_bounded2; eauto.
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
      pe_rewrite.
      eapply agree_on_incl; eauto. rewrite H7. clear_all; cset_tac; intuition.
      pe_rewrite.
      rewrite <- incl, <- H13.
      clear_all; cset_tac; intuition.
      decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; try eapply agr.
      rewrite H7. rewrite incl. eapply incl_left.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto with cset.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    + eapply IHinj; eauto.
      pe_rewrite.
      eapply agree_on_incl; eauto. rewrite H8.
      clear_all; cset_tac; intuition.
      pe_rewrite. rewrite <- incl, <- H14.
      clear_all; cset_tac; intuition.
      decide (x === a); intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    + intros.
      edestruct get_length_eq; try eapply H5; eauto.
      eapply H1; eauto.
      eapply agree_on_incl; eauto.
      edestruct H7; eauto; dcr. rewrite H13.
      setoid_rewrite union_comm at 2. rewrite union_assoc.
      eapply incl_union_lr; eauto.
      rewrite <- H12. eapply incl_union_left.
      eapply incl_list_union. eapply zip_get; eauto.
      reflexivity.
      edestruct H7; eauto; dcr. rewrite H13.
      edestruct H19; eauto. rewrite <- incl. revert H21.
      clear_all. intros. intro.
      decide (a ∈ of_list (fst Zs)); cset_tac.
      right; eapply H21; cset_tac.
    + eapply IHinj; eauto.
      eapply agree_on_incl; eauto.
      rewrite H10. simpl. rewrite <- H12. eauto with cset.
      rewrite H10; simpl. rewrite <- incl. eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto with cset.
Qed.
