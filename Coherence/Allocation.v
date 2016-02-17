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

(** ** local injectivity is decidable *)

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  revert ϱ lv an.
  sind s; intros; destruct s; destruct lv; try (now exfalso; inv an).
  + decide(injective_on a ϱ); try dec_solve.
    edestruct (IH s); eauto; try dec_solve. inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct (IH s1); eauto; try inv an; eauto; try dec_solve;
    edestruct (IH s2); eauto; try inv an; eauto; try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct (IH s); eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve.
    decide(length s = length sa); try dec_solve.
    edestruct (IH s0); eauto; try inv an; eauto; try dec_solve.
    edestruct (indexwise_R_dec' (R:=fun x y => locally_inj ϱ (snd x) y) (LA:=s) (LB:=sa));
      try dec_solve.
    intros. eapply IH; eauto. inv an; eauto.
Defined.

Instance locally_inj_dec_inst (ϱ:env var) (s:stmt) (lv:ann (set var))
         `{Computable (annotation s lv)}
  : Computable (locally_inj ϱ s lv).
Proof.
  destruct H as [].
  hnf; eauto using locally_inj_dec.
  right; intro; eauto using locally_inj_annotation.
Defined.

Lemma minus_incl_add X `{OrderedType X} x (s t:set X)
:  s \ singleton x ⊆ t
   -> s [<=]{x; t}.
Proof.
  cset_tac; intuition. decide (x === a); eauto. right. eapply H0.
  cset_tac; intuition.
Qed.

Hint Resolve minus_incl_add : cset.
(** ** Renaming with a locally injective renaming yields a coherent program *)

Lemma live_globals_bounded F alvs lv
: ( forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
      get F n Zs ->
      get alvs n a ->
      of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
  -> bounded
      (live_globals (Liveness.live_globals F alvs)) lv.
Proof.
  intros. unfold live_globals, Liveness.live_globals.
  rewrite map_zip.
  eapply get_bounded. intros.
  inv_zip H0. inv H3.
  edestruct H; eauto.
Qed.

Lemma live_globals_app L L'
: live_globals (L ++ L') = live_globals L ++ live_globals L'.
Proof.
  unfold live_globals. rewrite List.map_app. reflexivity.
Qed.

Lemma map_lookup_app L L' ϱ
: map_lookup ϱ (L ++ L') = map_lookup ϱ L ++ map_lookup ϱ L'.
Proof.
  unfold map_lookup. rewrite List.map_app. reflexivity.
Qed.

Ltac norm_map_zip :=
  unfold map_lookup, live_globals, restrict, oglobals, globals, Liveness.live_globals;
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
      (BND:bounded (live_globals Lv) D)
      (INCL: lv ⊆ D)
: AllInRel.PIR2 (fstNoneOrR Equal)
                (map_lookup ϱ
                            (restrict (live_globals (Liveness.live_globals F alvs ++ Lv))
                                      (getAnn x0)))
                (restrict
                   (oglobals
                      (List.map
                         (fun Zs : params * stmt =>
                            (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) F)
                      (List.map (mapAnn (lookup_set ϱ)) alvs) ++
                      map_lookup ϱ (restrict (live_globals Lv) lv))
                   (getAnn (mapAnn (lookup_set ϱ) x0) \
                           of_list (fst (lookup_list ϱ (fst x), rename ϱ (snd x))))).
Proof.
  simpl.
  rewrite live_globals_app.
  repeat rewrite restrict_app.
  rewrite map_lookup_app.
  eapply AllInRel.PIR2_app.
  rewrite getAnn_mapAnn.
  rewrite of_list_lookup_list; eauto.
  erewrite (@restrict_incl_ext _ (getAnn x0)); eauto.
  instantiate (1:=getAnn x0 \ of_list (fst x)).
  - norm_map_zip.
    eapply AllInRel.PIR2_get; intros.
    inv_zip H.
    inv_zip H1. repeat get_functional; subst.
    unfold global. rewrite getAnn_mapAnn. simpl.
    repeat destruct if; simpl; try now econstructor.
    econstructor.
    rewrite of_list_lookup_list; intuition.
    eapply lookup_set_minus_eq; intuition.
    exploit H13; eauto. simpl in *; dcr.
    exploit H0; eauto. eapply locally_injective in H2.
    eapply injective_on_incl. eapply H2. rewrite H3.
    clear_all; cset_tac; intuition.
    exfalso. eapply n1.
    rewrite of_list_lookup_list; intuition.
    repeat rewrite <- lookup_set_minus_eq; eauto.
    eapply lookup_set_incl; eauto. intuition.
    exploit H13; try eapply H19; eauto. simpl in *; dcr.
    exploit H0; try eapply H19; eauto. eapply locally_injective in H2.
    eapply injective_on_incl. eapply H2. rewrite H3.
    clear_all; cset_tac; intuition.
    intuition.
    exploit H13; eauto. simpl in *; dcr.
    exploit H0; eauto. eapply locally_injective in H2.
    eapply injective_on_incl. eapply H2. rewrite H3.
    clear_all; cset_tac; intuition.
    repeat rewrite zip_length2; eauto.
  - instantiate (1:=D).
    simpl in H13. simpl in *. rewrite <- INCL.
    eapply live_globals_bounded; eauto.
  - edestruct H8; eauto; dcr.
    revert H4; clear_all; cset_tac; intuition; eauto.
  - simpl.
    erewrite (@restrict_incl_ext _ (getAnn x0)); eauto.
    instantiate (1:=getAnn x0 \ of_list (fst x)).
    eapply list_eq_special; eauto.
    edestruct H13; eauto.
    rewrite getAnn_mapAnn. rewrite of_list_lookup_list; eauto.
    eapply lookup_set_minus_incl_inj; eauto; intuition.
    exploit H0; try eapply H19; eauto.
    eapply locally_injective in H.
    eapply injective_on_incl; eauto.
    exploit H13; eauto; dcr.
    edestruct H8; eauto; dcr.
    revert H4; clear_all; cset_tac; intuition; eauto.
Qed.



Instance fstNoneOrR_flip_Subset_trans2 {X} `{OrderedType X} : Transitive (fstNoneOrR Equal).
hnf; intros. inv H; inv H0.
- econstructor.
- inv H1. econstructor. transitivity y0; eauto.
Qed.

Lemma PIR2_map_lookup ϱ A B
  : AllInRel.PIR2 (fstNoneOrR (flip Subset)) A B ->
    AllInRel.PIR2 (fstNoneOrR (flip Subset))
                  (map_lookup ϱ A)
                  (map_lookup ϱ B).
Proof.
  intros. general induction H; simpl; eauto using AllInRel.PIR2.
  econstructor; eauto.
  inv pf; simpl; econstructor. unfold flip in *. rewrite H0; eauto.
Qed.

Lemma PIR2_oglobals ϱ F alvs Lv (alvb:ann(set var)) lv
      (LEN:length F = length alvs) (A:getAnn alvb ⊆ lv)
  : AllInRel.PIR2 (fstNoneOrR (flip Subset))
                  (map_lookup ϱ
                              (restrict (live_globals (Liveness.live_globals F alvs ++ Lv))
                                        (getAnn alvb)))
                  (oglobals
                     (List.map
                        (fun Zs : params * stmt =>
                           (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) F)
                     (List.map (mapAnn (lookup_set ϱ)) alvs) ++
                     map_lookup ϱ (restrict (live_globals Lv) lv)).
Proof.
  rewrite live_globals_app. rewrite restrict_app.
  rewrite map_lookup_app. eapply AllInRel.PIR2_app; eauto using list_eq_fstNoneOrR_incl.
  unfold oglobals. unfold globals. rewrite map_zip.
  unfold live_globals, Liveness.live_globals.
  rewrite map_zip. rewrite zip_map_l. rewrite zip_map_r.
  unfold global. unfold map_lookup. unfold restrict.
  repeat rewrite map_zip.
  eapply AllInRel.PIR2_get; intros.
  inv_zip H. inv_zip H0. repeat get_functional; subst.
  unfold lookup_set_option, restr, live_global, Liveness.live_global; simpl.
  destruct if. rewrite getAnn_mapAnn. econstructor. unfold flip.
             rewrite of_list_lookup_list; eauto. eapply lookup_set_minus_incl; eauto.
             econstructor. repeat rewrite zip_length2; eauto.
             eapply PIR2_map_lookup. eapply restrict_subset2; eauto.
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
  general induction RI; inv LS; subst; inv SSA; simpl in * |- *; pe_rewrite.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto; pe_rewrite.
        rewrite <- INCL; eauto with cset.
        eauto using bounded_incl with cset.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ {{x}}).
        eapply list_eq_special; eauto with cset.
        rewrite lookup_set_minus_incl_inj; eauto. rewrite <- minus_inane_set.
        instantiate (1:={{ϱ x}}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; intuition. eapply lookup_set_incl; intuition.
        rewrite lookup_set_singleton; intuition.
        rewrite meet_comm. eapply meet_minus.
        assert (getAnn al [=] getAnn al ++ {x; {}}). cset_tac; intuition.
        invc H2; eauto. rewrite <- H1. eauto using locally_injective.
        cset_tac; intuition.
  - econstructor. simpl in *.
    + eapply srd_monotone.
      eapply IHRI1; eauto using Subset_trans, lookup_set_incl; eauto;
      try (now eapply Subset_trans; eauto); pe_rewrite.
      etransitivity; eauto.
      eauto using bounded_incl.
      eapply list_eq_fstNoneOrR_incl; eauto.
    + eapply srd_monotone.
      eapply IHRI2; eauto; try (now eapply Subset_trans; eauto); pe_rewrite.
      etransitivity; eauto.
      eauto.
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
  - econstructor; eauto with len.
    + intros.
      inv_map H4. clear H19. inv_map H5. clear H20.
      edestruct (get_length_eq _ H17 H6).
      eapply srd_monotone.
      * edestruct H8; eauto; dcr.
        eapply (H1 _ _ _ H17 H19); eauto. simpl in *.
        rewrite H21. exploit H13; eauto; dcr. rewrite <- INCL, <- H27.
        clear_all; cset_tac; intuition.
        rewrite H21. unfold live_globals. rewrite List.map_app.
        rewrite <- incl_right.
        rewrite bounded_app. simpl in *. split; eauto.
        eapply get_bounded; intros.
        unfold live_global, Liveness.live_globals in H22. inv_map H22.
        inv_zip H24. simpl. exploit H13; eauto; dcr.
        rewrite H31; eauto.
      * eapply PIR2_rename; eauto.
    + eapply srd_monotone2. simpl in * |- *.
      * eapply IHRI; eauto.
        rewrite H16; simpl in * |- *; eauto. transitivity lv; eauto.
        rewrite H16; simpl.
        unfold live_globals. rewrite List.map_app.
        rewrite bounded_app; split; eauto.
        eapply get_bounded; intros.
        unfold live_global, Liveness.live_globals in H4. inv_map H4.
        inv_zip H5. simpl. exploit H13; eauto; dcr.
        rewrite H22; eauto.
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
  - econstructor; eauto using meet1_incl2.
    + rewrite zip_length2; eauto; congruence.
    + intros. inv_zip H2. get_functional; subst.
      symmetry in H. edestruct get_length_eq; try eapply H; eauto.
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
  - econstructor; eauto.
    + repeat rewrite map_length; eauto.
(*    exploit renamedApart_globals_live; eauto.
    hnf; intros. inv H1. pe_rewrite.
    eapply renamedApart_disj in H13. pe_rewrite; eauto.
    eapply ann_R_get in H20. pe_rewrite. rewrite H20.
    revert H13; unfold disj; clear_all; cset_tac; intuition; eauto.
    eapply bounded_disjoint; eauto.
    eapply renamedApart_disj in H13. pe_rewrite; eauto.
    destruct X; dcr. invc H2; simpl in *.
    econstructor; eauto. *)
    + intros. inv_map H3. inv_map H4. clear H25.
      edestruct get_length_eq; try eapply H5; eauto.
      eapply srd_monotone.
      * eapply H1; eauto.  simpl in *. edestruct H7; eauto; dcr. rewrite H28.
        rewrite live_globals_app.
        rewrite bounded_app; split; eauto using bounded_incl with cset.
        eapply live_globals_bounded.
        intros. split. eapply H12; eauto.
        edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H37.
        destruct (getAnn x2); simpl in *. rewrite H37.
        rewrite H35. clear_all; cset_tac; intuition.
      * eapply PIR2_rename; eauto.
        simpl in *.
        split. eapply H12; eauto.
        edestruct get_length_eq; eauto.
        edestruct H7; eauto; dcr.
        exploit H19; eauto using get_range.
        edestruct renamedApart_globals_live; eauto.
        hnf; intros. pe_rewrite.
        eapply renamedApart_disj in H14. pe_rewrite; eauto.
        exploit H23; eauto. eapply ann_R_get in H37.
        rewrite live_globals_app in H34.
        eapply get_app_cases in H34. destruct H34; dcr.
        unfold live_globals, Liveness.live_globals in H34.
        rewrite map_zip in H34. inv_zip H34.
        unfold live_global, Liveness.live_global in H40.
        inv H40.
        simpl in *. clear H40.
        edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto; dcr.
        exploit H23; eauto. eapply ann_R_get in H42.
        destruct (getAnn x5); simpl in *.
        rewrite H42. rewrite H41. eapply disj_1_incl; try eapply H14.
        clear_all; cset_tac; intuition.
        eapply disj_1_incl. eapply H14.
        eapply bounded_get in H38. eapply H38. eauto.
        dcr; simpl in *.
        eapply get_app_le in H37; eauto.
        unfold Liveness.live_globals in H37. inv_zip H37.
        repeat get_functional; subst.
        simpl in H38. rewrite H38. eauto.
        unfold live_globals, Liveness.live_globals.
        rewrite zip_length2; eauto. eapply get_range; eauto.
    + eapply srd_monotone2. simpl in * |- *.
      eapply IHRI; eauto.
      rewrite H15; simpl in * |- *; eauto.
      rewrite live_globals_app. rewrite bounded_app. split; eauto.
      eapply live_globals_bounded; intros; split.
      * eapply H12; eauto.
      * edestruct get_length_eq; try eapply H5; eauto.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H27.
        destruct (getAnn x); simpl in *. rewrite H27.
        rewrite H25. clear_all; cset_tac; intuition.
      * eapply PIR2_oglobals; eauto.
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
    + rewrite map_length; eauto.
    + intros. inv_map H11; simpl. rewrite lookup_list_length; eauto.
    + intros. inv_map H11. simpl.
      rewrite update_with_list_lookup_list; eauto.
      edestruct get_length_eq; try eapply H; eauto.
      edestruct get_length_eq; try eapply H12; eauto.
      eapply H1; eauto.
      eapply inverse_on_update_with_list; try intuition.
      eapply injective_on_incl. eapply locally_injective.
      eapply H13; eauto.
      edestruct H23; eauto.
      eapply inverse_on_incl; try eassumption. simpl.
      edestruct H23; eauto.
    + eapply IHrenamedApart; eauto using inverse_on_incl.
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
  eapply renamedApart_live_imperative_is_functional in H5; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in H5.
  eapply renamedApart_locally_inj_alpha in H5; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
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
  -(* exploit renamedApart_globals_live; eauto.
    hnf; intros. inv H13. pe_rewrite.
    eapply renamedApart_disj in H4. pe_rewrite; eauto.
    eapply ann_R_get in H28. pe_rewrite. rewrite H28.
    revert H4; unfold disj; clear_all; cset_tac; intuition; eauto.
    eapply bounded_disjoint; eauto. simpl.
    eapply renamedApart_disj in H4. pe_rewrite; eauto.
    destruct X; dcr. invc H14; simpl in *.*)
    constructor.
    + rewrite map_length; eauto.
    + intros. inv_map H14. simpl. rewrite lookup_list_length; eauto.
    + intros. inv_map H14. simpl. rewrite update_with_list_lookup_list; eauto.
      edestruct get_length_eq; try eapply H; eauto.
      edestruct get_length_eq; try eapply H24; eauto.
      eapply H1; eauto.
      * assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
        eapply inverse_on_update_with_list; try intuition.
        eapply injective_on_incl. eapply locally_injective.
        eapply H16; eauto.
        simpl. edestruct H26; eauto; simpl in *.
        eapply inverse_on_incl; try eassumption. simpl.
        exploit H21; eauto using get_range.
        edestruct renamedApart_globals_live; eauto; dcr.
        {
          pe_rewrite. rewrite live_globals_app.
          simpl in *. eapply renamedApart_disj in H4. pe_rewrite.
          rewrite disjoint_app; split; eauto using bounded_disjoint.
          Lemma funConstr_disjoint_globals F ans alvs D Dt
          : length F = length ans
            -> length F = length alvs
            -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
        get alvs n a -> get ans n b -> ann_R Subset1 a b)
            -> Indexwise.indexwise_R (funConstr D Dt) F ans
            -> disj D Dt
            -> disjoint (live_globals (Liveness.live_globals F alvs)) Dt.
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
          eapply funConstr_disjoint_globals; eauto.
        }
        simpl in *. eapply get_app_le in H37.
        unfold Liveness.live_globals in H37.
        inv_zip H37. simpl in *. repeat get_functional; subst.
        rewrite H38; eauto. unfold Liveness.live_globals.
        rewrite zip_length2; eauto using get_range.
      * {
          edestruct H2; eauto; dcr. rewrite H34.
          rewrite live_globals_app.
          rewrite bounded_app; split; eauto using bounded_incl with cset.
          eapply live_globals_bounded; intros.
          edestruct get_length_eq; eauto.
          edestruct H2; eauto; dcr.
          exploit H30; eauto. eapply ann_R_get in H42.
          exploit H26; eauto. simpl in *; dcr.
          split; eauto.
          destruct (getAnn x1); simpl in *.
          rewrite H42, H41. clear_all; cset_tac; intuition.
        }
    + eapply IHrenamedApart; eauto using inverse_on_incl.
      pe_rewrite. rewrite live_globals_app. rewrite bounded_app; split; eauto.
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
       (live_globals (Liveness.live_globals F alvs)) D.
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
    eapply agree_on_incl; eauto.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H8; simpl; eauto.
      eapply agree_on_incl; eauto. rewrite H9.
      clear_all; cset_tac; intuition.
      rewrite H8. simpl. rewrite <- incl, <- H14.
      clear_all; cset_tac; intuition.
      decide (x === a); intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
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
      clear_all; cset_tac; intuition.
      decide (a ∈ of_list (fst Zs)); intuition.
    + eapply IHinj; eauto.
      eapply agree_on_incl; eauto.
      rewrite H10. simpl. rewrite <- H12. eauto with cset.
      rewrite H10; simpl. rewrite <- incl. eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
