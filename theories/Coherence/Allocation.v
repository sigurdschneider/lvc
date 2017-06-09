Require Import CSet Le.

Require Import Plus Util Map DecSolve AllInRel OptionR Subset1 PairwiseDisjoint.
Require Import Env IL Annotation Liveness.Liveness Coherence Alpha Restrict RenamedApart.
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
      of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv )
  -> bounded (Some ⊝ ((getAnn ⊝ alvs) \\ (fst ⊝ F))) lv.
Proof.
  intros.
  eapply get_bounded; intros; inv_get.
  edestruct H; eauto.
Qed.

Ltac norm_map_zip :=
  repeat (progress (repeat rewrite List.map_app;
                    repeat rewrite List.map_map;
                    repeat rewrite map_zip;
                    repeat rewrite zip_map_l;
                    repeat rewrite zip_map_r)).

Lemma map_fst_zip X Y Z(f: X -> Y) (g:X->Z) L
  : fst ⊝ (fun x => (f x, g x)) ⊝ L = f ⊝ L.
Proof.
  rewrite map_map. reflexivity.
Qed.

Lemma locally_inj_fun ϱ alvs alv F Zs n lv
  : ( forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
        get F n Zs ->
        get alvs n a -> of_list (fst Zs) ⊆ getAnn a /\ getAnn a \ of_list (fst Zs) ⊆ lv)
    -> ( forall (n : nat) (Zs : params * stmt) (alv : ann ⦃var⦄),
          get F n Zs -> get alvs n alv -> locally_inj ϱ (snd Zs) alv)
    -> get F n Zs
    -> get alvs n alv
    -> injective_on (getAnn alv ∪ of_list (fst Zs)) ϱ.
Proof.
  intros. eapply injective_on_incl.
  - eapply locally_injective; eauto.
  - edestruct H; eauto. rewrite H3. eauto with cset.
Qed.

Lemma globals_disj alvs alv F Zs n m lv Zs' ans D Dt a' alv'
  : ( forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
        get F n Zs ->
        get alvs n a -> of_list (fst Zs) ⊆ getAnn a /\ getAnn a \ of_list (fst Zs) ⊆ lv)
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> get F n Zs
    -> get alvs n alv
    -> get ans m a'
    -> get F m Zs'
    -> get alvs m alv'
    -> lv ⊆ D
    -> disj (getAnn alv \ of_list (fst Zs)) (of_list (fst Zs')).
Proof.
  intros. edestruct (H n); eauto.
  edestruct (H0 m); eauto; dcr.
  symmetry. rewrite H8, H6; eauto.
Qed.

Lemma globals_disj_bounded Lv ZL Z F Zs n m lv ans D Dt a
  : bounded (Some ⊝ Lv \\ ZL) D
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> get Lv n lv
    -> get ZL n Z
    -> get F m Zs
    -> get ans m a
    -> disj (lv \ of_list Z) (of_list (fst Zs)).
Proof.
  intros. exploit (bounded_get); eauto.
  edestruct H0; eauto; dcr.
  symmetry. rewrite H5; eauto.
Qed.

Hint Resolve locally_inj_fun globals_disj globals_disj_bounded.

Lemma PIR2_rename ZL Lv ϱ alvs F ans Dt D lv alv Zs n a
      (H0 : forall (n : nat) (Zs : params * stmt) (alv : ann (set var)),
              get F n Zs -> get alvs n alv -> locally_inj ϱ (snd Zs) alv)
      (H8 : Indexwise.indexwise_R (funConstr D Dt) F ans)
      (H13 : forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
               get F n Zs ->
               get alvs n a ->
               of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
      (H19 :get alvs n alv)
      (H17 :get F n Zs)
      (H20 : get ans n a)
      (H11 : length F = length alvs)
      (BND:bounded (Some ⊝ (Lv \\ ZL)) D)
      (INCL: lv ⊆ D)
: PIR2 (fstNoneOrR Equal)
     (lookup_seto ϱ ⊝ (restr (getAnn alv) ⊝ (Some ⊝ (getAnn ⊝ alvs ++ Lv) \\ (fst ⊝ F ++ ZL))))
     (restr (getAnn (mapAnn (lookup_set ϱ) alv) \
                of_list (fst (lookup_list ϱ (fst Zs), rename ϱ (snd Zs)))) ⊝
            (Some
         ⊝ (getAnn ⊝ mapAnn (lookup_set ϱ) ⊝ alvs) \\
         (fst ⊝ (fun Zs : params * stmt => (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) ⊝ F) ++
         lookup_seto ϱ ⊝ (restr lv ⊝ (Some ⊝ Lv \\ ZL)))).
Proof.
  simpl.
  rewrite getAnn_mapAnn_map.
  rewrite getAnn_mapAnn.
  rewrite map_fst_zip. rewrite <- map_map with (f:=fst).
  rewrite of_list_lookup_list; eauto.
  rewrite zip_app; eauto with len.
  repeat rewrite List.map_app.
  eapply PIR2_app.
  - eapply PIR2_get; [ intros; inv_get | eauto 20 with len].
    repeat rewrite lookup_seto_restr.
    cases; [| econstructor].
    simpl. repeat (cases; simpl; eauto using @fstNoneOrR).
    + econstructor. rewrite of_list_lookup_list; eauto.
      eapply lookup_set_minus_eq; eauto.
    + exfalso. eapply NOTCOND.
      rewrite of_list_lookup_list; eauto.
      rewrite lookup_set_minus_incl; eauto.
      rewrite <- lookup_set_minus_eq; eauto.
      eapply lookup_set_incl; eauto.
      eapply not_incl_minus; eauto.
  - eapply PIR2_get; [ intros; inv_get | eauto with len].
    repeat rewrite lookup_seto_restr.
    cases; [| econstructor].
    repeat (cases; simpl; eauto using @fstNoneOrR).
    + exfalso. eapply NOTCOND.
      rewrite <- lookup_set_minus_eq; eauto.
      eapply lookup_set_incl; eauto.
      eapply not_incl_minus; eauto.
    + exfalso. eapply NOTCOND.
      exploit bounded_get; eauto.
      exploit H13; eauto; dcr.
      rewrite <- H5. eapply not_incl_minus; eauto.
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
    PIR2 (fstNoneOrR (flip Subset)) (lookup_seto ϱ ⊝ A) (lookup_seto ϱ ⊝ B).
Proof.
  intros. eapply PIR2_get; [intros; inv_get | eauto using PIR2_length with len].
  PIR2_inv; simpl; eauto using @fstNoneOrR.
  econstructor. unfold flip in *. rewrite H4. reflexivity.
Qed.


Lemma restrict_subset2 DL DL' G G'
: PIR2 (fstNoneOrR (flip Subset)) DL DL'
  -> G ⊆ G'
  -> PIR2 (fstNoneOrR (flip Subset)) (restr G ⊝ DL) (restr G' ⊝ DL').
Proof.
  intros. induction H; simpl; econstructor; eauto.
  - inv pf.
    + simpl. econstructor.
    + unfold restr. repeat cases; try econstructor; eauto.
      exfalso. unfold flip in H1. rewrite H0 in COND. cset_tac.
Qed.

Lemma PIR2_oglobals ϱ F alvs ZL Lv (alvb:ann(set var)) lv
      (LEN:length F = length alvs) (A:getAnn alvb ⊆ lv)
  : PIR2 (fstNoneOrR (flip Subset))
         (lookup_seto ϱ ⊝ restr (getAnn alvb) ⊝ (Some ⊝ (getAnn ⊝ alvs ++ Lv) \\ (fst ⊝ F ++ ZL)))
         (Some
            ⊝ (getAnn ⊝ mapAnn (lookup_set ϱ) ⊝ alvs) \\
            (fst ⊝ (fun Zs : params * stmt => (lookup_list ϱ (fst Zs), rename ϱ (snd Zs))) ⊝ F) ++
            lookup_seto ϱ ⊝ restr lv ⊝ (Some ⊝ Lv \\ ZL)).
Proof.
  rewrite zip_app; eauto with len.
  rewrite map_fst_zip. rewrite <- map_map with (f:=fst).
  rewrite getAnn_mapAnn_map.
  repeat rewrite List.map_app.
  eapply PIR2_app.
  - eapply PIR2_get; [ intros; inv_get | eauto 20 with len ].
    repeat rewrite lookup_seto_restr.
    cases; eauto using @fstNoneOrR.
    econstructor. unfold flip.
    rewrite of_list_lookup_list; eauto. eapply lookup_set_minus_incl; eauto.
  - eapply PIR2_map_lookup. eapply restrict_subset2; eauto.
Qed.

Lemma rename_renamedApart_srd s ang ϱ (alv:ann (set var)) ZL Lv
  : renamedApart s ang
    -> (getAnn alv) ⊆ fst (getAnn ang)
    -> live_sound FunctionalAndImperative ZL Lv s alv
    -> locally_inj ϱ s alv
    -> bounded (Some ⊝ (Lv \\ ZL)) (fst (getAnn ang))
    -> srd (lookup_seto ϱ ⊝ (restr (getAnn alv) ⊝ (Some ⊝ (Lv \\ ZL))))
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
      * erewrite (@restrict_incl_ext _ (getAnn al) (getAnn al \ singleton x));
          eauto with cset.
        -- eapply list_eq_special; [ eauto with cset | ].
           rewrite lookup_set_minus_incl_inj; eauto.
           ++ rewrite <- minus_inane_set.
             instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
             rewrite lookup_set_minus_incl; eauto with cset.
             rewrite lookup_set_singleton'; eauto.
             rewrite meet_comm. eapply meet_minus.
           ++ assert (getAnn al [=] getAnn al ∪ singleton x) by
                 (revert H11; clear_all; cset_tac).
             rewrite <- H1. eauto using locally_injective.
        -- revert H4; clear_all; cset_tac.
  - econstructor. simpl in *.
    + eapply srd_monotone.
      eapply IHRI1; eauto.
      * pe_rewrite. rewrite H12; eauto.
      * pe_rewrite. eauto using bounded_incl.
      * eapply list_eq_fstNoneOrR_incl; eauto.
    + eapply srd_monotone.
      eapply IHRI2; eauto; pe_rewrite; eauto with cset.
      eapply list_eq_fstNoneOrR_incl; eauto.
  - econstructor.
    instantiate (1:= lookup_set ϱ (blv \ of_list Z)).
    eapply map_get_eq. eauto using map_get_1. simpl.
    cases. reflexivity.
  - econstructor.
  - econstructor; eauto with len.
    + intros. inv_get.
      eapply srd_monotone.
      * edestruct H8; eauto; dcr.
        eapply H1; eauto.
        rewrite H12. exploit H14; eauto; dcr.
        rewrite <- INCL. rewrite <- H26.
        clear_all; cset_tac.
        rewrite H12. rewrite <- incl_right.
        rewrite zip_app; eauto with len; rewrite List.map_app.
        rewrite bounded_app; split; eauto.
        eapply get_bounded; intros; inv_get.
        exploit H14; eauto; dcr. eauto with cset.
      * eapply PIR2_rename; eauto.
    + eapply srd_monotone2. simpl in * |- *.
      * eapply IHRI; eauto; pe_rewrite; eauto with cset.
        rewrite zip_app; eauto with len.
        rewrite List.map_app.
        rewrite bounded_app; split; eauto.
        eapply get_bounded; intros; inv_get; simpl in *.
        exploit H14; eauto; dcr. eauto with cset.
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

Lemma bounded_disjoint ZL Lv u v
: bounded (Some ⊝ Lv \\ ZL) u
  -> disj u v
  -> disjoint (Some ⊝ Lv \\ ZL) v.
Proof.
  general induction Lv; destruct ZL; simpl in * |- *; eauto; isabsurd; dcr.
  - hnf; intros. inv H.
    + rewrite H1; eauto.
    + exploit IHLv; eauto.
Qed.

Require Import LabelsDefined.

Lemma rename_renamedApart_srd' b s ang ϱ (alv:ann (set var)) ZL Lv
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> noUnreachableCode (isCalled b) s
  -> srd (lookup_seto ϱ ⊝
                     (restr (getAnn (mapAnn2 meet1 alv ang)) ⊝ (Some ⊝ Lv \\ ZL)))
        (rename ϱ s)
        (mapAnn (lookup_set ϱ) (mapAnn2 meet1 alv ang)).
Proof.
  intros.
  exploit live_sound_renamedApart_minus; eauto.
  eapply renamedApart_live_imperative_is_functional in H4; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply rename_renamedApart_srd in H4; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  erewrite getAnn_mapAnn2; eauto using live_sound_annotation, renamedApart_annotation.
  cset_tac.
Qed.

(** ** Theorem 6 from the paper. *)
(** The generalization to the paper version is
    that we do not bound by the free variables, but by a set that that contains
    the free variables and is disjoint with any variables occuring in binding
    positions in [s]; this set is [fst (getAnn ang)] *)

Lemma rename_renamedApart_srd'' b s ang ϱ (alv:ann (set var)) ZL Lv
  : renamedApart s ang
    -> live_sound Imperative ZL Lv s alv
    -> ann_R Subset1 alv ang
    -> locally_inj ϱ s alv
    -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
    -> noUnreachableCode (isCalled b) s
    -> srd (lookup_seto ϱ ⊝ (restr (getAnn alv) ⊝ (Some ⊝ Lv \\ ZL)))
          (rename ϱ s)
          (mapAnn (lookup_set ϱ) alv).
Proof.
  intros SSA LS INCL RI BOUND UNREACH.
  general induction RI; inv LS; subst; inv SSA; inv INCL; inv UNREACH; simpl; set_simpl.
  - econstructor.
    + eapply srd_monotone.
      * eapply IHRI; eauto. pe_rewrite.
        rewrite <- incl_add'; eauto.
      * erewrite (@restrict_incl_ext _ (getAnn al)); eauto.
        instantiate (1:=getAnn al \ singleton x).
        eapply list_eq_special. eauto.
        rewrite lookup_set_minus_incl_inj; eauto. rewrite <- minus_inane_set.
        instantiate (1:={ϱ x}). eapply incl_minus_lr; eauto.
        rewrite lookup_set_minus_incl; eauto with cset.
        rewrite lookup_set_singleton'; eauto.
        rewrite meet_comm. eapply meet_minus.
        assert (getAnn al [=] getAnn al ∪ singleton x). cset_tac; intuition.
        rewrite <- H0. eauto using locally_injective.
        simpl; cset_tac; intuition.
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
    eapply map_get_eq. eauto using map_get_1. simpl.
    cases. reflexivity.
  - econstructor.
  - econstructor; eauto.
    + repeat rewrite map_length; eauto.
    + intros. inv_get.
      eapply srd_monotone.
      * eapply H1; eauto. simpl in *. edestruct H7; eauto; dcr. rewrite H11.
        rewrite zip_app; eauto with len. rewrite List.map_app.
        rewrite bounded_app; split; eauto using bounded_incl with cset.
        eapply live_globals_bounded.
        intros. split. eapply H13; eauto. inv_get.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H32.
        rewrite H32.
        rewrite H30. simpl. clear_all; cset_tac; intuition.
      * eapply PIR2_rename; eauto.
        simpl in *.
        split.
        -- eapply H13; eauto.
        -- inv_get.
           exploit H19; eauto using get_range.
           edestruct renamedApart_globals_live_From; try eapply H26; eauto.
           ++ pe_rewrite. eauto with cset.
           ++ eauto with cset.
           ++ eapply bounded_disjoint. eauto.
             eauto with cset.
           ++ dcr; simpl in *. inv_get. eauto with cset.
    + eapply srd_monotone2. simpl in * |- *.
      eapply IHRI; eauto.
      rewrite H15; simpl in * |- *; eauto.
      rewrite zip_app; eauto with len.
      rewrite List.map_app. rewrite bounded_app. split; eauto.
      eapply live_globals_bounded; intros; split.
      * eapply H13; eauto.
      * inv_get.
        edestruct H7; eauto.
        exploit H23; eauto. eapply ann_R_get in H25.
        rewrite H25. simpl.
        rewrite H11. clear_all; cset_tac; intuition.
      * eapply PIR2_oglobals; eauto.
Qed.


(** ** Renaming with a locally injective renaming yields an α-equivalent program *)

Lemma renamedApart_locally_inj_alpha s ϱ ϱ' ZL Lv (slv:ann (set var)) ang
  : renamedApart s ang
  -> locally_inj ϱ s slv
  -> live_sound Functional ZL Lv s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros. general induction H; simpl; invt locally_inj; invt live_sound;
            set_simpl.
  - econstructor. simpl in *. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    assert (REQ:rename ϱ s = rename (update ϱ x (ϱ x)) s). {
      rewrite update_id; eauto.
    }
    rewrite REQ. eapply IHrenamedApart; eauto.
    assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
    split; eauto. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H11.
    cset_tac; intuition.
  - econstructor; eauto. eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.
    now eapply IHrenamedApart1; eauto using inverse_on_incl.
    now eapply IHrenamedApart2; eauto using inverse_on_incl.

  - econstructor; eauto. eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.

  - econstructor; eauto. rewrite map_length. eauto.
    intros. edestruct map_get_4; eauto; dcr; subst.
    get_functional; eauto; subst.
    eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.

  - constructor.
    + rewrite map_length; eauto.
    + intros. inv_get; simpl. rewrite lookup_list_length; eauto.
    + intros. inv_get. simpl.
      rewrite update_with_list_lookup_list; eauto.
      eapply H1; eauto.
      eapply inverse_on_update_with_list; eauto.
      * eapply injective_on_incl. eapply locally_injective.
        eapply H13; eauto.
        edestruct H24; eauto. simpl in *.
        eauto with cset.
      * eapply inverse_on_incl; try eassumption. simpl.
        edestruct H24; eauto.
    + eapply IHrenamedApart; eauto using inverse_on_incl.
Qed.

Lemma renamedApart_locally_inj_alpha' b s ϱ ϱ' ZL Lv alv ang
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> locally_inj ϱ s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> LabelsDefined.noUnreachableCode (isCalled b) s
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
  cset_tac; intuition.
Qed.

Lemma funConstr_disjoint_globals F ans alvs D Dt
  : length F = length ans
    -> length F = length alvs
    -> (forall (n : nat) (a : ann (set var)) (b : ann (set var * set var)),
          get alvs n a -> get ans n b -> ann_R Subset1 a b)
    -> Indexwise.indexwise_R (funConstr D Dt) F ans
    -> disj D Dt
    -> disjoint (Some ⊝ (getAnn ⊝ alvs) \\ (fst ⊝ F)) Dt.
Proof.
  intros. norm_map_zip. hnf; intros.
  inv_zip H4. invc H7; simpl in *.
  edestruct get_length_eq; try eapply H; eauto.
  edestruct H2; eauto; dcr.
  exploit H1; eauto. eapply ann_R_get in H9.
  rewrite H9, H8. simpl. eapply disj_1_incl; try eapply H3; eauto.
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
   -> bounded (Some ⊝ (getAnn ⊝ alvs) \\ (fst ⊝ F)) D.
Proof.
  intros LEN1 LEN2 ANNR ZINCL FUNC. norm_map_zip.
  eapply get_bounded. intros.
  inv_zip H. invc H2.
  edestruct get_length_eq; try eapply LEN2; eauto.
  exploit ANNR; eauto; dcr. eapply ann_R_get in H3.
  edestruct ZINCL; eauto; dcr.
  edestruct FUNC; eauto; dcr.
  rewrite H3, H6.
  clear_all; cset_tac; intuition.
Qed.

(** ** Theorem 7 from the paper *)
(** the generalization is analogous to the generalization in Theorem 6 *)

Lemma renamedApart_locally_inj_alpha'' b s ϱ ϱ' ZL Lv (slv:ann (set var)) ang
  : renamedApart s ang
  -> locally_inj ϱ s slv
  -> live_sound Imperative ZL Lv s slv
  -> inverse_on (getAnn slv) ϱ ϱ'
  -> ann_R Subset1 slv ang
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> noUnreachableCode (isCalled b) s
  -> alpha ϱ ϱ' s (rename ϱ s).
Proof.
  intros RA INJ LS IOn AnnR BND NUC.
  general induction LS; simpl; invt locally_inj; invt renamedApart;
          invt @ann_R; invt noUnreachableCode; set_simpl.
  - econstructor. simpl in *. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl. eapply Exp.freeVars_live; eauto. eauto.
    assert (rename ϱ s = rename (update ϱ x (ϱ x)) s). {
      rewrite update_id; eauto.
    }
    rewrite H2. eapply IHLS; eauto.
    assert (fpeq _eq ϱ (update ϱ x (ϱ x))). {
    split; eauto. rewrite update_id. reflexivity. intuition.
    }
    eapply locally_inj_morphism; eauto.
    eapply inverse_on_update_minus; eauto using inverse_on_incl, locally_injective.
    eapply injective_on_incl. eapply locally_injective, H4.
    revert H1; clear_all; cset_tac.
    pe_rewrite; simpl in *. rewrite <- incl_add'; eauto.
  - econstructor; eauto. eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.
    eapply IHLS1; eauto using inverse_on_incl.
    pe_rewrite; eauto.
    eapply IHLS2; eauto using inverse_on_incl.
    pe_rewrite; eauto.

  - econstructor; eauto with len.
    intros. inv_get.
    eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.

  - econstructor; eauto. eapply alpha_op_rename_injective.
    eapply inverse_on_incl. eapply Op.freeVars_live; eauto. eauto.

  - constructor.
    + eauto with len.
    + intros. inv_get. simpl. eauto with len.
    + intros. inv_get. simpl. rewrite update_with_list_lookup_list; eauto.
      eapply H1; eauto.
      * assert (fpeq _eq ϱ ϱ). split. reflexivity. split; intuition.
        eapply inverse_on_update_with_list; try eauto.
        eapply injective_on_incl. eapply locally_injective.
        eapply H10; eauto.
        simpl. edestruct H2; eauto; simpl in *. eauto with cset.
        eapply inverse_on_incl; try eassumption. simpl.
        exploit H19; eauto using get_range.
        edestruct renamedApart_globals_live_From; try eassumption; dcr.
        -- pe_rewrite. eauto with cset.
        -- eapply renamedApart_disj in RA. eauto.
        -- eapply bounded_disjoint; try eassumption. simpl.
           eapply renamedApart_disj in RA. eauto.
        -- simpl in *. inv_get. rewrite H29; eauto.
      * edestruct H8; try eassumption; dcr. rewrite H5.
        rewrite zip_app; [| eauto with len].
        rewrite List.map_app.
        rewrite bounded_app; split; [| eauto using bounded_incl with cset].
        eapply live_globals_bounded; intros. inv_get.
        edestruct H8; try eassumption; dcr.
        exploit H23 as AnnR'; try eassumption.
        eapply ann_R_get in AnnR'.
        exploit H2; try eassumption. simpl in *; dcr.
        split; eauto.
        rewrite AnnR', H30.
        clear_all; cset_tac; intuition.

    + eapply IHLS; eauto using inverse_on_incl.
      pe_rewrite.
      rewrite zip_app; eauto with len.
      rewrite List.map_app. rewrite bounded_app; split; eauto.
      eapply live_globals_bounded2; eauto.
      intros; edestruct H2; dcr; repeat split; eauto.
Qed.


(** ** local injectivity only looks at variables occuring in the program *)

Lemma locally_inj_live_agree s ϱ ϱ' ara alv ZL Lv
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (sd: renamedApart s ara)
      (inj: locally_inj ϱ s alv)
      (agr: agree_on eq (fst (getAnn ara) ∪ snd (getAnn ara)) ϱ ϱ')
      (incl:getAnn alv ⊆ fst (getAnn ara))
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction inj; invt renamedApart; invt live_sound; simpl in *;
    set_simpl.
  - econstructor; eauto.
    + eapply IHinj; eauto; pe_rewrite.
      eapply agree_on_incl; eauto.
      clear; cset_tac. eauto with cset.
    + eapply injective_on_agree; eauto with cset.
  - econstructor; eauto.
    eapply injective_on_agree; eauto with cset.
    + eapply IHinj1; eauto; pe_rewrite; eauto with cset.
    + eapply IHinj2; eauto; pe_rewrite; eauto with cset.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
    + intros. inv_get.
      eapply H1; eauto; pe_rewrite.
      * eapply agree_on_incl; eauto.
        edestruct H7; eauto; dcr.
        rewrite H12.
        setoid_rewrite union_comm at 2. rewrite union_assoc.
        eapply incl_union_lr; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply zip_get; eauto.
        reflexivity.
      * edestruct H7; eauto; dcr. rewrite H12.
        edestruct H20; dcr; eauto. rewrite <- incl.
        eauto with cset.
    + eapply IHinj; eauto; pe_rewrite.
      eapply agree_on_incl; eauto with cset.
      eauto with cset.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto with cset.
Qed.

(** ** Liveness is stable under renaming with locally injective renaming *)

Lemma live_inj_rename_sound i ZL Lv s an (ϱ:env var)
  (LS:live_sound i ZL Lv s an)
  (LI:locally_inj ϱ s an)
  : live_sound i (lookup_list ϱ ⊝ ZL) (lookup_set ϱ ⊝ Lv) (rename ϱ s) (mapAnn (lookup_set ϱ) an).
Proof.
  general induction LS; invt locally_inj; simpl.
  - econstructor; eauto using live_exp_rename_sound.
    + rewrite getAnn_mapAnn.
      rewrite <- lookup_set_singleton'; eauto.
      rewrite lookup_set_minus_incl; eauto with cset.
    + rewrite getAnn_mapAnn.
      eapply lookup_set_spec; eauto.
  - econstructor; eauto using live_op_rename_sound.
    + rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
    + rewrite getAnn_mapAnn. eapply lookup_set_incl; eauto.
  - econstructor; eauto with len.
    + cases; eauto.
      rewrite of_list_lookup_list; eauto.
      etransitivity. eapply lookup_set_minus_incl; eauto.
      eapply lookup_set_incl; eauto.
    + intros; inv_get; eauto using live_op_rename_sound.
  - econstructor; eauto using live_op_rename_sound.
  - econstructor; eauto; try rewrite getAnn_mapAnn; eauto with cset len.
    + repeat rewrite map_map; simpl. rewrite <- map_map. rewrite <- List.map_app.
      setoid_rewrite getAnn_mapAnn.
      setoid_rewrite <- map_map at 3. rewrite <- List.map_app.
      eapply IHLS; eauto.
    + intros; inv_get. simpl.
      repeat rewrite map_map; simpl. rewrite <- map_map.
      rewrite <- List.map_app.
      setoid_rewrite getAnn_mapAnn.
      setoid_rewrite <- map_map at 3. rewrite <- List.map_app. eauto.
    + intros; inv_get; simpl.
      exploit H2; eauto with cset; dcr.
      split.
      * rewrite of_list_lookup_list; eauto.
        rewrite getAnn_mapAnn.
        eapply lookup_set_incl; eauto.
      * split.
        -- exploit H10 as INJ; eauto. eapply locally_injective in INJ.
           eapply injective_on_incl in INJ; eauto.
           eapply (injective_nodup INJ); eauto.
        -- cases; eauto.
           rewrite getAnn_mapAnn.
           rewrite of_list_lookup_list; eauto.
           rewrite lookup_set_minus_incl; eauto with cset.
Qed.
