Require Import List Map Envs AllInRel Exp AppExpFree.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import Infra.PartialOrder AnnotationLattice CSetPartialOrder.

Set Implicit Arguments.

(** * ReconstrLive *)

Fixpoint reconstr_live
         (Lv : list (set var))
         (ZL : list (params))
         (G : set var)
         (s : stmt)
         (rm : ann (set var))
         {struct s}
  : ann (set var)
  :=
    match s, rm with
    | stmtLet x e t, ann1 _ rm
      => let lv_t := reconstr_live Lv ZL (singleton x) t rm in
        ann1 ((getAnn lv_t) \ singleton x ∪ Exp.freeVars e ∪ G) lv_t

    | stmtReturn e, ann0 _
      => ann0 (Op.freeVars e ∪ G)

    | stmtIf e t v, ann2 _ rm_t rm_v
      => let lv_t := reconstr_live Lv ZL ∅ t rm_t in
        let lv_v := reconstr_live Lv ZL ∅ v rm_v in
        ann2 (getAnn lv_t ∪ getAnn lv_v ∪ Op.freeVars e ∪ G) lv_t lv_v

    | stmtApp f Y, ann0 _
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (list_union (Op.freeVars ⊝ Y) ∪ blv \ of_list Z ∪ G)

    | stmtFun F t, annF _ rm_F rm_t
      => let rms := getAnn ⊝ rm_F in
        let lv_t := reconstr_live (rms ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s =>
                      reconstr_live (rms ++ Lv)
                                    (fst ⊝ F ++ ZL)
                                    (of_list (fst ps))
                                    (snd ps)
                                    rm_s
                    ) ⊜ F rm_F in
        annF (getAnn lv_t ∪ G) lv_F lv_t

    | _,_ => ann0 G

    end.


Lemma reconstr_live_G_eq (G : ⦃var⦄) (Lv : list ⦃var⦄)
      (ZL : list params) (s : stmt) a
  : getAnn (reconstr_live Lv ZL G s a) [=] getAnn (reconstr_live Lv ZL ∅ s a) ∪ G .
Proof.
  general induction s;
    destruct a;
    try destruct a;
    simpl; eauto; cset_tac.
Qed.

Lemma reconstr_live_remove_G Lv ZL G s sl G'
  : getAnn (reconstr_live Lv ZL G s sl) \ G ⊆ getAnn (reconstr_live Lv ZL G' s sl) .
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.

Lemma reconstr_live_G Lv ZL G s a
  : G ⊆ getAnn (reconstr_live Lv ZL G s a).
Proof.
  induction s,a; simpl; eauto with cset.
Qed.

Lemma reconstr_live_subset Lv Lv' ZL G s sl
  : Lv ⊑ Lv'
    -> reconstr_live Lv  ZL G s sl ⊑ reconstr_live Lv' ZL G s sl.
Proof.
  intros H.
  revert Lv Lv' H ZL G sl.
  sind s; intros; destruct s, sl; simpl; try econstructor; eauto;
    try eapply IH; eauto.
  - exploit (IH s); eauto.
    rewrite (ann_R_get H0); eauto.
  - exploit (IH s1); eauto.
    exploit (IH s2); eauto.
    rewrite (ann_R_get H0); eauto.
    rewrite (ann_R_get H1); eauto.
  - enough (nth (labN l) Lv ∅ ⊆ nth (labN l) Lv' ∅)
      as HH by (rewrite HH; clear; cset_tac).
    apply PIR2_length in H as Lv_len.
    decide (labN l < length Lv).
    + assert ({x : ⦃var⦄ & get Lv (labN l) x}) as [x get_x]
          by (apply get_in_range; eauto).
      rewrite Lv_len in l0.
      assert ({y : ⦃var⦄ & get Lv' (labN l) y}) as [y get_y]
          by (apply get_in_range; eauto).
      erewrite get_nth; eauto.
      erewrite get_nth; eauto.
      eapply get_PIR2; eauto.
    + apply not_le in n.
      rewrite nth_overflow; eauto with cset.
      omega.
  - eapply incl_union_lr; eauto.
    eapply ann_R_get.
    eapply (IH s); eauto.
  - eauto with len.
  - intros; inv_get; eauto with len.
    eapply IH; eauto.
Qed.

Lemma reconstr_live_equal Lv Lv' ZL G s sl
  : Lv ≣ Lv'
    -> reconstr_live Lv  ZL G s sl ≣ reconstr_live Lv' ZL G s sl.
Proof.
  intros H.
  revert Lv Lv' H ZL G sl.
  sind s; intros; destruct s, sl; simpl; try econstructor; eauto;
    try eapply IH; eauto.
  - exploit (IH s); eauto.
    rewrite (ann_R_get H0); eauto.
  - exploit (IH s1); eauto.
    exploit (IH s2); eauto.
    rewrite (ann_R_get H0); eauto.
    rewrite (ann_R_get H1); eauto.
  - enough (nth (labN l) Lv ∅ [=] nth (labN l) Lv' ∅)
      as HH by (rewrite HH; clear; cset_tac).
    apply PIR2_length in H as Lv_len.
    decide (labN l < length Lv).
    + assert ({x : ⦃var⦄ & get Lv (labN l) x}) as [x get_x]
          by (apply get_in_range; eauto).
      rewrite Lv_len in l0.
      assert ({y : ⦃var⦄ & get Lv' (labN l) y}) as [y get_y]
          by (apply get_in_range; eauto).
      erewrite get_nth; eauto.
      erewrite get_nth; eauto.
      eapply get_PIR2; eauto.
    + apply not_le in n.
      rewrite nth_overflow; eauto with cset;
        [ | omega].
      rewrite Lv_len in n.
      rewrite nth_overflow; eauto with cset.
      omega.
  - eapply eq_union_lr; eauto.
    eapply ann_R_get.
    eapply (IH s); eauto.
  - eauto with len.
  - intros; inv_get; eauto with len.
    eapply IH; eauto.
Qed.



Lemma reconstr_live_setTopAnn ZL Lv s alv G a
  : reconstr_live Lv ZL G s alv = reconstr_live Lv ZL G s (setTopAnn alv a).
Proof.
  destruct s, alv; simpl; eauto.
Qed.

Lemma reconstr_live_incl ZL Lv s alv G
  : live_sound Imperative ZL Lv s alv
    -> G ⊆ getAnn alv
    -> poLe (reconstr_live Lv ZL G s alv) alv.
Proof.
  intros LS.
  general induction LS; simpl in *.
  - eapply ann1_poLe; eauto with cset.
    + rewrite H2, IHLS; eauto 20 using Exp.freeVars_live with cset.
      rewrite Exp.freeVars_live; eauto.
      unfold poLe; simpl. cset_tac.
  - eapply ann2_poLe; eauto with cset.
    rewrite IHLS1, IHLS2; eauto 20 with cset.
    rewrite Op.freeVars_live; eauto.
    unfold poLe; simpl. cset_tac.
  - eapply ann0_poLe; eauto with cset.
    erewrite !get_nth; eauto.
    unfold poLe; simpl.
    rewrite Op.freeVars_live_list; eauto.
    cset_tac.
  - eapply ann0_poLe; eauto with cset.
    rewrite Op.freeVars_live; eauto.
    unfold poLe; simpl. cset_tac.
  - eapply annF_poLe; eauto with cset.
    + rewrite IHLS; eauto with cset.
      unfold poLe; simpl. cset_tac.
    + eapply PIR2_get; eauto with len.
      intros; inv_get.
      rewrite H1; eauto.
      exploit H2; eauto.
Qed.

Lemma reconstr_live_sound ZL Lv s alv G
  : live_sound Imperative ZL Lv s alv
    -> G ⊆ getAnn alv
    -> live_sound Imperative ZL Lv s (reconstr_live Lv ZL G s alv).
Proof.
  intros LS.
  general induction LS; simpl in *.
  - econstructor; eauto with cset.
    + eapply live_exp_sound_incl.
      * eapply live_freeVars.
      * clear. cset_tac.
    + rewrite <- reconstr_live_G; eauto with cset.
  - econstructor; eauto with cset.
    + eapply live_op_sound_incl.
      * eapply Op.live_freeVars.
      * clear. cset_tac.
  - econstructor; simpl; eauto.
    + erewrite !get_nth; eauto.
      clear. cset_tac.
    + intros.
      erewrite !get_nth; eauto.
      eapply live_op_sound_incl.
      * eapply Op.live_freeVars.
      * do 2 eapply incl_union_left.
        eapply incl_list_union; eauto using map_get_1.
  - econstructor; eauto.
    + eapply live_op_sound_incl.
      * eapply Op.live_freeVars.
      * clear. cset_tac.
  - econstructor; intros; inv_get; eauto with len.
    + eapply live_sound_monotone.
      * eapply IHLS; eauto with cset.
      * eapply PIR2_get; intros; eauto with len.
        eapply get_app_cases in H6 as [? |[? ?]]; inv_get.
        -- rewrite get_app_lt in H5; eauto with len.
           inv_get.
           rewrite reconstr_live_incl; eauto.
           exploit H2; eauto; dcr.
        -- rewrite get_app_ge in H5; len_simpl;
             rewrite H in *; inv_get; eauto.
    + eapply live_sound_monotone.
      * eapply H1; eauto with cset.
        exploit H2; eauto; dcr.
      * eapply PIR2_get; intros; eauto with len.
        eapply get_app_cases in H7 as [? |[? ?]]; inv_get.
        -- rewrite reconstr_live_incl; eauto.
           exploit H2; eauto; dcr.
        -- rewrite get_app_ge in H8; len_simpl;
             rewrite H in *; inv_get; eauto.
    + simpl.
      exploit H2; eauto; dcr.
      split; eauto.
      rewrite <- reconstr_live_G; eauto.
Qed.