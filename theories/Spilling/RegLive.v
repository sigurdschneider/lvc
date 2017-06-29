Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound SpillUtil.
Require Import RLiveMin RLiveSound.



Set Implicit Arguments.

(** * Register Liveness *)

Fixpoint reg_live
         (ZL : list params)
         (Lv : list ⦃var⦄)
         (G : ⦃var⦄)
         (s : stmt)
         (sl : spilling)
         {struct s}
  : ann ⦃var⦄
  :=
    match s, sl with
    | stmtLet x e s, ann1 (Sp, L, _) sl'
                          (* maybe we have to add Exp.freeVars e and etc.
                             getAnn al [<=] {x; R
*)
      => let lv_s := reg_live ZL Lv (singleton x) s sl' in
        ann1 (G ∪ Sp ∪ (((getAnn lv_s) \ singleton x ∪ Exp.freeVars e) \ L)) lv_s

    | stmtReturn e, ann0 (Sp, L, _)
      => ann0 (G ∪ Sp ∪ (Op.freeVars e \ L))

    | stmtIf e s1 s2, ann2 (Sp, L, _) sl1 sl2
      => let lv1 := reg_live ZL Lv ∅ s1 sl1 in
        let lv2 := reg_live ZL Lv ∅ s2 sl2 in
        ann2 (G ∪ Sp ∪ ((getAnn lv1 ∪ getAnn lv2 ∪ Op.freeVars e) \ L)) lv1 lv2

    | stmtApp f Y, ann0 (Sp, L, (R',M')::nil)
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (G ∪ Sp ∪ (((list_union (Op.freeVars ⊝ Y) ∩ R') ∪ blv \ of_list Z) \ L))

    | stmtFun F t, annF (Sp, L, rms) sl_F sl_t
      => let lv_t := reg_live (fst ⊝ F ++ ZL) (fst ⊝ rms ++ Lv) ∅ t sl_t in
        let lv_F := (fun ps (rmsl : spilling * ⦃var⦄)
                     => let (sl_s, Rf) := rmsl in
                       reg_live (fst ⊝ F   ++ ZL)
                                (fst ⊝ rms ++ Lv)
                                (Rf)
                                (snd ps)
                                 sl_s
                    ) ⊜ F (pair ⊜ sl_F (fst ⊝ rms)) in
        annF (G ∪ Sp ∪ ((getAnn lv_t ∪ G) \ L)) lv_F lv_t

    | _,_ => ann0 G
    end
.

Lemma reg_live_G_eq
      (G : ⦃var⦄)
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (s : stmt)
      (sl : spilling)
  :
    getAnn (reg_live ZL Lv G s sl)
           [=]
           getAnn (reg_live ZL Lv ∅ s sl) ∪ G
.
Proof.
  general induction s;
    destruct sl;
    try destruct a;
    try destruct p;
    simpl; eauto with cset.
  - rewrite IHs. clear. cset_tac.
  - rewrite IHs1; rewrite IHs2.
    clear. cset_tac.
  - induction l0; simpl; eauto with cset.
    + let_pair_case_eq; subst; simpl in *; cases; simpl; eauto with cset.
      clear. cset_tac.
  - cset_tac.
  - rewrite IHs; eauto. clear. cset_tac.
Qed.

Lemma reg_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (G : set var)
      (s : stmt)
      (sl : spilling)
  :
    G ⊆ getAnn (reg_live ZL Lv G s sl)
.
Proof.
  induction s,sl; destruct a,p;
    simpl; eauto with cset.
  - simpl. induction l0; simpl; eauto with cset.
    destruct a,l0; simpl; cset_tac.
Qed.



Lemma reg_live_R k ZL Λ RM  s sl rLv :
    spill_sound k ZL Λ RM s sl
    -> PIR2 Subset rLv (fst ⊝ Λ)
    -> getAnn (reg_live ZL rLv (∅:⦃var⦄) s sl) ⊆ fst RM
.
Proof.
  intros spillSnd pir2. general induction spillSnd; simpl.
  - rewrite reg_live_G_eq. rewrite IHspillSnd; simpl; eauto.
    rewrite H1, H. clear; cset_tac.
  - rewrite H1, H. clear; cset_tac.
  - rewrite H, H1, IHspillSnd1, IHspillSnd2; simpl; eauto. clear; cset_tac.
  - eapply PIR2_nth_2 in pir2 as [Rl [get_Rl Rl_sub]].
    + erewrite !get_nth; eauto. simpl. rewrite Rl_sub, H, H4, H6, H7. clear; cset_tac.
    + eapply map_get_eq; eauto.
  - rewrite reg_live_G_eq. rewrite H, IHspillSnd; eauto.
    + simpl; clear; cset_tac.
    + rewrite List.map_app. apply PIR2_app; eauto.
Qed.


Lemma reg_live_rlive_min k G ZL Λ RM s sl rLv :
  let rlv := reg_live ZL rLv G s sl in
  spill_sound k ZL Λ RM s sl
  -> PIR2 Subset rLv (fst ⊝ Λ)
  -> annotation s rlv
  -> rlive_min k ZL Λ G s sl rlv
.
Proof.
  intros rlv spillSnd pir2 anno. subst rlv. general induction spillSnd; invc anno; cbn.
  - econstructor; eauto.
    unfold is_rlive_min in *. intros. rewrite reg_live_G_eq. clear spillSnd.
    invc H5. rewrite reg_live_R; eauto. cbn. clear - H17 H20; cset_tac.
  - econstructor; eauto.
    unfold is_rlive_min. intros. invc H3. clear - H13 H11. cset_tac.
  - econstructor; eauto. clear spillSnd1 spillSnd2. unfold is_rlive_min. intros.
    invc H3. rewrite !reg_live_R; eauto. cbn. clear - H19 H16. cset_tac.
  - eapply PIR2_nth_2 with (blk:=R_f) in pir2 as [Rl [get_Rl Rl_sub]]; [|eapply map_get_eq;eauto].
    erewrite !get_nth; eauto.
    econstructor; eauto. unfold is_rlive_min.
    intros. rewrite Rl_sub. invc H9. eapply get_get_eq with (x:=Z) in H23;eauto. subst Z0.
    eapply get_get_eq with (x':=(R_f,M_f)) in H24; eauto. invc H24.
    rewrite H18, H25, H27, H28. clear; cset_tac.
  - econstructor; eauto.
    + intros. inv_get.
      eapply rlive_min_G_anti.
      eapply H6; eauto.
      * rewrite List.map_app. eapply PIR2_app; eauto.
      * eapply H13; eauto.
        eapply zip_get_eq; eauto using zip_get.
      * reflexivity.
    + eapply IHspillSnd; eauto.
      rewrite List.map_app. eapply PIR2_app; eauto.
    + unfold is_rlive_min. intros. clear H6 IHspillSnd spillSnd H13 H11 H5. invc H7.
      rewrite reg_live_R; eauto; cbn; [clear - H18; cset_tac|].
      rewrite List.map_app. eapply PIR2_app; eauto.
Qed.



Lemma reg_live_sound k ZL Λ rlv (R M : ⦃var⦄) G s sl
  : spill_sound k ZL Λ (R,M) s sl
    -> PIR2 Subset rlv (fst ⊝ Λ)
    -> rlive_sound ZL rlv s sl (reg_live ZL rlv G s sl)
.
Proof.
  intros spillSnd pir2.
  general induction spillSnd; simpl.
  - econstructor.
    + apply union_incl_left; clear;cset_tac.
    + eapply IHspillSnd; eauto.
    + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      * apply live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear;cset_tac.
    + setoid_rewrite <-incl_right at 3.
      clear; cset_tac.
    + apply reg_live_G. clear; cset_tac.
  - econstructor.
    + clear; cset_tac.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.
  - econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
     + eapply IHspillSnd1; eauto.
    + eapply IHspillSnd2; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
  - assert (pir2' := pir2). eapply PIR2_flip in pir2'. eapply PIR2_nth in pir2'; eauto.
    destruct pir2', H9.
    econstructor; eauto.
    + clear; cset_tac.
    + simpl. erewrite !get_nth; eauto. clear; cset_tac.
    + intros. inv_get.
      apply live_op_sound_incl with (lv':=Op.freeVars y).
      * apply Op.live_freeVars.
      * erewrite <-incl_list_union with (s:=Op.freeVars y); eauto.
        rewrite set_decomp with (s:= Op.freeVars y) (t:= M').
        apply union_incl_split.
        -- clear; cset_tac.
        -- eapply get_live_op_sound in H6; eauto. apply Op.freeVars_live in H6.
           rewrite <-inter_subset_equal with (s':= R' ∪ M'); [|clear - H6; cset_tac].
           clear; cset_tac.
    + rewrite H7 at 1. erewrite !get_nth; eauto. 
  - simpl.
    econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + set (fix1 := fun (ps : params * stmt) (rmsl : spilling * ⦃var⦄) => _ ).
      eapply rlive_sound_monotone with (LV := fst ⊝ rms ++ rlv).
      eapply IHspillSnd; eauto.
     * rewrite List.map_app. apply PIR2_app; [apply PIR2_refl|]; eauto.
     * apply PIR2_app; [|apply PIR2_refl;eauto].
       apply PIR2_get. intros; inv_get.
       -- subst fix1. simpl. rewrite reg_live_G_eq. rewrite reg_live_R.
          ++ instantiate (1:=x0). clear; cset_tac.
          ++ eauto.
          ++ rewrite List.map_app. apply PIR2_app; eauto.
       -- eauto with len.
    + eauto with len.
    + intros; inv_get. eapply rlive_sound_monotone. eapply H6; eauto.
      * apply pair_eta.
      * rewrite List.map_app. apply PIR2_app; eauto.
      * apply PIR2_app; [|apply PIR2_refl;eauto].
        apply PIR2_get. intros; inv_get.
        -- rewrite reg_live_G_eq, reg_live_R; eauto.
           ++ clear; cset_tac.
           ++ rewrite List.map_app. apply PIR2_app; [apply PIR2_refl|]; eauto.
        -- eauto with len.
    + intros; inv_get. rewrite <-reg_live_G. clear; cset_tac.
    + clear; cset_tac.
Qed.


Lemma reg_live_anno ZL R M G sl s Λ k :
  spill_sound k ZL Λ (R,M) s sl
  -> annotation s (reg_live ZL (fst ⊝ Λ) G s sl)
.
Proof.
  intros spillSnd.
  general induction spillSnd; cbn;try econstructor; eauto.
  - eauto with len.
  - intros. inv_get. rewrite <-List.map_app. eapply H6; eauto. rewrite <-surjective_pairing. reflexivity.
  - rewrite <-List.map_app. eapply IHspillSnd; eauto.
Qed.
