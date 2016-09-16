Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill DoSpillRm DiscardMergeSl.
Require Import SpillUtil SpillLive SpillLiveSmall.


Set Implicit Arguments.


Lemma simpl_als
      F
      als
  :
    length F = length als
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get als n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
    ->                (fun (rm : ⦃var⦄) (ps : params * stmt)
                      => rm ∪ of_list (fst ps)) ⊜ (getAnn ⊝ als) F
                                               === getAnn ⊝ als
.
Proof.
  intros H H2.
  revert dependent F; induction als;
    intros F H H2; simpl; eauto.
  destruct F ; simpl; eauto.
  + isabsurd.
  + econstructor.
    * assert (get (p::F) 0 p) as get_p.
      { econstructor. }
      assert (get (a::als) 0 a) as get_a.
      { econstructor. }
      exploit H2; eauto.
      change (Equal_pw ⦃var⦄ var In (getAnn a ∪ of_list (fst p)) (getAnn a))
      with (getAnn a ∪ of_list (fst p) [=] getAnn a).
      cset_tac.
    * apply IHals; eauto.
      intros.
      apply H2 with (n:= S(n)); econstructor; eauto.
Qed.



Lemma spill_live_sound_s
      (slot : var -> var)
      (n : nat)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (Lv : list (set var))
      (s : stmt)
      (sl sl': ann (set var * set var * option (list (set var * set var))))
  :
    sub_spill sl' sl
    -> n = count sl'
    -> let sl0 := setTopAnn sl (∅,∅,snd (getAnn sl)) in
   (forall G', live_sound Imperative ZL Lv
              (do_spill slot s sl0)
              (spill_live (slot_merge slot Λ) ZL G'
                          (do_spill slot s sl0)
                          (discard_merge_sl slot (do_spill_rm' slot 0 sl))))
-> live_sound Imperative ZL Lv
              (do_spill slot s sl')
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl')
                          (discard_merge_sl slot (do_spill_rm' slot n sl))).
Proof.

set (Sp' := fst (fst (getAnn sl'))).
set (L'  := snd (fst (getAnn sl'))).
set (rm' := snd (getAnn sl')).
intros sub_sl n_count sl0 strong_sls.

remember (cardinal Sp') as n_Sp'.
symmetry in Heqn_Sp'.
rename Heqn_Sp' into card_Sp'.
revert dependent sl'.
revert G.
revert n.
induction n_Sp';
  intros n G sl' Sp' L' rm' sub_sl n_count card_Sp'.

- remember (cardinal L') as n_L'.
  symmetry in Heqn_L'.
  rename Heqn_L' into card_L'.
  revert dependent sl'.
  revert G.
  revert n.
  induction n_L';
    intros n G sl' Sp' L' rm' sub_sl n_count card_Sp' card_L'.

  {
    assert (count sl' = 0) as count_sl'.
    { unfold count. subst Sp'. subst L'.
      rewrite card_Sp'. rewrite card_L'. omega. }
    rewrite do_spill_empty_invariant
    with (Sp':=∅) (L':=∅) (sl':=sl0);
      simpl; eauto; try apply empty_1;
      try apply cardinal_Empty; eauto.

    + rewrite n_count.
      rewrite count_sl'.
      rewrite do_spill_rm_zero.
      destruct sl; destruct a; destruct p; apply strong_sls.
    + subst sl0.
      unfold sub_spill in sub_sl.
      destruct  sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite <- eq_rm.
      rewrite top_sl'.
      rewrite setTopAnn_setTopAnn.
      rewrite getAnn_setTopAnn.
      subst rm'.
      reflexivity.
  }


  rewrite do_spill_L.
  Focus 2. rewrite cardinal_Empty. subst Sp'. assumption.
  Focus 2. clear - card_L'. intro N.
           apply cardinal_Empty in N. subst L'. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  subst L'.
  rewrite card_L'.
  rewrite card_Sp'.
  simpl.

  rewrite do_spill_rm_s.

  rewrite discard_merge_sl_step.

  constructor; fold spill_live.

  * apply IHn_L'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.

    -- rewrite count_reduce_L with (n:=n_L') (m:=n_L'); eauto.
       unfold count. rewrite card_Sp'. rewrite card_L'. eauto.
    -- rewrite getAnn_setTopAnn.
       simpl.
       assumption.
    -- rewrite getAnn_setTopAnn.
       simpl. erewrite cardinal_set_tl. eauto.
       rewrite of_list_elements. rewrite card_L'. eauto.
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl'))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

- rewrite do_spill_Sp.
  Focus 2. subst Sp'. clear - card_Sp'. intro N.
           apply cardinal_Empty in N. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  rewrite card_Sp'.
  simpl.


  rewrite do_spill_rm_s with (n:=n_Sp' + cardinal L').

  econstructor; fold spill_live.
  * apply IHn_Sp'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.
    -- rewrite count_reduce_Sp with (n:=n_Sp' + cardinal L') (m:=n_Sp'); eauto.
       unfold count. rewrite card_Sp'. subst L'. omega.
    -- rewrite getAnn_setTopAnn.
       simpl.
       erewrite cardinal_set_tl; eauto.
       rewrite of_list_elements.
       rewrite card_Sp'.
       omega.
     * apply live_exp_sound_incl
        with (lv':= singleton (hd 0 (elements (fst (fst (getAnn sl')))))).
      -- econstructor. econstructor. eauto with cset.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.
Qed.





Lemma spill_live_sound
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (R M : set var)
      (s : stmt)
      (Lv : list (set var))
      (sl : ann (set var * set var * option (list (set var * set var))))
      (alv : ann (set var))
  :  app_expfree s
   -> spill_sound k ZL Λ (R,M) s sl
   -> some_spill_live sl alv
   -> PIR2 Equal (merge Λ) Lv
   -> live_sound Imperative ZL (merge Λ) s alv
   -> live_sound Imperative
                (slot_lift_params slot ⊜ ZL Λ)
                (slot_merge slot Λ)
                (do_spill slot s sl)
                (spill_live (slot_merge slot Λ)
                            (slot_lift_params slot ⊜ ZL Λ)
                             G
                            (do_spill slot s sl)
                            (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound sSpillLv PEQ lvSound.

general induction lvSound;
  invc aeFree;
  inv sSpillLv;
  inv spillSound;
  apply spill_live_sound_s;
  try apply sub_spill_refl; eauto.

- rename sl0 into sl.

  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step. simpl.

  econstructor.
  + eapply IHlvSound; eauto.
  + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
    * apply Exp.live_freeVars.
    * clear. cset_tac.
  +  clear. cset_tac.
  + apply spill_live_G.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + eapply IHlvSound1; eauto.
  + eapply IHlvSound2; eauto.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
  + clear. cset_tac.
  + clear. cset_tac.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  intro G'.

  assert (get (slot_lift_params slot ⊜ ZL Λ) l (slot_lift_params slot Z0 (R_f,M_f)))
    as get_slp.
  { apply zip_get; eauto. }
  rewrite get_nth with (m:=slot_lift_params slot Z0 (R_f,M_f)); eauto.
  assert (Z = Z0) as eq_Z.
  { apply get_get_eq with (L:=ZL) (n:=counted l); eauto. }
  subst Z0.
  assert (get (slot_merge slot Λ) l (R_f ∪ map slot M_f)) as get_rfmf.
  { apply map_get_eq with (x:=(R_f,M_f)); simpl; eauto. }

  econstructor; simpl in *; eauto;
    [ erewrite get_nth
    | unfold slot_lift_params; eauto with len
    | erewrite get_nth ]
    ; eauto.
  + clear. cset_tac.
  + admit. (* We need some new assumptions to prove this *)
  + intros n y get_y.
    apply live_op_sound_incl with (lv':=Op.freeVars y).
    * apply Op.live_freeVars.
    * repeat apply incl_union_left.
      eapply get_list_union_map; eauto.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.




- specialize (IHlvSound k slot).
  change (snd (getAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t)))
    with (⎣ rms ⎦).
  change (setTopAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t) (∅, ∅, ⎣ rms ⎦))
    with (annF (∅,∅,⎣ rms ⎦) sl_F sl_t).
  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  intros G'.

  econstructor;  simpl in *; eauto.
  + rewrite fst_F; eauto.
    apply live_sound_monotone with (LV:= slot_merge slot rms ++ slot_merge slot Λ).
    * apply live_sound_ann_ext with (lv:= spill_live
        (slot_merge slot rms ++ slot_merge slot Λ)
        (slot_lift_params slot ⊜ (fst ⊝ F) rms ++ slot_lift_params slot ⊜ ZL Λ)
         ∅
        (do_spill slot t sl_t)
        (discard_merge_sl slot (do_spill_rm slot sl_t))).
      -- apply spill_live_equal.
         apply PIR2_app.
         ++ apply PIR2_get.
            ** intros.
               erewrite get_get_eq with (x:=x)
                                        (x':=x')
                                        (L:=slot_merge slot rms)
                                        (n:=n); eauto.
           ** reflexivity.
         ++ apply PIR2_refl; eauto.
      --
         rewrite slot_lift_params_app; eauto with len.
         rewrite slot_merge_app.
         eapply IHlvSound; eauto.
         ** unfold merge.
            rewrite map_app.
            rewrite <- H10.
            reflexivity.
         ** apply PIR2_app; eauto.
            apply PIR2_refl; eauto.
    * apply PIR2_app with (L2:=slot_merge slot Λ).
      -- apply PIR2_get.
         ++ intros.
            unfold slot_merge in H5.
            inv_get; simpl.
            rewrite slot_merge_app.
            rewrite slot_lift_params_app; eauto with len.
            erewrite spill_live_small with (R:=fst x0) (M:=snd x0); eauto.
            ** exploit H2 as H2'; eauto.
               destruct H2' as [H2' _].
               unfold slot_lift_params.
               rewrite of_list_elements.
               rewrite H2'.
               rewrite map_slot_cut.
               cset_tac.
            ** unfold merge. rewrite map_app.
               unfold merge in H10.
               rewrite H10.
               apply PIR2_refl; eauto.
            ** eapply H25; eauto.
               enough (x0 = (fst x0, snd x0)) as enog.
               { rewrite <- enog. eauto. }
               clear. rewrite injective_projections with (p2:=x0);simpl;eauto.
         ++ unfold slot_merge.
            do 2 rewrite Coqlib.list_length_map; eauto.
            do 2 rewrite zip_length2; eauto with len.
      -- apply PIR2_refl; eauto.
  + symmetry. apply zip_length2.
    repeat rewrite Coqlib.list_length_map.
    rewrite zip_length2; eauto with len.
  + intros.
    inv_get.
    simpl.
    rewrite fst_F; eauto.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app.
    apply live_sound_monotone with (LV:=slot_merge slot rms ++ slot_merge slot Λ).
     * apply live_sound_ann_ext with (lv:= spill_live
        (slot_merge slot rms ++ slot_merge slot Λ)
        (slot_lift_params slot ⊜ ((fst ⊝ F) ++ ZL) (rms ++ Λ))
        (of_list (slot_lift_params slot (fst x) x3))
        (do_spill slot (snd x) x2)
        (discard_merge_sl slot (do_spill_rm slot x2))).
       -- apply spill_live_equal.
          rewrite <- slot_merge_app.
          apply PIR2_app.
          ++ apply PIR2_get.
             ** intros.
                erewrite get_get_eq with (x:=x1)
                                           (x':=x')
                                           (L:=slot_merge slot rms)
                                           (n:=n0); eauto.
           ** reflexivity.
         ++ apply PIR2_refl; eauto.
      -- rewrite slot_merge_app.
         eapply H1 with (R:=fst x3) (M:=snd x3); eauto.
         ** eapply H25 ; eauto.
            rewrite injective_projections with (p2:=x3); eauto.
         ** unfold merge.
            rewrite map_app.
            rewrite <- H10.
            reflexivity.
         ** apply PIR2_app; eauto.
            apply PIR2_refl; eauto.
    * apply PIR2_app with (L2:=slot_merge slot Λ).
      -- apply PIR2_get.
         ++ intros.
            unfold slot_merge in H14.
            inv_get; simpl.
            erewrite spill_live_small with (R:=fst x4) (M:=snd x4); eauto.
            ** exploit H2 as H2'; eauto.
               destruct H2' as [H2' _].
               unfold slot_lift_params.
               rewrite of_list_elements.
               rewrite H2'.
               rewrite map_slot_cut.
               clear.
               cset_tac.
            ** unfold merge. rewrite map_app.
               unfold merge in H10.
               rewrite H10.
               apply PIR2_refl; eauto.
            ** eapply H25; eauto.
               rewrite injective_projections with (p2:=x4); eauto.
         ++ unfold slot_merge.
            do 2 rewrite Coqlib.list_length_map; eauto.
            do 2 rewrite zip_length2; eauto with len.
      -- apply PIR2_refl; eauto.
    * eauto with len.
  + intros.
    inv_get.
    simpl.
    split; [ | auto].
    apply spill_live_G_set.
Admitted.