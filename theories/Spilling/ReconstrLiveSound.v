Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm.
Require Import SpillUtil ReconstrLive.

Set Implicit Arguments.




Lemma reconstr_live_sound_s
      (slot : var -> var)
      (ZL : list params)
      (G : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Lv : list ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    (forall G',
        live_sound Imperative ZL Lv
                   (do_spill slot s (clear_SpL sl))
                   (reconstr_live (slot_merge slot Λ) ZL G'
                                  (do_spill slot s (clear_SpL sl))
                                  (do_spill_rm slot (clear_SpL sl))))
   -> live_sound Imperative ZL Lv
                (do_spill slot s sl)
                (reconstr_live (slot_merge slot Λ) ZL G
                               (do_spill slot s sl)
                               (do_spill_rm slot sl)).
Proof.
  intros sls.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.


  unfold count.

  (* prepare induction *)
  remember (elements (getSp sl)) as elSp.
  symmetry in HeqelSp.
  remember (elements (getL  sl)) as elL.
  symmetry in HeqelL.
  do 2 rewrite <- elements_length.
  rewrite HeqelL.
  rewrite HeqelSp.
  clear HeqelSp.
  revert G.
  induction elSp;
    intros G;
    simpl.
  - (*apply elements_nil_eset in HeqelSp as empty_Sp.*)
    revert G.
    clear HeqelL.
    induction elL;
      intros G;
      simpl in *.
    + apply sls.

    + rewrite add_anns_S.

      constructor; eauto; fold reconstr_live.
      * simpl.
        apply live_exp_sound_incl with (lv':=singleton (slot a)).
        -- econstructor.
           econstructor.
           cset_tac.
        -- clear.
           cset_tac.
      * clear.
        cset_tac.
      * apply reconstr_live_G.
        cset_tac.
  - rewrite add_anns_S.
    econstructor; simpl; eauto.
    * simpl.
      apply live_exp_sound_incl with (lv':=singleton a).
      -- econstructor.
         econstructor.
         cset_tac.
      -- clear.
         cset_tac.
    * clear.
      cset_tac.
    * apply reconstr_live_G.
      cset_tac.
Qed.



Lemma reconstr_live_sound
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (Lv : list ⦃var⦄)
      (sl : spilling)
      (alv : ann ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  : app_expfree s
    -> renamedApart s ra
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live sl alv
    -> PIR2 Equal (merge Λ) Lv
    -> live_sound Imperative ZL (merge Λ) s alv
    -> live_sound Imperative
                 ((slot_lift_params slot) ⊜ (snd ⊝ Λ) ZL)
                 (slot_merge slot Λ)
                 (do_spill slot s sl)
                 (reconstr_live (slot_merge slot Λ)
                                ((slot_lift_params slot) ⊜ (snd ⊝ Λ) ZL)
                                 G
                                (do_spill slot s sl)
                                (do_spill_rm slot sl))
.
Proof.
  intros aeFree renAp spillSnd spilli pir2_EQ lvSnd.

  general induction lvSnd;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    invc renAp;
    apply reconstr_live_sound_s;
    intros G'.

  - rename sl0 into sl.

    rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    econstructor; eauto.
    + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      * apply live_freeVars.
      * clear; cset_tac.
    + clear; cset_tac.
    + apply reconstr_live_G.
      eauto with cset.

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    econstructor; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.
    + clear; cset_tac.
    + clear; cset_tac.

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.
    eapply get_get_eq in H; eauto.
    subst Z0.

    econstructor; eauto.
    + eapply zip_get.
      eapply map_get_eq; eauto.
      eauto.
    + simpl.
      unfold slot_merge.
      eapply map_get_eq; eauto.
    + simpl.
      assert (nth (labN l) (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f)
        as nth_EQ.
      {
        unfold slot_merge.
        assert ((fun RM => fst RM ∪ map slot (snd RM)) (R_f,M_f) = R_f ∪ map slot M_f)
          by (simpl; reflexivity).
        eapply map_get_eq in H13; eauto.
        erewrite get_nth; eauto.
        reflexivity.
      }
      rewrite nth_EQ.
      assert (of_list (nth (labN l) (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) nil)
              [=] of_list (slot_lift_params slot M_f Z))
        as nth_slp by (erewrite nth_zip; eauto; simpl; reflexivity).
      rewrite nth_slp.
      clear; cset_tac.
    + unfold slot_lift_params.
      rewrite !map_length.
      eauto.
    + intros; inv_get.
      exploit H5 as is_var; eauto.
      invc is_var.
      apply live_op_sound_incl
      with (lv':= match slot_lift_args slot Sl (Var v) with
                  | Var v => singleton v
                  | _ => ∅
                  end
           );
        unfold slot_lift_args;
        simpl.
      * decide (v ∈ Sl);
          econstructor;
          eauto with cset.
      * repeat apply incl_union_left.
        decide (v ∈ Sl);
          unfold slot_lift_args;
          simpl;
          [ change (singleton (slot v)) with (Op.freeVars (Var (slot v)))
          | change (singleton v) with (Op.freeVars (Var v)) ];
          eapply get_list_union_map; eauto;
          eapply map_get_eq; eauto;
          simpl;
          decide (v ∈ Sl); simpl; eauto.

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    econstructor; simpl; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.

  - rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    rewrite fst_zip_pair by eauto with len.
    econstructor; simpl; eauto.
    + rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

      apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- map_app.
        eapply IHlvSnd; eauto.
        -- unfold merge.
           rewrite map_app.
           rewrite <- H9.
           reflexivity.
        -- apply PIR2_app; eauto.
           apply PIR2_refl; eauto.
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        -- intros.
           unfold slot_merge in H5.
           inv_get; simpl.
           rewrite slot_merge_app.
           admit.
           (*erewrite spill_live_small with (R:=fst x0) (M:=snd x0); eauto.
           ++ exploit H2 as H2'; eauto.
              destruct H2' as [H2' _].
              unfold slot_lift_params.
              rewrite of_list_elements.
              rewrite H2'.
              rewrite map_slot_cut.
              cset_tac.
           ++ unfold merge. rewrite map_app.
              unfold merge in H10.
              rewrite H10.
              apply PIR2_refl; eauto.
           ++ eapply H25; eauto.
              enough (x0 = (fst x0, snd x0)) as enog.
              { rewrite <- enog. eauto. }
              clear. rewrite injective_projections with (p2:=x0);simpl;eauto.*)
        -- unfold slot_merge.
           do 2 rewrite Coqlib.list_length_map; eauto.
           do 2 rewrite zip_length2; eauto with len.




    + symmetry.
      apply zip_length2.
      repeat rewrite length_map.
      rewrite zip_length2;
        eauto with len.
    + intros; inv_get.
      simpl.
      rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

            apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- map_app.
        exploit H19; eauto.
        assert ((fst x, snd x) = x)
          by (destruct x; simpl; reflexivity).
        rewrite <- H30 in H29.
        eapply H1; eauto.
        -- unfold merge.
           rewrite map_app.
           rewrite <- H9.
           reflexivity.
        -- apply PIR2_app; eauto.
           apply PIR2_refl; eauto.
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        -- intros.
           unfold slot_merge in H5.
           inv_get; simpl.
           rewrite slot_merge_app.
           admit.
           (*erewrite spill_live_small with (R:=fst x0) (M:=snd x0); eauto.
           ++ exploit H2 as H2'; eauto.
              destruct H2' as [H2' _].
              unfold slot_lift_params.
              rewrite of_list_elements.
              rewrite H2'.
              rewrite map_slot_cut.
              cset_tac.
           ++ unfold merge. rewrite map_app.
              unfold merge in H10.
              rewrite H10.
              apply PIR2_refl; eauto.
           ++ eapply H25; eauto.
              enough (x0 = (fst x0, snd x0)) as enog.
              { rewrite <- enog. eauto. }
              clear. rewrite injective_projections with (p2:=x0);simpl;eauto.*)
        -- unfold slot_merge.
           do 2 rewrite Coqlib.list_length_map; eauto.
           do 2 rewrite zip_length2; eauto with len.

    + intros.
      inv_get.
      simpl.
      split; [ | auto].
      apply reconstr_live_G.
