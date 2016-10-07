Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm.
Require Import SpillUtil ReconstrLive ReconstrLiveSmall.

Set Implicit Arguments.



Lemma reconstr_live_sound_s
      (slot : var -> var)
      (ZL : list params)
      (G : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Lv : list ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (IB : list (list bool))
  :
    (forall G',
        live_sound Imperative ZL Lv
                   (do_spill slot s (clear_SpL sl) IB)
                   (reconstr_live (slot_merge slot Λ) ZL G'
                                  (do_spill slot s (clear_SpL sl) IB)
                                  (do_spill_rm slot (clear_SpL sl))))
   -> live_sound Imperative ZL Lv
                (do_spill slot s sl IB)
                (reconstr_live (slot_merge slot Λ) ZL G
                               (do_spill slot s sl IB)
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

Lemma al_sub_RfMf

      (als : list (ann ⦃var⦄))
      (rms : list (⦃var⦄ * ⦃var⦄))
      (al : ann ⦃var⦄)
      (R M : ⦃var⦄)
      (n : nat)
  :
    get rms n (R,M)
    -> get als n al
    -> merge rms = getAnn ⊝ als
    -> getAnn al ⊆ R ∪ M
.
Proof.
  intros get_rm get_al H16.
  general induction get_rm;
    invc get_al; invc H16;
      simpl in *; eauto.
Qed.


Lemma ofl_slp_sub_rm
      (al : ann ⦃var⦄)
      (R M : ⦃var⦄)
      (Z : params)
      (slot : var -> var)
  :
    getAnn al ⊆ R ∪ M
    -> of_list Z ⊆ getAnn al
    -> of_list (slot_lift_params slot (R,M) Z) ⊆ R ∪ map slot M
.
Proof.
  intros ofl_in_rm H2'.
  rewrite <- H2' in ofl_in_rm.
  induction Z;
    simpl in *; eauto.
  - clear; cset_tac.
  - assert (of_list Z ⊆ getAnn al) as ofl_al
        by (rewrite <- H2'; clear; cset_tac).
    assert (of_list Z ⊆ R ∪ M) as ofl_rm
        by (rewrite <- ofl_in_rm; clear; cset_tac).
    assert (a ∈ M -> slot a ∈ map slot M)
      as slot_a_in.
    {
      intro a_in.
      apply in_singleton.
      rewrite <- map_singleton.
      apply lookup_set_incl; eauto.
      apply incl_singleton; eauto.
    }
    specialize (IHZ ofl_rm ofl_al).
    decide (a ∈ R ∩ M); simpl.
    + apply inter_iff in i as [a_fst a_snd].
      rewrite IHZ.
      apply slot_a_in in a_snd.
      clear - a_fst a_snd; cset_tac.
    + decide (a ∈ R); simpl.
      * rewrite IHZ.
        clear - i; cset_tac.
      * rewrite add_union_singleton in ofl_in_rm.
        eapply union_incl_split2 in ofl_in_rm as [ofl_in_rm _].
        eapply in_singleton in ofl_in_rm.
        assert (a ∈ M) as a_in
            by (clear - ofl_in_rm n0; cset_tac).
        apply slot_a_in in a_in.
        rewrite IHZ.
        clear - a_in; cset_tac.
Qed.

Lemma nth_mark_elements
      (l : lab)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (rm : ⦃var⦄ * ⦃var⦄)
      (Z : params)
  :
    get ZL l Z
    -> get Λ l rm
    -> nth l (mark_elements ⊜ ZL ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) ⊝ Λ)) nil
      = mark_elements Z ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) rm)
.
Proof.
  intros get_Z get_rm.
  apply get_nth.
  eapply zip_get; eauto.
  eapply map_get_eq; eauto.
Qed.





Lemma sla_extargs_slp_length
      (slot : var -> var)
      (R_f M_f Sl : ⦃var⦄)
      (ZL : list params)
      (Z : params)
      (l : lab)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Y : args)
  :
    length Y = length Z
    -> ❬slot_lift_args slot Sl
                      ⊝ extend_args Y
                      (mark_elements Z ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∩ snd RM) (R_f,M_f)))❭
      = ❬slot_lift_params slot (R_f, M_f) Z❭
.
Proof.
  intros H2.
  unfold slot_lift_params.
  rewrite !map_length.
  general induction Z; inv H2;
    simpl; eauto.
  - apply length_zero_iff_nil in H2.
    rewrite H2.
    eauto with len.
  - fold slot_lift_params.
    fold slot_lift_params in IHZ.
    destruct Y; isabsurd.
    simpl.
    decide (a ∈ R_f ∩ M_f);
      unfold extend_args;
      simpl; eauto.
    decide (a ∈ R_f);
      simpl; eauto.
Qed.


Lemma get_Y_from_extargs
      (Y : args)
      (ib : list bool)
      (y : op)
      (n : nat)
  :
    get (extend_args Y ib) n y
    -> exists n', get Y n' y
.
Proof.
  intros get_ext.

  general induction get_ext;
    destruct Y;
    destruct ib;
    simpl; isabsurd; eauto.
  - exists 0.
    invc Heql.
    econstructor; eauto.
  - exists 0.
    invc Heql.
    destruct b; simpl in H0; invc H0;
      econstructor; eauto.
  - exists (S n).
    invc Heql.
    econstructor; eauto.
  - destruct b; simpl in *.
    + specialize (IHget_ext (o :: Y) (false :: ib)).
      simpl in IHget_ext.
      invc Heql.
      apply IHget_ext; eauto.
    + specialize (IHget_ext Y ib).
      invc Heql.
      assert (extend_args Y ib = extend_args Y ib)
        as refl by reflexivity.
      apply IHget_ext in refl as [n0 get_x].
      exists (S n0).
      econstructor; eauto.
Qed.



Lemma reconstr_live_sound
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M VD : ⦃var⦄)
      (s : stmt)
      (Lv : list ⦃var⦄)
      (sl : spilling)
      (alv : ann ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  : injective_on VD slot
    -> disj VD (map slot VD)
    -> R ⊆ VD
    -> M ⊆ VD
    -> union_fs (getAnn ra) ⊆ VD
    -> app_expfree s
    -> renamedApart s ra
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl alv
    -> PIR2 Equal (merge Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> live_sound Imperative ZL Lv s alv
    -> live_sound Imperative
                 ((slot_lift_params slot) ⊜ Λ ZL)
                 (slot_merge slot Λ)
                 (do_spill slot s sl (mark_elements
                                        ⊜ ZL ((fun RM => fst RM ∩ snd RM) ⊝ Λ)))
                 (reconstr_live (slot_merge slot Λ)
                                ((slot_lift_params slot) ⊜ Λ ZL)
                                 G
                                 (do_spill slot s sl (mark_elements
                                                        ⊜ ZL ((fun RM => fst RM ∩ snd RM) ⊝ Λ)))
                                (do_spill_rm slot sl))
.
Proof.
  intros inj_VD disj_VD R_VD M_VD ra_VD aeFree renAp spillSnd spilli pir2_EQ Z_VD lvSnd.

  general induction lvSnd;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    inv renAp;
    apply reconstr_live_sound_s;
    intros G'.

  - rename sl0 into sl.
    assert (x ∈ VD) as x_VD by (eapply x_VD; eauto).
    rewrite do_spill_empty by apply count_clear_zero.
    unfold do_spill_rec.
    rewrite do_spill_rm_empty by apply count_clear_zero.
    simpl.

    econstructor; eauto.
    + eapply IHlvSnd with (ra:=an) (R:={x; (R\K ∪ L) \Kx}) (M:=Sp ∪ M); eauto.
      * eapply Rx_VD with (R:=R) (M:=M); eauto.
      * eapply M'_VD with (R:=R) (M:=M); eauto.
      * eapply renamedApart_incl in renAp as rena.
        rewrite rena. eauto.
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

    apply renamedApart_incl in renAp as [rena1 rena2].
    assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    econstructor; eauto.
    + eapply IHlvSnd1 with (ra:=ans) (R:=R\K ∪ L); eauto.
      rewrite rena1. eauto.
    + eapply IHlvSnd2 with (ra:=ant) (R:=R\K ∪ L); eauto.
      rewrite rena2; eauto.
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
    + eapply zip_get; eauto.
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
      assert (of_list (nth (labN l) (slot_lift_params slot ⊜ Λ ZL) nil)
              [=] of_list (slot_lift_params slot (R_f,M_f) Z))
        as nth_slp by (erewrite nth_zip; eauto; simpl; reflexivity).
      rewrite nth_slp.
      clear; cset_tac.
    + erewrite nth_mark_elements; eauto.
      apply sla_extargs_slp_length; eauto.
    + intros; inv_get.
      erewrite nth_mark_elements; eauto.
      erewrite nth_mark_elements in H; eauto.
      assert (get_x := H).
      eapply get_Y_from_extargs in get_x as [n' get_x].
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

    apply renamedApart_incl in renAp as [renaF rena2].
    rewrite fst_zip_pair by eauto with len.
    econstructor; simpl; eauto.
    + rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

      apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- zip_app.
        rewrite <- map_app.
        eapply IHlvSnd with (ra:=ant) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (R:=R) (M:=M); eauto.
        -- eapply M'_VD with (R:=R) (M:=M); eauto.
        -- rewrite rena2; eauto.
        -- rewrite merge_app.
           eapply getAnn_als_EQ_merge_rms; eauto.

        -- eapply get_ofl_VD; eauto.
        -- eauto with len.
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        rewrite <- zip_app.
        rewrite <- map_app.
        -- intros n x x' H4 H5.
           unfold slot_merge in H5.
           inv_get; simpl.
           rename x into Zs.
           rename x0 into rm.
           rename x4 into sl_s.
           rename x1 into a.
           rename x2 into al.
           rename H28 into get_al.
           rename H4 into get_a.
           rename H26 into get_sls.
           rename H29 into get_Zs.
           rename H5 into get_rm.

           rewrite slot_merge_app.

           exploit H19 as H24'; eauto. (*H31*)
           exploit H23 as H20'; eauto. (*H32*)
           exploit renaF as renaF'; eauto.
           exploit H14 as H15'; eauto. (*H33*)
           exploit H2 as H2'; eauto.
           destruct H2' as [H2' _].
           destruct H15' as [A [B [C E]]].
           assert (rm = (fst rm, snd rm)) as rm_eta by apply pair_eta.
           rewrite rm_eta in H24'.
           erewrite reconstr_live_small with (VD:=VD)
                                             (ra:=a)
                                             (R:=fst rm)
                                             (M:=snd rm); eauto.
           ++ (*clear - pir2_EQ pir3 renaF H24 H20 H15 H2 H16 H20 H8 H13 H14 H H9 H18 ra_VD.*)
             clear - rm_eta H2' get_al get_a get_sls get_rm get_Zs H15.
             rewrite rm_eta in get_rm.
             eapply al_sub_RfMf in get_rm; eauto.
             rewrite rm_eta.
              repeat apply union_incl_split;
                [clear; cset_tac | clear; cset_tac
                 | eapply ofl_slp_sub_rm; eauto ].
           ++ rewrite renaF'; eauto.
           ++ rewrite merge_app.
              eapply getAnn_als_EQ_merge_rms; eauto.
           ++ eapply get_ofl_VD; eauto.
        -- unfold slot_merge.
           do 2 rewrite Coqlib.list_length_map; eauto.
        -- rewrite <- zip_app.
           rewrite <- map_app.
           rewrite map_length.
           ++ rewrite zip_length2.
              ** rewrite zip_length2; eauto with len.
              ** rewrite zip_length2, map_length;
                   eauto with len.
           ++ eauto with len.
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
      * rewrite <- zip_app.
        rewrite <- map_app.
        assert ((fst x1, snd x1) = x1)
          by (destruct x1; simpl; reflexivity).
        rewrite <- H30 in H29.
        exploit H23; eauto.
        eapply H1 with (ra:=x) (R:=fst x1) (M:=snd x1); eauto.
        -- exploit renaF as renaF'; eauto.
           rewrite renaF'; eauto.
        -- rewrite merge_app.
           eapply getAnn_als_EQ_merge_rms; eauto.
        -- eapply get_ofl_VD; eauto.
        -- eauto with len.
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
           rewrite <- zip_app.
           rewrite <- map_app.
           rename x5 into a.
           rename x6 into al.
           rename x7 into rm.
           rename x8 into sl_s.
           rename x4 into Zs.
           assert (x' = fst rm ∪ map slot (snd rm)).
           {
             unfold slot_merge in H31.
             eapply map_get in H31; eauto.
           }
           exploit H19; eauto.
           exploit H23; eauto.
           erewrite reconstr_live_small with (ra:=a)
                                             (VD:=VD)
                                             (R:=fst rm)
                                             (M:=snd rm); eauto.

           ++ exploit H2 as H2'; eauto.
              destruct H2' as [H2' _].
              rewrite H36.
              rewrite pair_eta with (p:=rm); simpl.
              rewrite pair_eta with (p:=rm) in H35.
              eapply al_sub_RfMf in H35; eauto.
              repeat apply union_incl_split; [clear; cset_tac | clear; cset_tac | ].
              eapply ofl_slp_sub_rm; eauto.
           ++ exploit renaF as renaF'; eauto.
              rewrite renaF'; eauto.
           ++ rewrite merge_app.
              eapply getAnn_als_EQ_merge_rms; eauto.
           ++ eapply get_ofl_VD; eauto.
           ++ assert ((fst rm, snd rm) = rm)
               by (destruct rm; simpl; reflexivity).
              rewrite H39; eauto.
           ++ eauto with len.

        -- unfold slot_merge.
           do 2 rewrite Coqlib.list_length_map; eauto.
           do 2 rewrite zip_length2; eauto with len.

    + intros.
      inv_get.
      simpl.
      split; [ | auto].
      apply reconstr_live_G.
Qed.
