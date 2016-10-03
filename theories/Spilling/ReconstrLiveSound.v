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

Lemma ofl_slp_sub_rm:
  forall (F : 〔params * stmt〕) (als : 〔ann ⦃var⦄〕) (slot : var -> var) 
         (rms : 〔⦃var⦄ * ⦃var⦄〕) (sl_F : 〔spilling〕),
    merge rms = getAnn ⊝ als ->
    forall (ans : 〔ann (⦃var⦄ * ⦃var⦄)〕) (n : nat) (rm : ⦃var⦄ * ⦃var⦄),
      get rms n rm ->
      forall (Zs : params * stmt) (sl_s : spilling),
        get F n Zs ->
        get sl_F n sl_s ->
        forall a : ann (⦃var⦄ * ⦃var⦄),
          get ans n a ->
          forall al : ann ⦃var⦄,
            get als n al ->
            of_list (fst Zs) ⊆ getAnn al ->
            of_list (slot_lift_params slot (snd rm) (fst Zs)) ⊆ fst rm ∪ map slot (snd rm).
Proof.
  intros F als slot rms sl_F H16 ans n rm get_rm Zs sl_s get_Zs get_sls a get_a al get_al H2'.
  
  assert (of_list (fst Zs) ⊆ fst rm ∪ snd rm) as ofl_in_rm.
  {
    rewrite H2'.
    clear - H16 get_al get_rm.
    general induction get_rm;
      invc get_al; invc H16;
        simpl in *; eauto.
  }
  clear - H2' ofl_in_rm.
  induction (fst Zs); simpl; eauto.
  ** clear; cset_tac.
  ** decide (a ∈ snd rm).
     --- enough (singleton (slot a) ⊆ map slot (snd rm)) as enouf.
         {
           rewrite add_union_singleton.
           rewrite IHl; eauto.
           - rewrite enouf.
             clear; cset_tac.
           - rewrite <- H2'.
             clear; eauto with cset.
           - rewrite <- ofl_in_rm.
             clear; eauto with cset.
         }
         rewrite <- map_singleton.
         apply lookup_set_incl; eauto.
         clear - i; cset_tac.
     --- enough (singleton a ⊆ fst rm) as enouf.
         {
           rewrite add_union_singleton.
           rewrite IHl; eauto.
           - rewrite enouf.
             clear; cset_tac.
           - rewrite <- H2'.
             clear; eauto with cset.
           - rewrite <- ofl_in_rm.
             clear; eauto with cset.
         }
         clear - n ofl_in_rm.
         hnf in ofl_in_rm.
         assert (a ∈ of_list (a :: l)) by eauto with cset.
         exploit ofl_in_rm; eauto.
         apply union_iff in H0 as [H0 | H0]; eauto with cset.
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
    -> PIR2
        (fun (rm : ⦃var⦄ * ⦃var⦄) (Z : params) =>
           disj (fst rm ∩ of_list Z) (snd rm ∩ of_list Z) /\ of_list Z ⊆ VD) Λ ZL
    -> live_sound Imperative ZL Lv s alv
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
  intros inj_VD disj_VD R_VD M_VD ra_VD aeFree renAp spillSnd spilli pir2_EQ pir3 lvSnd.

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

    apply renamedApart_incl in renAp as [renaF rena2].
    rewrite fst_zip_pair by eauto with len.
    econstructor; simpl; eauto.
    + rewrite fst_zip_pair by eauto with len.
      rewrite slot_merge_app.
      rewrite slot_lift_params_app; eauto with len.

      apply live_sound_monotone with (LV:= slot_merge slot (rms ++ Λ)).
      * rewrite <- map_app.
        eapply IHlvSnd with (ra:=ant) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (R:=R) (M:=M); eauto.
        -- eapply M'_VD with (R:=R) (M:=M); eauto.
        -- rewrite rena2; eauto.
        -- rewrite merge_app.
           eapply getAnn_als_EQ_merge_rms; eauto.
           
        -- eapply disj_RfMf_pir2_app; eauto.      
      * rewrite <- slot_merge_app.
        apply PIR2_app with (L2:=slot_merge slot Λ);
          swap 1 2.
        {
          apply PIR2_refl; eauto.
        }
        apply PIR2_get.
        -- intros n x x' H4 H5.
           unfold slot_merge in H5.
           inv_get; simpl.
           rename x into Zs.
           rename x0 into rm.
           rename x4 into sl_s.
           rename x1 into a.
           rename x2 into al.
           rename H29 into get_al.
           rename H4 into get_a.
           rename H27 into get_sls.
           rename H30 into get_Zs.
           rename H5 into get_rm.
                  
           rewrite slot_merge_app.
           rewrite <- map_app.
           exploit H24 as H24'; eauto. (*H31*)
           exploit H20 as H20'; eauto. (*H32*)
           exploit renaF as renaF'; eauto.
           exploit H15 as H15'; eauto. (*H33*)
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
              clear - H2' get_al get_a get_sls get_rm get_Zs H16.
              repeat apply union_incl_split;
                [clear; cset_tac | clear; cset_tac
                 | eapply ofl_slp_sub_rm; eauto ].              
           ++ rewrite renaF'; eauto.
           ++ rewrite merge_app.
              eapply getAnn_als_EQ_merge_rms; eauto.
           ++ clear - pir3 H8 H9 H15 renaF H14 H18 ra_VD.
              eapply disj_RfMf_pir2_app; eauto.
           ++ eapply H20; eauto.
              rewrite <- rm_eta; eauto.
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
        assert ((fst x, snd x) = x)
          by (destruct x; simpl; reflexivity).
        rewrite <- H31 in H30.
        exploit H24; eauto.
        eapply H1 with (ra:=x0) (R:=fst x) (M:=snd x); eauto.
        -- exploit renaF as renaF'; eauto.
           rewrite renaF'; eauto.
        -- rewrite merge_app.
           eapply getAnn_als_EQ_merge_rms; eauto.
        -- eapply disj_RfMf_pir2_app; eauto. 
      *  rewrite <- slot_merge_app.
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
           rewrite <- map_app.
           rename x5 into rm.
           rename x6 into a.
           rename x7 into al.
           rename x8 into sl_s.
           rename x4 into Zs.
           assert (x' = fst rm ∪ map slot (snd rm)).
           {
             unfold slot_merge in H32.
             eapply map_get in H32; eauto.
           }
           exploit H24; eauto.
           erewrite reconstr_live_small with (ra:=a)
                                             (VD:=VD)
                                             (R:=fst rm)
                                             (M:=snd rm); eauto.

           ++ exploit H2 as H2'; eauto.
              destruct H2' as [H2' _].
              rewrite H37.
              repeat apply union_incl_split; [clear; cset_tac | clear; cset_tac | ].
              eapply ofl_slp_sub_rm; eauto.                     
           ++ exploit renaF as renaF'; eauto.
              rewrite renaF'; eauto.
           ++ rewrite merge_app.
              eapply getAnn_als_EQ_merge_rms; eauto.
           ++ eapply disj_RfMf_pir2_app; eauto.
           ++ eapply H20; eauto.
              assert ((fst rm, snd rm) = rm)
                by (destruct rm; simpl; reflexivity).
              rewrite H39; eauto.
           
        -- unfold slot_merge.
           do 2 rewrite Coqlib.list_length_map; eauto.
           do 2 rewrite zip_length2; eauto with len.

    + intros.
      inv_get.
      simpl.
      split; [ | auto].
      apply reconstr_live_G.
Qed.

