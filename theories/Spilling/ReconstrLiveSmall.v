Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import  Spilling DoSpill DoSpillRm SpillUtil ReconstrLive.

Set Implicit Arguments.


Lemma reconstr_live_remove_G
      Lv ZL G s sl G'
  :
    getAnn (reconstr_live Lv ZL G s sl) \ G
           ⊆ getAnn (reconstr_live Lv ZL G' s sl)
.
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.



Lemma reconstr_live_small_L
      (k : nat)
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_SpL sl))
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s (clear_Sp sl))
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
  intros L_sub cleared.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  remember (elements (getL sl)) as elL.
  rewrite count_clearSp.
  rewrite getSp_clearSp.
  rewrite getL_clearSp.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  rewrite setTopAnn_setTopAnn.
  rewrite elements_empty.
  simpl.
  rewrite <- elements_length.
  rewrite <- HeqelL.


  assert (of_list elL ⊆ getL sl) as H
    by (rewrite HeqelL; rewrite of_list_elements; reflexivity).
  clear HeqelL.
  revert G.
  induction elL;
    intros G;
    simpl in *.
  + rewrite add_anns_zero.
    apply cleared.
  + rewrite add_anns_S.
    simpl.
    rewrite IHelL; eauto.
    * enough (singleton (slot a) ⊆ map slot (getSp sl ∪ M)) as in_M.
      {
        rewrite in_M; eauto.
        rewrite !SetOperations.map_app; eauto.
        clear; cset_tac.
      }
      apply incl_singleton.
      apply map_iff; eauto.
      exists a.
      split; eauto.
      rewrite <- L_sub.
      rewrite <- H.
      clear; cset_tac.
    * rewrite <- H.
      clear; cset_tac.
Qed.



Lemma reconstr_live_small_Sp
      (k : nat)
      (sl : spilling)
      (ZL : list (params))
      (R M Sp' G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    getSp sl ⊆ R
    -> Sp' ⊆ getSp sl
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_Sp sl))
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s (setSp sl Sp'))
           (do_spill_rm slot (setSp sl Sp')))
        ⊆ R ∪ map slot (getSp sl \ Sp' ∪ M) ∪ G
.
Proof.
  intros Sp_sub Sp'_sub clearedSp.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  rewrite do_spill_extract_writes in clearedSp.
  rewrite do_spill_rm_s in clearedSp.
  rewrite getSp_clearSp in clearedSp.
  rewrite getL_clearSp in clearedSp.
  rewrite elements_empty in clearedSp.
  rewrite count_clearSp in clearedSp.
  unfold clear_Sp in clearedSp.
  rewrite setTopAnn_setTopAnn in clearedSp.
  rewrite getAnn_setTopAnn in clearedSp.
  simpl in clearedSp.

  remember (elements Sp') as elSp.

  unfold count.
  rewrite <- elements_length.
  rewrite getSp_setSp.
  rewrite <- HeqelSp.
  unfold setSp.
  rewrite setTopAnn_setTopAnn.
  rewrite getAnn_setTopAnn.
  simpl.

  assert (Sp' [=] of_list elSp) as Sp_EQ
    by (rewrite HeqelSp; rewrite of_list_elements; reflexivity).
  clear HeqelSp.
  general induction elSp;
    simpl in *.

  - rewrite clearedSp.
    rewrite !SetOperations.map_app; eauto.
    rewrite Sp_EQ.
    assert (getSp sl \ ∅ [=] getSp sl) as H by (clear; cset_tac).
    rewrite H.
    clear; cset_tac.
  - rewrite add_anns_S.
    simpl.
    rewrite IHelSp with (Sp':=Sp' \ singleton a) ; eauto.
    + rewrite SetOperations.map_app; eauto.
      rewrite -> SetOperations.map_app; eauto.
      rewrite !lookup_set_minus_eq; eauto.
      unfold lookup_set.
      rewrite map_singleton.
      enough (singleton a ⊆ R) as in_R
          by (rewrite in_R; clear; cset_tac).
      rewrite <- Sp_sub.
      rewrite <- Sp'_sub.
      rewrite Sp_EQ.
      clear; cset_tac.
      admit. admit. admit.
    + rewrite Sp'_sub.
      clear; cset_tac.
    + rewrite Sp_EQ.
      clear; cset_tac.
      admit.
Admitted.


Lemma reconstr_live_small_s
      (k : nat)
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    injective_on D slot
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G'
           (do_spill slot s (clear_Sp sl))
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s sl)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros slot_inj Sp_sub L_sub cleared.
  apply reconstr_live_small_Sp.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  unfold count.

  enough (forall Sp' : ⦃var⦄, Sp' ⊆ getSp sl
                         -> getL sl ⊆ Sp' ∪ M
                         -> getAnn
     (reconstr_live (slot_merge slot Λ) (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL) G
        (write_spills slot (elements Sp')
           (write_loads slot (elements (getL sl)) (do_spill slot s (setTopAnn sl (∅, ∅, getRm sl)))))
        (add_anns ⎣⎦ (cardinal Sp' + cardinal (getL sl))
                  (do_spill_rm slot (setTopAnn sl (∅, ∅, getRm sl)))))
     ⊆ R ∪ map slot (Sp' ∪ M) ∪ G) as H by (apply H ; eauto).

  intros Sp' Sp'_sub L_sub'.

  remember (elements Sp') as elSp.
  remember (elements (getL  sl)) as elL.
  do 2 rewrite <- elements_length.
  rewrite <- HeqelL.
  rewrite <- HeqelSp.
  assert (Sp' ⊆ of_list elSp) as Sp_sub''
    by (rewrite HeqelSp; rewrite of_list_elements; reflexivity).
  clear HeqelSp.
  revert G.
  induction elSp;
    intros G;
    simpl in *.

  - rewrite add_anns_S.
    simpl.
    rewrite IHelSp; eauto.
    + enough (singleton a ⊆ R) as in_R
          by (rewrite in_R; clear; cset_tac).
      rewrite <- Sp_sub.
      rewrite <- H.
      clear; cset_tac.
    + rewrite <- H.
      clear; cset_tac.
Qed.

(*

Corollary reconstr_live_small_s'
      (sl : ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄))))
      ZL G
      slot s Λ R M
  :
    let Sp := fst (fst (getAnn sl )) in
    let L  := snd (fst (getAnn sl )) in
    Sp ⊆ R
    -> L ⊆ Sp ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G'
           (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))))
           (discard_merge_sl slot (do_spill_rm' slot 0 sl)))
        ⊆ (R ∪ L) ∪ map slot (Sp ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl)
           (discard_merge_sl slot (do_spill_rm' slot (count sl) sl)))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros Sp L sp_sub l_sub.
  assert (R [=] R ∪ L \ L).
  { clear. cset_tac. }
  assert (M [=] Sp \ Sp ∪ M).
  { clear. cset_tac. }
  rewrite H.
  rewrite H0.
  apply reconstr_live_small_s;
    subst Sp; subst L;
      [ apply sub_spill_refl | | ];
      eauto.
Qed.
*)

Lemma reconstr_live_small
      ZL Λ Lv s G k R M sl slot al (F : list(params * stmt))
  :
    PIR2 Equal Lv (merge Λ)
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> some_reconstr_live sl al
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ (snd ⊝ Λ) ZL)
            G
           (do_spill slot s sl)
           (do_spill_rm slot sl)))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros pir2 lvSnd spSnd ssl.
  general induction lvSnd;
    invc spSnd;
    invc ssl;
    apply reconstr_live_small_s';
    try apply sub_spill_refl;
    simpl in *; eauto; intros G';
      rewrite empty_cardinal;
      simpl.
  - rewrite IHlvSnd with (R:={x; (R \ K ∪ L) \ Kx})
                         (M:=Sp ∪ M); eauto.
    rewrite H13.
    rewrite SetOperations.map_app; eauto.
    clear.
    cset_tac.
  - rewrite IHlvSnd1 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M); eauto.
    rewrite IHlvSnd2 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M); eauto.
    rewrite H11.
    rewrite SetOperations.map_app; eauto.
    clear.
    cset_tac.
  - repeat apply union_incl_split.
    + admit. (* TODO talk about Op.freeVars ⊝ Y *)
    + eapply get_nth with (d:=(∅,∅)) in H14 as H14'.
      assert (nth l (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f).
      {
        assert ((fun RM => fst RM ∪ map slot (snd RM)) (nth l Λ (∅,∅))
                = (fun RM => fst RM ∪ map slot (snd RM)) (R_f,M_f)) as H_sms.
        { f_equal; simpl; [ | f_equal];
          rewrite H14'; simpl; eauto. }
        unfold slot_merge.
        rewrite <- map_nth in H_sms.
        simpl in H_sms.
        assert (l < length ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∪ map slot (snd RM)) ⊝ Λ)) as l_len.
        { apply get_length in H14. clear - H14. eauto with len. }
        assert (nth l ((fun RM : ⦃var⦄ * ⦃var⦄ => fst RM ∪ map slot (snd RM)) ⊝ Λ) ∅
                = R_f ∪ map slot M_f) as H_sms'.
        { rewrite nth_indep with (d':=∅ ∪ map slot ∅). exact H_sms. eauto with len. }
        rewrite H_sms'.
        reflexivity.
      }
      rewrite H4.
      assert (of_list (nth l (slot_lift_params slot ⊜ ZL Λ) nil)
                      [=] of_list (slot_lift_params slot Z0 (R_f,M_f))).
      {
        erewrite nth_zip; eauto.
        reflexivity.
      }
      rewrite H5.
      rewrite SetOperations.map_app; eauto.
      clear - H16 H17.
      apply map_slot_incl with (slot:=slot) in H17.
      rewrite map_slot_minus in H17.
      assert ((R_f ∪ map slot M_f) \ of_list (slot_lift_params slot Z0 (R_f,M_f))
                 ⊆ R_f \ of_list Z0 ∪ map slot M_f \ map slot (of_list Z0)).
      { clear.
        unfold slot_lift_params.
        rewrite of_list_elements.
        rewrite map_slot_cut.
        simpl.
        cset_tac. }
      rewrite H.
      rewrite H16.
      rewrite H17.
      rewrite SetOperations.map_app; eauto.
      clear.
      cset_tac.
    + clear. cset_tac.
  - rewrite H7.
    cset_tac.
  - rewrite fst_F; eauto.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    rewrite IHlvSnd with (R:=R \ K ∪ L) (M:=Sp ∪ M); eauto.
    + clear. cset_tac.
    + unfold merge.
      unfold merge in H7.
      rewrite <- H7.
      rewrite map_app.
      apply PIR2_app.
      * apply PIR2_refl; eauto.
      * unfold merge in pir2.
        eauto.

Admitted.
