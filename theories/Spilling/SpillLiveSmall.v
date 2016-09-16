Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill DoSpillRm DiscardMergeSl SpillUtil SpillLive.

Set Implicit Arguments.


Lemma spill_live_remove_G
      Lv ZL G s sl G'
  :
    getAnn (spill_live Lv ZL G s sl) \ G
           ⊆ getAnn (spill_live Lv ZL G' s sl)
.
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.




Lemma spill_live_small_s
      (sl sl' : ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄))))
      ZL G
      slot s Λ R M
  :
    let Sp := fst (fst (getAnn sl )) in
    let L  := snd (fst (getAnn sl )) in
    let Sp':= fst (fst (getAnn sl')) in
    let L' := snd (fst (getAnn sl')) in
    sub_spill sl' sl
    -> Sp ⊆ R
    -> L  ⊆ Sp ∪ M
    -> (forall G', getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G'
           (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))))
           (discard_merge_sl slot (do_spill_rm' slot 0 sl)))
        ⊆ (R ∪ L) ∪ map slot (Sp ∪ M) ∪ G')
    -> getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl')
           (discard_merge_sl slot (do_spill_rm' slot (count sl') sl)))
        ⊆ (R ∪ L \ L') ∪ map slot (Sp \ Sp' ∪ M) ∪ G
.
Proof.
  intros Sp L Sp' L' sub spr lspm sls.

  remember (cardinal Sp') as card_Sp'.
  general induction card_Sp'.
  - remember (cardinal L') as card_L'.
    general induction card_L'.
    + assert (((R ∪ L ∪ map slot (Sp ∪ M) ∪ G) \ (L ∩ L')) \ (map slot (Sp ∩ Sp'))
                                                       ∪ R ∪ map slot M ∪ G
          ⊆ R ∪ L \ L' ∪ map slot (Sp \ Sp' ∪ M) ∪ G) as set_EQ.
      {
        repeat rewrite SetOperations.map_app; eauto.
        rewrite map_slot_cut; eauto.
        rewrite map_slot_minus; eauto.
        clear. cset_tac.
      }
      rewrite <- set_EQ.
      rewrite <- sls.
      assert (count sl' = 0) as count_zero.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite count_zero.
      enough (do_spill slot s sl'
              = do_spill slot s (setTopAnn sl (∅,∅, snd (getAnn sl))))
        as do_spill_eq.
      {
        rewrite do_spill_eq.
        symmetry in Heqcard_Sp'.
        apply cardinal_Empty in Heqcard_Sp'.
        apply empty_inter_2 with (s0:=Sp) in Heqcard_Sp'.
        apply empty_is_empty_1 in Heqcard_Sp'.
        rewrite Heqcard_Sp'.
        symmetry in Heqcard_L'.
        apply cardinal_Empty in Heqcard_L'.
        apply empty_is_empty_1 in Heqcard_L'.
        rewrite Heqcard_L'.
        rewrite SetOperations.map_empty; eauto.
        clear. cset_tac.
      }
      erewrite do_spill_empty_invariant
      with (Sp':=∅) (L':=∅) ;
        try apply cardinal_Empty;
        try apply empty_1;
        eauto.
      unfold sub_spill in sub.
      destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite top_sl'.
      rewrite getAnn_setTopAnn.
      rewrite setTopAnn_setTopAnn.
      rewrite eq_rm.
      reflexivity.
    + assert (count sl' = S card_L') as count_sl'.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite do_spill_L;
        [ | apply cardinal_Empty;
            subst Sp'
          | intro N ;
            apply cardinal_Empty in N ;
            subst L';
            omega ];
        eauto.
      rewrite count_sl'.
      rewrite do_spill_rm_s.
      rewrite discard_merge_sl_step.
      simpl.
      assert (count (setTopAnn sl'
                               (fst (fst (getAnn sl')),
                                of_list (tl (elements (snd (fst (getAnn sl'))))),
               snd (getAnn sl'))) = card_L') as count_L'.
      { eapply count_reduce_L; eauto. }
      rewrite <- count_L'.
      assert (Sp' [=] ∅) as Sp'_empty.
      {
        clear - Heqcard_Sp'.
        apply empty_is_empty_1.
        apply cardinal_Empty.
        eauto.
      }
      apply union_incl_split; [ apply union_incl_split | ].
      * assert (forall s t u : set var, s ⊆ t ∪ u -> s \ u ⊆ t) as set_eq.
        { clear. cset_tac.
          hnf in H.
          exploit H; eauto.
          apply union_iff in H0.
          destruct H0; eauto. contradiction.
        }
        assert (forall s t : set var, s \ t [=] s \ t \ t) as set_eq2.
        { clear. cset_tac. }
        rewrite set_eq2.
        apply set_eq.
        rewrite spill_live_remove_G with (G':=G).
        set (sl'' := setTopAnn _ _).
        let reset :=
            (subst L; subst L'; subst Sp; subst Sp';
             set (Sp := fst (fst (getAnn sl))) in *;
             set (L := snd (fst (getAnn sl))) in *;
             set (Sp' := fst (fst (getAnn sl'))) in *;
             set (L' := snd (fst (getAnn sl'))) in *) in
                 rewrite IHcard_L';
             simpl; eauto; reset.
        -- enough (L \ snd (fst (getAnn sl''))
                          ⊆ L \ L' ∪ singleton (hd 0 (elements L'))) as enog.
           {
            rewrite enog.
            subst sl''.
            rewrite getAnn_setTopAnn.
            simpl.
            clear.
            cset_tac.
          }
          subst sl''.
          rewrite getAnn_setTopAnn.
          simpl.
          rewrite tl_hd_set_incl.
          reflexivity.
        -- subst sl''.
           unfold sub_spill in *.
           destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
           repeat split.
           ** rewrite top_sl'.
              repeat rewrite getAnn_setTopAnn.
              rewrite setTopAnn_setTopAnn.
              reflexivity.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst Sp'.
              apply sub_Sp.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst L'.
              rewrite tl_set_incl.
              apply sub_L.
           ** rewrite getAnn_setTopAnn.
              simpl.
              apply eq_rm.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           eauto.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           symmetry.
           apply cardinal_set_tl.
           rewrite of_list_elements.
           eauto.
      * assert (hd 0 (elements (snd (fst (getAnn sl'))))
                    ∈ (snd (fst (getAnn sl')))) as hd_in.
        {
          apply hd_in_elements.
          intro N.
          subst L'.
          rewrite N in Heqcard_L'.
          rewrite empty_cardinal in Heqcard_L'.
          clear - Heqcard_L'. isabsurd.
        }
        apply incl_singleton in hd_in.
        rewrite map_slot_incl with (slot:=slot) in hd_in.
        assert (singleton (slot (hd 0 (elements (snd (fst (getAnn sl'))))))
                          ⊆ map slot (snd (fst (getAnn sl')))) as hd_in_set.
        { rewrite <- hd_in. clear. cset_tac. }
        rewrite hd_in_set.
        rewrite Sp'_empty.
        enough (map slot (snd (fst (getAnn sl'))) ⊆ map slot (Sp ∪ M)) as enog.
        { revert enog. clear.
          repeat rewrite SetOperations.map_app; eauto.
          rewrite map_slot_minus.
          intros.
          rewrite H.
          rewrite SetOperations.map_empty; eauto.
          apply union_incl_split; cset_tac.
        }
        apply map_slot_incl.
        unfold sub_spill in sub.
        destruct sub as [_ [_ [sub_L _]]].
        rewrite sub_L.
        subst L.
        eauto.
      * clear. cset_tac.
  - assert (count sl' = S card_Sp' + cardinal L') as count_sl'.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite do_spill_Sp;
        [ | intro N ;
            apply cardinal_Empty in N ;
            subst Sp';
            omega ];
        eauto.
      rewrite count_sl'.
      simpl.
      rewrite do_spill_rm_s.
      rewrite discard_merge_sl_step.
      simpl.
      assert (count (setTopAnn sl'
                               (of_list (tl (elements (fst (fst (getAnn sl'))))),
                                snd (fst (getAnn sl')),
               snd (getAnn sl'))) = card_Sp' + cardinal L') as count_Sp'.
      { eapply count_reduce_Sp; eauto. }
      rewrite <- count_Sp'.
      apply union_incl_split; [ apply union_incl_split | ].
      * assert (forall s t u : set var, s ⊆ t ∪ u -> s \ u ⊆ t) as set_eq.
        { clear. cset_tac.
          hnf in H.
          exploit H; eauto.
          apply union_iff in H0.
          destruct H0; eauto. contradiction.
        }
        assert (forall s t : set var, s \ t [=] s \ t \ t) as set_eq2.
        { clear. cset_tac. }
        rewrite set_eq2.
        apply set_eq.
        rewrite spill_live_remove_G with (G':=G).
        set (sl'' := setTopAnn _ _).
        let reset :=
            (subst L; subst L'; subst Sp; subst Sp';
             set (Sp := fst (fst (getAnn sl))) in *;
             set (L := snd (fst (getAnn sl))) in *;
             set (Sp' := fst (fst (getAnn sl'))) in *;
             set (L' := snd (fst (getAnn sl'))) in *) in
                 rewrite IHcard_Sp';
             simpl; eauto; reset.
        -- enough (Sp \ fst (fst (getAnn sl''))
                          ⊆ Sp \ Sp' ∪ singleton ((hd 0 (elements Sp')))) as enog.
           {
            rewrite enog.
            subst sl''.
            rewrite getAnn_setTopAnn.
            simpl.
            clear.
            repeat rewrite SetOperations.map_app; eauto.
            rewrite map_singleton.
            cset_tac.
          }
          subst sl''.
          rewrite getAnn_setTopAnn.
          simpl.
          rewrite tl_hd_set_incl.
          reflexivity.
        -- subst sl''.
           unfold sub_spill in *.
           destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
           repeat split.
           ** rewrite top_sl'.
              repeat rewrite getAnn_setTopAnn.
              rewrite setTopAnn_setTopAnn.
              reflexivity.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst Sp'.
              rewrite tl_set_incl.
              apply sub_Sp.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst L'.
              apply sub_L.
           ** rewrite getAnn_setTopAnn.
              simpl.
              apply eq_rm.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           symmetry.
           apply cardinal_set_tl.
           rewrite of_list_elements.
           eauto.
      * assert (hd 0 (elements (fst (fst (getAnn sl'))))
                    ∈ (fst (fst (getAnn sl')))) as hd_in.
        {
          apply hd_in_elements.
          intro N.
          subst Sp'.
          rewrite N in Heqcard_Sp'.
          rewrite empty_cardinal in Heqcard_Sp'.
          clear - Heqcard_Sp'. isabsurd.
        }
        apply incl_singleton in hd_in.
        subst Sp Sp' L L'.
        rewrite <- spr.
        unfold sub_spill in sub.
        destruct sub as [_ [sub_Sp' _]].
        rewrite <- sub_Sp'.
        rewrite hd_in.
        clear.
        cset_tac.
      * clear. cset_tac.
Qed.



Corollary spill_live_small_s'
      (sl : ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄))))
      ZL G
      slot s Λ R M
  :
    let Sp := fst (fst (getAnn sl )) in
    let L  := snd (fst (getAnn sl )) in
    Sp ⊆ R
    -> L ⊆ Sp ∪ M
    -> (forall G', getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G'
           (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))))
           (discard_merge_sl slot (do_spill_rm' slot 0 sl)))
        ⊆ (R ∪ L) ∪ map slot (Sp ∪ M) ∪ G')
    -> getAnn
        (spill_live
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
  apply spill_live_small_s;
    subst Sp; subst L;
      [ apply sub_spill_refl | | ];
      eauto.
Qed.


Lemma spill_live_small
      ZL Λ Lv s G k R M sl slot al (F : list(params * stmt))
  :
    PIR2 Equal Lv (merge Λ)
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> some_spill_live sl al
    -> getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl)
           (discard_merge_sl slot (do_spill_rm slot sl)))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros pir2 lvSnd spSnd ssl.
  general induction lvSnd;
    invc spSnd;
    invc ssl;
    apply spill_live_small_s';
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
      admit.
    + clear. cset_tac.
  - rewrite H7.
    cset_tac.
  - admit.

Admitted.
