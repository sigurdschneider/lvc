Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm SpillUtil ReconstrLive AnnP InVD SetUtil.
Require Import ReconstrLiveUtil.
Require Import ToBeOutsourced.

Set Implicit Arguments.




(* remove this  *)
Lemma reconstr_live_small_L'
      (sl : spilling)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (slot : var -> var)
      (ys : list var)
      (R M R' G : ⦃var⦄)
      (IB : list (list bool))
  :
    getL sl ⊆ getSp sl ∪ M
    -> of_list ys ⊆ getL sl
    -> R' [=] R ∪ getL sl \ of_list ys
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ Λ ZL) G'
                (do_spill slot s (clear_SpL sl) IB)
                (do_spill_rm slot (clear_SpL sl))
             )
             ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G'
       )
    -> getAnn
         (reconstr_live
            (slot_merge slot Λ)
            (slot_lift_params slot ⊜ Λ ZL) G
            (write_loads slot ys
                         (do_spill slot s (clear_SpL sl) IB)
            )
            (add_anns ⎣⎦ (length ys)
                      (do_spill_rm slot (clear_SpL sl))
            )
         )
            ⊆ R' ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
intros L_SpM ys_L RR base.
  rewrite RR.
  general induction ys;
    simpl; eauto.
  - rewrite add_anns_zero.
    rewrite base.
    clear; cset_tac.
  - rewrite add_anns_S.
    simpl.
    rewrite IHys; eauto.
    + enough (singleton (slot a) ⊆ map slot (getSp sl ∪ M))
        as a_in_SpM
          by (rewrite a_in_SpM; clear; cset_tac).
      rewrite <- map_singleton.
      apply lookup_set_morphism.
      rewrite <- L_SpM.
      rewrite <- ys_L.
      clear; eauto with cset.
    + rewrite <- ys_L.
      clear; eauto with cset.
    + eauto with cset.
Qed.

(* this will be generalized by reconstr_live_write_loads *)
Lemma reconstr_live_small_L
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl) IB)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s (clear_Sp sl) IB)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
  intros L_sub base.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  rewrite count_clearSp.
  rewrite getSp_clearSp.
  rewrite getL_clearSp.
  unfold clear_Sp.
  rewrite getAnn_setTopAnn.
  rewrite setTopAnn_setTopAnn.
  rewrite elements_empty.
  simpl.
  rewrite <- elements_length.
  eapply reconstr_live_small_L'; eauto.
  - rewrite of_list_elements.
    reflexivity.
  - rewrite of_list_elements.
    clear; cset_tac.
Qed.


(* remove this *)
Lemma reconstr_live_small_Sp'
      (sl : spilling)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (s : stmt)
      (slot : var -> var)
      (xs : list var)
      (R M M' G : ⦃var⦄)
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> of_list xs ⊆ getSp sl
    -> M' [=] getSp sl \ of_list xs ∪ M
    -> (forall G' : ⦃var⦄,
           getAnn
             (reconstr_live
                (slot_merge slot Λ)
                (slot_lift_params slot ⊜ Λ ZL) G'
                (write_loads slot (elements (getL sl))
                             (do_spill slot s (clear_SpL sl) IB)
                )
                (add_anns ⎣⎦ (cardinal (getL sl))
                          (do_spill_rm slot (clear_SpL sl))
                )
             )
             ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G'
       )
    -> getAnn
         (reconstr_live
            (slot_merge slot Λ)
            (slot_lift_params slot ⊜ Λ ZL) G
            (write_spills slot xs
                          (write_loads slot (elements (getL sl))
                                       (do_spill slot s (clear_SpL sl) IB)
                          )
            )
            (add_anns ⎣⎦ (length xs + cardinal (getL sl))
                      (do_spill_rm slot (clear_SpL sl))
            )
         )
            ⊆ R ∪ map slot M' ∪ G
.
Proof.
  intros inj_slot Sp_R xs_Sp MM base.
  rewrite MM.
  general induction xs;
    simpl; eauto.
  - rewrite SetOperations.map_app; eauto.
    assert (getSp sl \ ∅ [=] getSp sl)
      as minus_empty by (clear; cset_tac).
    rewrite minus_empty.
    rewrite <- SetOperations.map_app; eauto.
  - rewrite add_anns_S.
    simpl.
    rewrite IHxs; eauto.
    + rewrite -> !SetOperations.map_app; eauto.
      rewrite -> !lookup_set_minus_eq; eauto.
      rewrite lookup_set_add; eauto.
      * enough (singleton a ⊆ R)
          as a_in_R
            by (rewrite a_in_R; clear; cset_tac).
        rewrite <- Sp_R.
        rewrite <- xs_Sp.
        clear; eauto with cset.
      * eapply injective_on_incl; eauto.
        apply union_incl_split.
        -- reflexivity.
        -- rewrite <- xs_Sp.
           clear; eauto with cset.
      * eapply injective_on_incl; eauto.
        apply union_incl_split.
        -- reflexivity.
        -- rewrite <- xs_Sp.
           clear; eauto with cset.
    + rewrite <- xs_Sp.
      clear; eauto with cset.
    + eauto with cset.
Qed.






(*
Lemma reconstr_live_write_spills
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (slot : var -> var)
      (xs: params)
      (s : stmt)
      (an : lvness_fragment)
      (x : var)
      (VD G : ⦃var⦄)
   :
    disj VD (map slot VD)
    -> of_list xs ⊆ VD
    -> x ∈ VD
    -> getAnn ( (* there is still a problemif G ∩ of_list xs <> ∅ *)
          reconstr_live Lv ZL G
                        (write_spills slot (xs ++ x::nil) s)
                        (add_anns ⎣⎦ (length (xs ++ x::nil)) an))
             [=] getAnn (
               reconstr_live Lv ZL (singleton x) s an)
             \ map slot (of_list (xs ++ x::nil))
             ∪ of_list xs
             ∪ G
.
Proof.


*)



(* this will be generalized by reconstr_live_write_spills *)
Lemma reconstr_live_small_Sp
      (sl : spilling)
      (ZL : list (params))
      (R M G D : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_Sp sl) IB)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl IB)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros inj_slot Sp_R base.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  unfold count.
  rewrite <- elements_length.
  eapply reconstr_live_small_Sp' with (M:=M); eauto.
  - rewrite of_list_elements.
    reflexivity.
  - rewrite of_list_elements.
    clear; cset_tac.
  - rewrite do_spill_extract_writes in base.
    rewrite do_spill_rm_s in base.
    rewrite getSp_clearSp in base.
    rewrite getL_clearSp in base.
    rewrite elements_empty in base.
    rewrite count_clearSp in base.
    unfold clear_Sp in base.
    rewrite setTopAnn_setTopAnn in base.
    rewrite getAnn_setTopAnn in base.
    simpl in base.
    apply base.
Qed.



(* proof has to be redone with new lemmata *)
Lemma reconstr_live_small_s
      (sl : spilling)
      (ZL : list (params))
      (R M G : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (IB : list (list bool))
  :
    injective_on (getSp sl) slot
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl) IB)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl IB)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros slot_inj Sp_sub L_sub base.
  apply reconstr_live_small_Sp; eauto.
  intros G''.
  apply reconstr_live_small_L; eauto.
Qed.







Lemma reconstr_live_small
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Lv : list ⦃var⦄)
      (s : stmt)
      (G R M VD: ⦃var⦄)
      (k : nat)
      (sl : spilling)
      (slot : var -> var)
      (al : ann ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    R ⊆ VD
    -> M ⊆ VD
    -> union_fs (getAnn ra) ⊆ VD
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> renamedApart s ra
    -> PIR2 Equal (merge Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> app_expfree s
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl al
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
            (do_spill slot s sl (mark_elements ⊜ ZL ((fun RM => fst RM ∩ snd RM) ⊝ Λ)))
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros R_VD M_VD ra_VD inj_VD VD_disj rena pir2 Z_VD aeFree lvSnd spillSnd spilli.

  unfold union_fs in ra_VD.
  assert (injective_on (getSp sl) slot)
    as inj_Sp.
  {
    eapply injective_on_incl; eauto.
    rewrite Sp_sub_R; [ | eauto].
    clear - R_VD ; cset_tac.
  }
  general induction lvSnd;
    inv rena;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    apply reconstr_live_small_s;
    eauto;
      intros G'; simpl;
        rewrite elements_empty;
        unfold clear_SpL;
        unfold setTopAnn;
        unfold count;
        simpl;
        rewrite empty_cardinal;
        simpl in *.
  - assert (x ∈ VD) as x_VD by (eapply x_VD; eauto).
    assert ({x; (R \ K ∪ L) \ Kx} ⊆ VD) as Rx_VD
        by (eapply Rx_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    erewrite IHlvSnd with (R:={x; (R \K ∪ L) \Kx})
                          (M:=Sp ∪ M)
                          (ra:=an)
                          (VD:=VD);
      eauto.
    + rewrite H19.
      clear; cset_tac.
    + apply renamedApart_incl in rena.
      rewrite rena.
      eauto.
    + eapply injective_on_incl with (D:=VD) ; eauto.
      rewrite Sp_sub_R; [ | eauto].
      rewrite Rx_VD.
      reflexivity.
  - assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    apply renamedApart_incl in rena as [rena1 rena2].
    rewrite IHlvSnd1 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M)
                          (ra:=ans)
                          (VD:=VD);
      eauto.
    + rewrite IHlvSnd2 with (R:=R \ K ∪ L)
                            (M:=Sp ∪ M)
                            (ra:=ant)
                            (VD:=VD);
        eauto.
      * rewrite H20.
        clear; cset_tac.
      * rewrite rena2. eauto.
      * eapply injective_on_incl with (D:=VD); eauto.
        rewrite Sp_sub_R; [| eauto].
        rewrite R'_VD.
        reflexivity.
    + rewrite rena1. eauto.
    + eapply injective_on_incl with (D:=VD); eauto.
      rewrite Sp_sub_R; [| eauto].
      rewrite R'_VD.
      reflexivity.
  - repeat apply union_incl_split.
    + apply incl_union_left.
      rewrite <- sla_list_union_EQ_extended_args.
      eapply lifted_args_in_RL_slot_SpM; eauto.
    + rewrite nth_rfmf; eauto.
      erewrite nth_zip; eauto.
      exploit Z_VD as Z_VD'; eauto.
      assert (R_f ⊆ VD) as Rf_VD
          by (eapply Rf_VD with (R:=R) (M:=M) (L:=L); eauto).
      assert (M_f ⊆ VD) as Mf_VD
          by (eapply Mf_VD with (R:=R) (M:=M); eauto).
      erewrite slp_union_minus_incl with (VD:=VD); eauto.
      rewrite H18.
      rewrite <- lookup_set_minus_eq; eauto; swap 1 2.
      {
        eapply injective_on_incl with (D:=VD); eauto.
        rewrite Z_VD', Mf_VD.
        clear; cset_tac.
      }
      rewrite lookup_set_incl; eauto.
      clear; cset_tac.
    + clear; cset_tac.
  - rewrite H9.
    clear; cset_tac.
  - rewrite fst_zip_pair; eauto with len.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    rewrite <- zip_app; eauto with len.
    apply union_incl_split.
    assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    + apply renamedApart_incl in rena as [renaF rena2].
      rewrite <- map_app.
      rewrite IHlvSnd with (R:=R\K ∪ L)
                           (M:=Sp ∪ M)
                           (ra:=ant)
                           (VD:=VD); eauto with len.
      * clear; cset_tac.
      * rewrite rena2.
        clear - ra_VD; cset_tac.
      * rewrite merge_app.
        apply getAnn_als_EQ_merge_rms; eauto.
      * clear - ra_VD H6 H8 H13 Z_VD.
        eapply get_ofl_VD; eauto.
      * eapply injective_on_incl with (D:=VD); eauto.
        rewrite Sp_sub_R; [| eauto].
        rewrite R'_VD.
        reflexivity.
    + clear; cset_tac.
Qed.
