Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.
Require Import SpillSound DoSpill DoSpillRm SpillUtil ReconstrLive AnnP InVD SetUtil.
Require Import ReconstrLiveUtil ReconstrLiveG.
Require Import ToBeOutsourced.

Set Implicit Arguments.

(** * ReconstrLiveSmall *)

Lemma reconstr_live_write_loads
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (slot : var -> var)
      (xs : params)
      (s : stmt)
      (an : lvness_fragment)
      (VD G : ⦃var⦄)
  :
    of_list xs ⊆ VD
    -> disj VD (map slot VD)
    -> getAnn (
          reconstr_live Lv ZL G
                        (write_moves xs (slot ⊝ xs) s)
                        (add_anns ⎣⎦ (length xs) an))
             [=]
             getAnn (reconstr_live Lv ZL ∅ s an)
             \ of_list xs ∪ map slot (of_list xs) ∪ G
.
Proof.
  intros xs_VD disj_VD.
  general induction xs;
    simpl in *; eauto.
  - rewrite add_anns_zero, reconstr_live_G_eq.
    rewrite lookup_set_empty; eauto.
    clear; cset_tac.
  - rewrite add_anns_S; simpl.
    rewrite lookup_set_add; eauto.
    unfold lookup_set.
    rewrite reconstr_live_G_eq.
    rewrite add_union_singleton in xs_VD.
    apply union_incl_split2 in xs_VD as [a_VD xs_VD].
    rewrite IHxs; eauto.
    apply incl_eq.
    + setoid_rewrite add_union_singleton at 2.
      repeat apply union_incl_split.
      * clear; cset_tac.
      * clear; cset_tac.
      * assert (forall (s t u v w r : ⦃var⦄),
                   t \ v ⊆ (s ∪ t ∪ u ∪ v) \ v ∪ w ∪ r)
          as setsub by (clear; cset_tac).
        rewrite <- setsub.
        rewrite disj_minus_eq; eauto.
        apply disj_sym.
        eapply disj_incl; eauto with cset.
      * clear; cset_tac.
    + clear; cset_tac.
Qed.



(* this will be generalized by reconstr_live_write_loads *)
Lemma reconstr_live_small_L
      (sl : spilling)
      (ZL : list (params))
      (R M G VD : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> M ⊆ VD
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl) ZL Λ)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s (clear_Sp sl) ZL Λ)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G
.
Proof.
  intros disj_VD R_VD M_VD Sp_R L_SpM base.

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

  rewrite reconstr_live_write_loads; eauto;
    [ | rewrite of_list_elements, L_SpM, Sp_R, R_VD, M_VD;
        clear; cset_tac].
  rewrite base.
  rewrite lookup_set_union; eauto.
  rewrite of_list_elements.
  setoid_rewrite lookup_set_incl at 3; eauto.
  rewrite lookup_set_union; eauto.
  clear; cset_tac.
Qed.



(* maybe I will need a lemma :
  x ∈  s
  ->   reconstr_live Lv ZL ∅ s an \ s
   [=] reconstr_live Lv ZL (singleton x) s an \ s
 *)

Lemma reconstr_live_write_spills
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (slot : var -> var)
      (xs: params)
      (s : stmt)
      (an : lvness_fragment)
      (VD G : ⦃var⦄)
   :
    disj VD (map slot VD)
    -> of_list xs ⊆ VD
    -> getAnn (
          reconstr_live Lv ZL G
                        (write_moves (slot ⊝ xs) xs s)
                        (add_anns ⎣⎦ (length xs) an))
             [=] getAnn (
               reconstr_live Lv ZL ∅ s an)
             \ map slot (of_list xs)
             ∪ of_list xs
             ∪ G
.
Proof.
  intros disj_VD xs_VD.
  general induction xs;
    simpl in *; eauto.
  - rewrite reconstr_live_G_eq.
    rewrite add_anns_zero.
    rewrite lookup_set_empty; eauto.
    clear; cset_tac.
  - rewrite add_anns_S; simpl.
    rewrite add_union_singleton in xs_VD.
    apply union_incl_split2 in xs_VD as [a_VD xs_VD].
    rewrite IHxs; eauto.
    rewrite lookup_set_add; eauto.
    unfold lookup_set.
    apply incl_eq.
    + setoid_rewrite add_union_singleton at 2.
      repeat apply union_incl_split.
      * clear; cset_tac.
      * clear; cset_tac.
      * assert (forall (s t u v w : ⦃var⦄),
                   t \ u ⊆ (s ∪ t ∪ u) \ u ∪ v ∪ w)
          as setsub by (clear; cset_tac).
        rewrite <- setsub.
        rewrite disj_minus_eq; eauto.
        eapply disj_incl; eauto.
        rewrite <- map_singleton; eauto.
        eauto with cset.
      * clear; cset_tac.
    + clear; cset_tac.
Qed.








(* this will be generalized by reconstr_live_write_spills *)
Lemma reconstr_live_small_Sp
      (sl : spilling)
      (ZL : list (params))
      (R M G VD : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> getSp sl ⊆ R
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_Sp sl) ZL Λ)
           (do_spill_rm slot (clear_Sp sl)))
        ⊆ R ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl  ZL Λ)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros disj_VD R_VD Sp_R base.

  rewrite do_spill_extract_spill_writes.
  rewrite do_spill_rm_s_Sp.

  rewrite <- elements_length.
  rewrite reconstr_live_write_spills; eauto;
    [ | rewrite of_list_elements, Sp_R; eauto ].
  rewrite base.
  rewrite of_list_elements.
  rewrite lookup_set_union; eauto.
  unfold lookup_set.
  setoid_rewrite Sp_R at 3.
  clear; cset_tac.
Qed.


(* proof has to be redone with new lemmata *)
Lemma reconstr_live_small_s
      (sl : spilling)
      (ZL : list (params))
      (R M G VD : ⦃var⦄)
      (slot : var -> var)
      (s : stmt)
      (Λ : list (⦃var⦄ * ⦃var⦄))
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> M ⊆ VD
    -> getSp sl ⊆ R
    -> getL sl ⊆ getSp sl ∪ M
    -> (forall G', getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G'
           (do_spill slot s (clear_SpL sl)  ZL Λ)
           (do_spill_rm slot (clear_SpL sl)))
        ⊆ R ∪ getL sl ∪ map slot (getSp sl ∪ M) ∪ G')
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
           (do_spill slot s sl ZL Λ)
           (do_spill_rm slot sl))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros disj_VD R_VD M_VD Sp_R L_SpM base.
  eapply reconstr_live_small_Sp; eauto.
  intros G''.
  eapply reconstr_live_small_L; eauto.
Qed.







Lemma reconstr_live_small o
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
  : R ⊆ VD
    -> M ⊆ VD
    -> union_fs (getAnn ra) ⊆ VD
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> renamedApart s ra
    -> PIR2 Equal (merge ⊝ Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> app_expfree s
    -> live_sound o ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl al
    -> getAnn
        (reconstr_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ Λ ZL)
            G
            (do_spill slot s sl ZL Λ)
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
    clear - R_VD ; cset_tac'.
  }
  general induction lvSnd;
    inv rena;
    invc aeFree;
    invc spillSnd;
    invc spilli;
    apply reconstr_live_small_s with (VD:=VD);
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
    + rewrite H18.
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
      rewrite lifted_args_in_RL_slot_SpM; eauto. reflexivity.
    + rewrite nth_rfmf; eauto.
      erewrite nth_zip; eauto.
      exploit Z_VD as Z_VD'; eauto.
      assert (R_f ⊆ VD) as Rf_VD
          by (eapply Rf_VD with (R:=R) (M:=M) (L:=L); eauto).
      assert (M_f ⊆ VD) as Mf_VD
          by (eapply Mf_VD with (R:=R) (M:=M); eauto).
      erewrite slp_union_minus_incl with (VD:=VD); eauto.
      rewrite H16.
      rewrite <- lookup_set_minus_eq; eauto; swap 1 2.
      {
        eapply injective_on_incl with (D:=VD); eauto.
        rewrite Z_VD', Mf_VD.
        clear; cset_tac.
      }
      rewrite lookup_set_incl; eauto.
      unfold lookup_set.
      clear; cset_tac.
    + clear; cset_tac.
  - rewrite H9.
    clear; cset_tac.
  - rewrite fst_zip_pair; eauto with len.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app; eauto with len.
    apply union_incl_split.
    assert (R \ K ∪ L ⊆ VD) as R'_VD
        by (eapply R'_VD with (R:=R) (M:=M); eauto).
    assert (Sp ∪ M ⊆ VD) as M'_VD
        by (eapply M'_VD with (R:=R) (M:=M); eauto).
    + apply renamedApart_incl in rena as [renaF rena2].
      rewrite IHlvSnd with (R:=R\K ∪ L)
                           (M:=Sp ∪ M)
                           (ra:=ant)
                           (VD:=VD); eauto with len.
      * clear; cset_tac.
      * rewrite rena2.
        clear - ra_VD; cset_tac.
      * apply getAnn_als_EQ_merge_rms; eauto.
      * clear - ra_VD H6 H8 H13 Z_VD.
        eapply get_ofl_VD; eauto.
      * eapply injective_on_incl with (D:=VD); eauto.
        rewrite Sp_sub_R; [| eauto].
        rewrite R'_VD.
        reflexivity.
    + clear; cset_tac.
Qed.
