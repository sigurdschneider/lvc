Require Import CSet IL Annotation RenamedApart PairwiseDisjoint RenamedApartAnn.

Inductive renamedApartGood : stmt -> Prop :=
  | renamedApartGoodExp x e s
    : x ∉ definedVars s
      -> disj (freeVars s) (definedVars s)
      -> renamedApartGood s
      -> renamedApartGood (stmtLet x e s)
  | renamedApartGoodIf e s t
    : disj (Op.freeVars e ∪ freeVars s ∪ freeVars t) (definedVars s ∪ definedVars t)
      -> disj (definedVars s) (definedVars t)
      -> renamedApartGood s
      -> renamedApartGood t
      -> renamedApartGood (stmtIf e s t)
  | renamedApartGoodRet e
    : renamedApartGood (stmtReturn e)
  | renamedApartGoodGoto f Y
    : renamedApartGood (stmtApp f Y)
  | renamedApartGoodLet F t
    : (forall n Zs, get F n Zs -> renamedApartGood (snd Zs))
      -> pairwise_ne disj ((defVarsZs definedVars) ⊝ F)
      -> disj (definedVars t) (list_union ((defVarsZs definedVars) ⊝ F))
      -> disj (list_union (List.map (fun f => (freeVars (snd f) ∪ of_list (fst f))) F)
                         ∪ freeVars t)
             (list_union (definedVars ⊝ snd ⊝ F))
      -> (forall n Zs, get F n Zs -> NoDupA eq (fst Zs))
      -> renamedApartGood t
      -> renamedApartGood (stmtFun F t).

Lemma defVars_ra_defVarsZs F ans (Len:❬F❭=❬ans❭)
  (RA:forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
      get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
  : list_union (defVars ⊜ F ans) [=] list_union (defVarsZs definedVars ⊝ F).
Proof.
  general induction Len; simpl; eauto; norm_lunion.
  rewrite IHLen; eauto using get.
  unfold defVars at 1.
  unfold defVarsZs at 2.
  rewrite !renamedApart_occurVars; eauto using get.
  reflexivity.
Qed.

Lemma pw_defVars_defVarsZs F ans (Len:❬F❭ = ❬ans❭)
      (RA: forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
          get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (PW:  pairwise_ne disj (defVars ⊜ F ans))
  :  pairwise_ne disj (defVarsZs definedVars ⊝ F).
Proof.
  hnf; intros. inv_get.
  exploit PW; eauto using zip_get. unfold defVars, defVarsZs in *.
  simpl in*.
  rewrite !renamedApart_occurVars; eauto.
Qed.

Lemma disj_definedVars_t F ans (Len:❬F❭ = ❬ans❭) D Dt ant t
  (RA: forall (n : nat) (Zs : params * stmt) (a : ann (⦃nat⦄ * ⦃nat⦄)),
      get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
  (IW:Indexwise.indexwise_R (funConstr D Dt) F ans)
  (RAt:renamedApart t ant)
  (PE: pe (getAnn ant) (D, Dt))
  : disj (definedVars t) (list_union (defVarsZs definedVars ⊝ F)).
Proof.
  eapply renamedApart_occurVars in RAt; eauto.
  pe_rewrite. rewrite RAt.
  rewrite <- defVars_ra_defVarsZs; eauto.
  rewrite list_union_defVars_decomp; eauto.
  eapply disj_union_right.
  * symmetry. eapply funConstr_disj_Dt; eauto.
  * eapply disj_1_incl.
    eapply disj_Dt_getAnn; eauto. eauto.
Qed.

Lemma renamedApart_renamedApartGood s ra
  : renamedApart s ra -> renamedApartGood s.
Proof.
  intros RA.
  general induction RA; simpl.
  - exploit renamedApart_occurVars; eauto.
    exploit renamedApart_freeVars; eauto.
    exploit renamedApart_disj; eauto.
    pe_rewrite. set_simpl.
    econstructor; eauto with cset.
  - exploit renamedApart_occurVars; eauto.
    exploit renamedApart_freeVars; eauto.
    exploit renamedApart_disj; eauto.
    exploit (@renamedApart_occurVars s); eauto.
    exploit (@renamedApart_freeVars s); eauto.
    exploit (@renamedApart_disj s); eauto.
    pe_rewrite. set_simpl.
    econstructor; eauto.
    + rewrite H, H5, H8.
      eapply disj_1_incl; eauto with cset.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    + intros. inv_get. edestruct H2; dcr; eauto.
    + eapply pw_defVars_defVarsZs; eauto.
    + eapply disj_definedVars_t; eauto.
    + eapply disj_union_left.
      hnf; intros.
      eapply list_union_get in H6 as [?|?]; dcr; eauto;[|exfalso; cset_tac].
      eapply list_union_get in H7 as [?|?]; dcr; eauto;[|exfalso; cset_tac].
      inv_get.
      decide (x2 = x0).
      * subst. inv_get. exploit (@renamedApart_disj (snd x4)) as DISJ; eauto.
        assert (disj (definedVars (snd x4)) (of_list (fst x4))). {
          edestruct H2; eauto; dcr.
          rewrite <- renamedApart_occurVars in *; eauto.
          rewrite H6 in *. symmetry. eapply disj_1_incl; eauto.
        }
        rewrite <- renamedApart_occurVars in DISJ; eauto.
        rewrite <- renamedApart_freeVars in DISJ; eauto.
        revert DISJ H6 H8 H9. clear_all. cset_tac.
      * edestruct H2; try eapply H10; eauto; dcr.
        edestruct H2; try eapply H11; eauto; dcr.
        rewrite renamedApart_freeVars in *; eauto.
        rewrite renamedApart_occurVars in *; eauto.
        exploit (@renamedApart_disj (snd x4)); eauto.
        exploit (@renamedApart_disj (snd x1)); eauto.
        exploit H3. eapply n. eauto using zip_get. eauto using zip_get.
        unfold defVars in H22.
        rewrite H12 in *. rewrite H13 in *.
        revert H8 H9 H15 H19 H22. clear_all. cset_tac.
      * rewrite renamedApart_freeVars in *; eauto. pe_rewrite.
        hnf; intros.
        eapply list_union_get in H6 as [?|?]; dcr; eauto;[|exfalso; cset_tac].
        inv_get. edestruct H2; eauto; dcr.
        rewrite renamedApart_occurVars in *; eauto.
        exploit H0; eauto. eapply renamedApart_disj in H11.
        rewrite H10 in *.
        revert H15 H8 H7 H11 H14. clear_all. cset_tac.
    + intros. inv_get. edestruct H2; eauto.
Qed.

Lemma renamedApartGood_renamedApart s G
      (RAG:renamedApartGood s)
      (Disj:disj G (definedVars s))
      (FVincl: freeVars s ⊆ G)
  : renamedApart s (renamedApartAnn s G).
Proof.
  general induction RAG; simpl in *.
  - econstructor; eauto.
    + revert Disj. clear_all. cset_tac.
    + rewrite <- FVincl. clear_all. cset_tac.
    + eapply IHRAG. revert Disj H. clear_all. cset_tac.
      rewrite <- FVincl. clear_all. cset_tac.
    + reflexivity.
    + eapply renamedApartAnn_decomp.
  - econstructor; only 6,7: eauto using renamedApartAnn_decomp; eauto.
    + rewrite <- FVincl. clear_all. cset_tac.
    + rewrite !snd_renamedApartAnn; eauto.
    + eapply IHRAG1. eauto with cset.
      rewrite <- FVincl. eauto with cset.
    + eapply IHRAG2. eapply disj_2_incl; eauto.
      rewrite <- FVincl. eauto with cset.
  - econstructor; eauto.
  - econstructor; eauto.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    econstructor.
    + eauto with len.
    + intros; inv_get. len_simpl. inv_get.
      eapply H0. eauto.
      * eapply disj_union_left.
        -- symmetry. eapply disj_2_incl; eauto.
           unfold definedVarsF, defVarsZs.
           rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
           eauto with cset.
        -- symmetry. eapply disj_incl; try eapply H3.
           ++ rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
             eauto with cset.
           ++ rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
      * rewrite <- FVincl.
        rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
        clear. cset_tac.
    + instantiate (1:=definedVars t).
      hnf; intros; inv_get. len_simpl. inv_get.
      econstructor.
      * rewrite renamedApartAnn_decomp. simpl. rewrite union_comm. reflexivity.
      * split; eauto.
        split. symmetry. eapply disj_2_incl; eauto.
        unfold definedVarsF.
        rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
        unfold defVarsZs. eauto with cset.
        rewrite snd_renamedApartAnn; eauto.
        symmetry. eapply disj_2_incl; eauto.
        rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
    + hnf; intros; inv_get. len_simpl. inv_get.
      unfold defVars.
      rewrite !snd_renamedApartAnn; eauto.
      exploit H1; try eapply H5; eauto.
    + eapply IHRAG.
      * eapply disj_2_incl; eauto.
      * rewrite <- FVincl. eauto with cset.
    + rewrite renamedApartAnn_decomp.
      rewrite snd_renamedApartAnn; eauto.
    + rewrite snd_renamedApartAnnF.
      rewrite snd_renamedApartAnn.
      rewrite defVars_ra_defVarsZs; eauto with len.
      intros; inv_get. len_simpl. inv_get.
      eapply H0. eauto.
      *  eapply disj_union_left.
        -- symmetry. eapply disj_2_incl; eauto.
           unfold definedVarsF, defVarsZs.
           rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
           eauto with cset.
        -- symmetry. eapply disj_incl; try eapply H3.
           ++ rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
             eauto with cset.
           ++ rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
      * rewrite <- FVincl.
        rewrite <- incl_list_union; eauto using map_get_1; try reflexivity.
        clear. cset_tac.
Qed.
