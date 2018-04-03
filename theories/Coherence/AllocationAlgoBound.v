Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take Subset1 ListMax.
Require Import Val Var Envs IL Annotation Liveness.Liveness MoreList SetOperations.
Require Import AnnotationLattice AnnP.
Require Import Coherence Coherence.Allocation RenamedApart AllocationAlgo.
Require Import RenamedApart_Liveness LabelsDefined Restrict InfiniteSubset InfinitePartition MapSep.
Require Import RenameApart_Partition Filter AllocationAlgoSep StableFresh.

Set Implicit Arguments.

Require Import AllocationAlgoCorrect AnnP BoundedIn VarP SmallestK.

Lemma mapAnn_renamedApart al ans s (ϱ ϱ': var -> var)
      (P1:Proper (_eq ==> _eq) ϱ) (P2:Proper (_eq ==> _eq) ϱ')
      (AR:ann_R Subset1 al ans)
      (RA:renamedApart s ans)
      (AGR:agree_on _eq (fst (getAnn ans) ∪ snd (getAnn ans)) ϱ ϱ')
:  ann_R SetInterface.Equal (mapAnn (lookup_set ϱ) al)
         (mapAnn (lookup_set ϱ') al).
Proof.
  general induction RA; invt @ann_R; pe_rewrite; simpl in *; set_simpl.
  - econstructor; eauto.
    + eapply lookup_set_agree; eauto.
      simpl. eapply agree_on_incl; eauto. eauto with cset.
    + eapply IHRA; eauto using agree_on_incl with cset.
  - econstructor; eauto.
    + eapply lookup_set_agree; eauto.
      simpl. eapply agree_on_incl; eauto. eauto with cset.
    + eauto using agree_on_incl with cset.
    + eauto using agree_on_incl with cset.
  - econstructor; eauto.
    + eapply lookup_set_agree; eauto.
      simpl. eapply agree_on_incl; eauto.
  - econstructor; eauto.
    + eapply lookup_set_agree; eauto.
      simpl. eapply agree_on_incl; eauto.
  - econstructor; eauto.
    + eapply lookup_set_agree; eauto.
      simpl. eapply agree_on_incl; eauto. rewrite <- H9. clear; cset_tac.
    + eauto with len.
    + intros; inv_get.
      eapply H1; eauto.
      simpl. eapply agree_on_incl; eauto.
      eapply ans_incl_D_union; eauto.
    + eapply IHRA; eauto.
      simpl. eapply agree_on_incl; eauto.
      clear; cset_tac.
Qed.

Lemma regAssign_assignment_small k p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (LS:live_sound Functional ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (RA:renamedApart s ra)
      (INCL:ann_R Subset1 alv ra)
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (part_size_bounded (part_1 p) k) alv)
      (up:For_all (part_vars_bounded (part_1 p) k) (lookup_set (findt ϱ default_var) (getAnn alv)))
  : ann_P (For_all (part_vars_bounded (part_1 p) k)) (mapAnn (lookup_set (findt ϱ' default_var)) alv).
Proof.
  general induction LS; invt ann_P; invt renamedApart; invt @ann_R; simpl in *.
  - econstructor; eauto.
    + exploit regAssign_renamedApart_agree; eauto using live_sound.
      pe_rewrite.
      rewrite <- map_update_update_agree in H2.
      eapply agree_on_update_inv in H2.
      rewrite <- lookup_set_agree; swap 1 4.
      simpl. eapply agree_on_incl; eauto. revert H10 H7; clear; cset_tac.
      eauto. eauto. eauto.
    + eapply IHLS; eauto.
      * eapply injective_on_agree; [|eapply map_update_update_agree].
        eapply injective_on_update_fresh; eauto using injective_on_incl.
        eapply least_fresh_part_fresh.
      * rewrite <- map_update_update_agree.
        eapply sep_update_part.
        eauto using sep_incl.
      * hnf; intros.
        rewrite <- lookup_set_agree in H2; swap 1 4.
        eapply map_update_update_agree. eauto. eauto.
        assert (EQal:getAnn al [=] getAnn al \ singleton x ∪ singleton x). {
          revert H1. clear.
          cset_tac.
        }
        eapply lookup_set_morphism_eq in H2; [|rewrite EQal; reflexivity].
        rewrite lookup_set_union in H2. eapply union_iff in H2; destruct H2.
        -- rewrite lookup_set_agree in H2; swap 1 4.
           eapply agree_on_update_dead. clear. cset_tac. reflexivity. eauto. eauto.
           eapply up. rewrite <- H0. eauto.
        -- rewrite lookup_set_singleton' in H2; eauto. eapply In_single in H2.
           invc H2. lud; [|isabsurd].
           hnf; intros. eapply ann_P_get in H5.
           eapply least_fresh_part_small1. eauto.
           rewrite <- sep_filter_map_comm.
           rewrite <- H5. rewrite cardinal_map.
           eapply subset_cardinal_lt with (x0 := x).
           rewrite filter_difference. eauto with cset. eauto.
           eapply zfilter_3; eauto.
           eapply least_fresh_part_p1 in H2. eauto.
           rewrite filter_incl. clear. cset_tac.
           eauto. eauto. eauto. eapply sep_incl; eauto.
        -- eauto.
  - monadS_inv allocOK.
    exploit regAssign_renamedApart_agree; eauto using live_sound. pe_rewrite.
    exploit regAssign_renamedApart_agree; try eapply EQ; eauto using live_sound. pe_rewrite.
    exploit regAssign_renamedApart_agree'; eauto. pe_rewrite.
    econstructor; eauto.
    + rewrite <- lookup_set_agree; eauto.
      simpl.
      etransitivity; eauto using agree_on_incl.
    + exploit IHLS1; eauto.
      * eauto using injective_on_incl; eauto.
      * rewrite H0. eauto.
      * eapply ann_P_morph with (R:=SetInterface.Equal); eauto.
        intros. rewrite <- H17. eauto.
        eapply mapAnn_renamedApart; eauto.
        eapply agree_on_incl; eauto.
        pe_rewrite. rewrite <- disj_eq_minus; try reflexivity.
        eapply disj_union_left. symmetry. eapply renamedApart_disj in H12. pe_rewrite. eauto.
        symmetry; eauto.
    + exploit IHLS2; try eapply EQ0; eauto.
      * eapply injective_on_agree; swap 1 2.
        simpl.
        eapply agree_on_incl. eapply H3. etransitivity; eauto.
        eauto using injective_on_incl; eauto.
      * rewrite H1. eapply sep_agree. eauto using agree_on_incl.
        eauto.
      * rewrite <- lookup_set_agree; swap 1 4.
        simpl. eapply agree_on_incl; eauto. etransitivity; eauto.
        eauto. eauto. rewrite H1. eauto.
  - econstructor.
    eauto.
  - econstructor; eauto.
  - monadS_inv allocOK.
    exploit regAssign_renamedApart_agree; eauto using live_sound. pe_rewrite.
    exploit regAssign_renamedApart_agreeF'; eauto using live_sound.
    intros. eapply regAssign_renamedApart_agree'; eauto using live_sound.
    reflexivity.
    econstructor; eauto.
    + rewrite <- lookup_set_agree; eauto.
      simpl.
      etransitivity; eauto using agree_on_incl.
      eapply agree_on_incl; eauto.
      rewrite <- disj_eq_minus; try reflexivity.
      rewrite H19.  eapply disj_D_defVars; eauto.
    + intros. inv_get.
      edestruct regAssignF_get; eauto.
      * intros. exploit disj_D_defVars; eauto.
        eapply renamedApart_disj in H13. pe_rewrite.
        eapply defVars_disj_D; eauto. eapply disj_union_right; eauto.
      * dcr. instantiate (1:=fst (getAnn x1) ∪ snd (getAnn x1)) in H27.
        rewrite <- disj_eq_minus in H27; try reflexivity; swap 1 2.
        {
          edestruct H11; dcr; eauto.
          rewrite H20. setoid_rewrite union_comm at 2. rewrite union_assoc.
          eapply disj_union_left; symmetry.
          eapply disj_D_defVars_take; eauto.
          exploit defVars_take_disj; eauto.
        }
        rewrite <- map_update_list_update_agree' in H27; eauto with len.
        assert (INCLx0:getAnn x0 ⊆ fst (getAnn x1) ∪ snd (getAnn x1)). {
          exploit H22; eauto.
          eapply ann_R_get in H20. rewrite H20. eauto with cset.
        }
        assert (DECOMP:getAnn x0 [=] getAnn x0 \ of_list (fst x2) ∪ of_list (fst x2)). {
          edestruct H2; eauto; dcr.
          revert H20; clear; cset_tac.
        }
        assert (Inclx2:getAnn x0 \ of_list (fst x2) ⊆ lv). {
          edestruct H2; eauto; dcr.
        }
        exploit H1; eauto.
        -- eapply injective_on_agree; simpl; eauto using agree_on_incl.
           rewrite DECOMP at 1.
           eapply injective_on_fresh_list. eauto.
           eapply injective_on_incl; eauto. eauto with len.
           eapply fresh_list_stable_spec.
           eapply fresh_list_stable_nodup.
        -- eapply sep_agree; eauto.
           eapply agree_on_incl; eauto.
           rewrite DECOMP at 1.
           eapply sep_update_list; eauto.
           edestruct H2; eauto.
           eapply sep_incl; eauto.
           rewrite <- Inclx2. clear. cset_tac.
        -- rewrite <- lookup_set_agree; swap 1 4; eauto using agree_on_incl.
           rewrite DECOMP at 2.
           rewrite lookup_set_union; eauto.
           rewrite lookup_set_update_disj; eauto; swap 1 2.
           clear. cset_tac.
           rewrite For_all_union; split.
           ++ rewrite Inclx2. eauto.
           ++ edestruct H2; eauto; dcr.
             rewrite update_with_list_lookup_list; eauto with len.
             eapply fresh_list_stable_small; eauto.
             exploit H8 as BNDk; eauto. eapply ann_P_get in BNDk.
             hnf in BNDk.
             rewrite DECOMP in BNDk.
             rewrite filter_union in BNDk; eauto.
             rewrite union_cardinal in BNDk; eauto; swap 1 2.
             rewrite !filter_incl; eauto.
             rewrite <- cardinal_map with (f:=findt ϱ default_var) in BNDk; eauto.
             rewrite <- sep_filter_map_comm; eauto.
        -- eapply ann_P_morph with (R:=SetInterface.Equal); eauto.
           intros. rewrite <- H26. eauto.
           eapply mapAnn_renamedApart; eauto.
           eapply regAssign_renamedApart_agreeF' with (ans:=drop (S n ) ans) in H24;
             eauto; try reflexivity; intros; inv_get; eauto with len.
           ++ etransitivity. eapply agree_on_incl; eauto.
             rewrite <- disj_eq_minus; swap 1 3.
             eapply disj_fst_snd_ra; eauto. reflexivity. reflexivity.
             eapply agree_on_incl.
             eapply regAssign_renamedApart_agree'; try eapply EQ0; eauto.
             pe_rewrite.
             rewrite <- disj_eq_minus; swap 1 3; try reflexivity.
             eapply disj_fst_snd_Dt; eauto.
           ++ eapply regAssign_renamedApart_agree' in H30; eauto.
    + exploit IHLS; try eapply EQ0; eauto.
      * eapply injective_on_agree; swap 1 2.
        change _eq with (@eq var).
        eapply agree_on_incl. eapply H5. etransitivity; eauto.
        rewrite <- disj_eq_minus; try reflexivity.
        rewrite H19.  eapply disj_D_defVars; eauto.
        eauto using injective_on_incl; eauto.
      * eapply sep_incl; eauto.
        etransitivity; eauto.
        rewrite <- disj_eq_minus; try reflexivity.
        rewrite H19.  eapply disj_D_defVars; eauto.
      * rewrite <- lookup_set_agree; swap 1 4.
        eapply agree_on_incl; eauto.
        etransitivity; eauto.
        rewrite <- disj_eq_minus; try reflexivity.
        rewrite H19.  eapply disj_D_defVars; eauto. eauto. eauto.
        rewrite H3. eauto.
Qed.

Lemma regAssign_assignment_small_I k p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (LS:live_sound Imperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (RA:renamedApart s ra)
      (INCL:ann_R Subset1 alv ra)
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (part_size_bounded (part_1 p) k) alv)
      (up:For_all (part_vars_bounded (part_1 p) k) (lookup_set (findt ϱ default_var) (getAnn alv)))
      (BOUND:bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ra)))
      (NUC:noUnreachableCode (isCalled true) s)
  : ann_P (For_all (part_vars_bounded (part_1 p) k)) (mapAnn (lookup_set (findt ϱ' default_var)) alv).
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in LS; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in LS.
  exploit regAssign_assignment_small; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
Qed.

Lemma ann_P_live_var_P i ZL Lv p k s lv
  : ann_P (For_all (part_vars_bounded p k)) lv
    -> live_sound i ZL Lv s lv
    -> var_P (part_vars_bounded p k) s.
Proof.
  intros ANN LS.
  general induction LS; invt ann_P; eauto using var_P, ann_P_get.
  - econstructor; eauto.
    + eapply ann_P_get in H5. eauto.
    + rewrite Exp.freeVars_live; eauto.
  - econstructor; eauto.
    rewrite Ops.freeVars_live; eauto.
  - econstructor; eauto.
    rewrite Ops.freeVars_live_list; eauto.
  - econstructor; eauto.
    rewrite Ops.freeVars_live; eauto.
  - econstructor; intros; inv_get; eauto.
    edestruct H2; dcr; eauto.
    exploit H8; eauto. eapply ann_P_get in H10.
    rewrite H6; eauto.
Qed.