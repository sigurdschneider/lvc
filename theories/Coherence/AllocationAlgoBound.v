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

Definition regbnd (p:inf_subset var) k (x:positive) := p x -> (x ∈ of_list (ksmallest p k)).
Definition part_bounded_in X `{OrderedType X} (p:inf_subset X) k a :=
  SetInterface.cardinal (filter p a) <= k.

Lemma cardinal_filter_incl X `{OrderedType X} Z i x (p:inf_subset X)
  (GET:get Z i x) (P1:p x) (ND: NoDupA _eq Z)
  : 0 < SetInterface.cardinal (filter p (of_list Z)).
Proof.
  general induction GET; simpl.
  - rewrite filter_add_in; eauto.
    rewrite add_cardinal_2. omega. inv ND.
    rewrite filter_incl; eauto.
  - rewrite add_union_singleton.
    rewrite filter_union; eauto.
    rewrite union_cardinal.
    exploit IHGET; eauto. omega.
    rewrite !filter_incl; eauto.
    hnf. cset_tac'. rewrite <- H0 in H1.
    eapply InA_in in H1; eauto.
    invc ND. eauto.
Qed.

Lemma regAssign_assignment_small k p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (LS:live_sound Functional ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (RA:renamedApart s ra)
      (INCL:ann_R Subset1 alv ra)
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (part_bounded_in (part_1 p) k) alv)
      (up:For_all (regbnd (part_1 p) k) (lookup_set (findt ϱ default_var) (getAnn alv)))
  : ann_P (For_all (regbnd (part_1 p) k)) (mapAnn (lookup_set (findt ϱ' default_var)) alv).
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
           revert H2. unfold least_fresh_part. cases. intros.
           eapply least_fresh_part_bounded.
           hnf in H5. rewrite <- sep_filter_map_comm.
           rewrite <- H5. rewrite cardinal_map.
           eapply subset_cardinal_lt with (x0 := x).
           rewrite filter_difference. eauto with cset. eauto.
           eapply zfilter_3; eauto. rewrite filter_incl. clear. cset_tac.
           eauto. eauto. eauto. eapply sep_incl; eauto.
           intros.
           enough ((part_2 p)
                     (least_fresh_P (part_2 p) (SetConstructs.map (findt ϱ default_var) (getAnn al \ singleton x)))).
           exfalso. eapply (part_disj p _ H2 H3).
           eapply least_fresh_P_p; eauto.
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
           eapply disj_intersection.
           eapply fresh_list_stable_spec. simpl.
           edestruct H2; eauto.
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
           ++ rewrite update_with_list_lookup_list; eauto with len.
             ** exploit H8 as BNDk; eauto. eapply ann_P_get in BNDk.
                hnf in BNDk.
                rewrite DECOMP in BNDk.
                rewrite filter_union in BNDk; eauto.
                rewrite union_cardinal in BNDk; eauto; swap 1 2.
                rewrite !filter_incl; eauto.
                rewrite <- cardinal_map with (f:=findt ϱ default_var) in BNDk; eauto.
                hnf; intros.
                eapply of_list_get_first in H20; eauto; dcr. invc H28.
                edestruct fresh_list_stable_get; eauto; dcr. subst.
                hnf; simpl. intros.
                unfold least_fresh_part. cases.
                --- eapply least_fresh_part_bounded.
                    rewrite <- BNDk.
                    rewrite filter_union; eauto.
                    rewrite union_cardinal_le; eauto.
                    rewrite <- sep_filter_map_comm; eauto.
                    rewrite plus_comm.
                    eapply plus_lt_compat_l.
                    eapply cardinal_smaller; eauto.
                    edestruct H2; eauto.
                --- simpl in *.
                    unfold least_fresh_part in H20. cases in H20. congruence.
                    eapply part_disj in H20. inv H20.
                    eapply least_fresh_P_p.
             ** edestruct H2; dcr; eauto.
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

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_assignment_small]
    above, which we did prove by induction. *)


Lemma regAssign_assignment_small' k p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (LS:live_sound Imperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (RA:renamedApart s ra)
      (INCL:ann_R Subset1 alv ra)
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (part_bounded_in (part_1 p) k) alv)
      (up:For_all (regbnd (part_1 p) k) (lookup_set (findt ϱ default_var) (getAnn alv)))
      (BOUND:bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ra)))
      (NUC:noUnreachableCode (isCalled true) s)
  : ann_P (For_all (regbnd (part_1 p) k)) (mapAnn (lookup_set (findt ϱ' default_var)) alv).
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in LS; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in LS.
  exploit regAssign_assignment_small; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
Qed.
