Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take Subset1 ListMax.
Require Import Val Var Envs IL Annotation Liveness.Liveness Fresh MoreList SetOperations AnnP.
Require Import Coherence Coherence.Allocation RenamedApart AllocationAlgo.
Require Import RenamedApart_Liveness LabelsDefined Restrict InfinitePartition MapSep.
Require Import RenameApart_Partition Filter.

Set Implicit Arguments.

Inductive locally_sep (p:inf_partition var) (rho:env var)
  : ann (set var) -> Prop :=
| RNOpr lv (al:ann (set var))
  :  locally_sep p rho al
     -> sep var p lv rho
     -> locally_sep p rho (ann1 lv al)
| RNIf lv (alv1 alv2:ann (set var))
  :  sep var p lv rho
     -> locally_sep p rho alv1
     -> locally_sep p rho alv2
     -> locally_sep p rho (ann2 lv alv1 alv2)
| RNGoto lv
  : sep var p lv rho
    -> locally_sep p rho (ann0 lv)
| RNReturn lv
  : sep var p lv rho
    -> locally_sep p rho (ann0 lv)
| RNLet lv alvs alvb
  : (forall n alv, get alvs n alv -> locally_sep p rho alv)
    -> locally_sep p rho alvb
    -> sep var p lv rho
    -> locally_sep p rho (annF lv alvs alvb).

Lemma locally_separate p ϱ lv
  : locally_sep p ϱ lv -> sep var p (getAnn lv) ϱ.
Proof.
  inversion 1; eauto.
Qed.

Lemma locally_sep_ext D p ϱ ϱ' lv ra s
      (LS:locally_sep p ϱ lv)
      (Incl1:ann_R (fun x y => x ⊆ fst y) lv ra)
      (RA:renamedApart s ra)
      (Incl2:fst (getAnn ra) ∪ snd (getAnn ra) ⊆ D)
      (Agr:agree_on eq D ϱ ϱ')
  : locally_sep p ϱ' lv.
Proof.
  general induction LS;
    pose proof (ann_R_get Incl1) as incl; simpl in incl;
      invt renamedApart;
      invt @ann_R; simpl in *; pe_rewrite; set_simpl.
  - econstructor.
    + eapply IHLS; eauto.
      pe_rewrite. rewrite <- Incl2; clear; cset_tac.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- H8. eauto with cset.
  - econstructor; eauto.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- H11. eauto with cset.
    + eapply IHLS1; eauto; pe_rewrite.
      rewrite <- Incl2. clear; cset_tac.
    + eapply IHLS2; eauto; pe_rewrite.
      rewrite <- Incl2. clear; cset_tac.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor.
    eapply sep_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite <- Incl2. eauto with cset.
  - econstructor; eauto.
    + intros. inv_get.
      eapply H0; eauto.
      rewrite <- Incl2.
      edestruct H4; eauto; dcr.
      rewrite H11.
      rewrite <- incl_list_union; eauto using zip_get; [|reflexivity].
      unfold defVars. clear; cset_tac.
    + eapply IHLS; eauto.
      pe_rewrite. rewrite <- Incl2.
      clear; cset_tac.
    + eapply sep_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite <- Incl2, <- incl; eauto.
Qed.

Lemma sep_part_bounded p k lv ϱ
      (AN:ann_P (part_bounded var (part_1 p) k) lv)
      (LS:locally_sep p ϱ lv)
  : ann_P (part_bounded var (part_1 p) k) (mapAnn (lookup_set ϱ) lv).
Proof.
  general induction AN; invt locally_sep;
    simpl in *; econstructor; eauto using part_bounded_sep.
  - intros; inv_get; eauto.
Qed.

Instance sep_agree_morph_impl p lv
  : Proper (agree_on eq lv ==> impl) (sep var p lv).
Proof.
  unfold Proper, respectful, impl.
  eauto using sep_agree.
Qed.

Instance sep_agree_morph_iff p lv
  : Proper (agree_on eq lv ==> iff) (sep var p lv).
Proof.
  unfold Proper, respectful; split.
  eauto using sep_agree.
  symmetry in H. eauto using sep_agree.
Qed.

Lemma sep_update_part p ϱ lv x G
      (SEP:sep var p (lv \ singleton x) ϱ)
  : sep var p lv (ϱ [x <- least_fresh_part p G x]).
Proof.
  unfold sep in SEP; dcr.
  hnf; split; intros; lud.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
  - invc e. eauto using least_fresh_part_1,least_fresh_part_2.
  - cset_tac.
Qed.

Lemma regAssign_sep p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (Sep:sep var p (getAnn alv) (findt ϱ default_var))
      (sd:renamedApart s ra)
      (incl:ann_R (fun x y => x ⊆ fst y) alv ra)
: locally_sep p (findt ϱ' default_var) alv.
Proof.
  intros.
  general induction LS; simpl in *;
    pose proof (ann_R_get incl) as incl'; simpl in incl';
      invt @ann_R;
      try monadS_inv allocOK; invt renamedApart;
        pe_rewrite; simpl in *; set_simpl.

  - econstructor; eauto. eapply IHLS; eauto.
    + eapply injective_on_update_cmap_fresh; eauto using injective_on_incl.
    + rewrite <- map_update_update_agree.
      eapply sep_update_part; eauto.
    + exploit regAssign_renamedApart_agree; eauto; pe_rewrite.
      eapply sep_agree.
      * eapply agree_on_incl; eauto with cset.
      * rewrite <- map_update_update_agree.
        eapply sep_update_part; eauto.
  - exploit regAssign_renamedApart_agree; try eapply EQ; eauto; pe_rewrite.
    exploit IHLS1; try eapply EQ; eauto using injective_on_incl, sep_incl.
    exploit IHLS2; try eapply EQ0; pe_rewrite; eauto using sep_incl, sep_agree, agree_on_incl.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto using agree_on_incl.
    + exploit regAssign_renamedApart_agree; eauto. pe_rewrite.
      econstructor; eauto.
      * assert (agree_on eq lv (findt ϱ default_var) (findt ϱ' default_var)). {
          etransitivity; eauto using agree_on_incl.
        }
        rewrite <- H9; eauto.
      * exploit regAssign_renamedApart_agree' as AGR;
          try eapply EQ0; simpl; eauto using live_sound. pe_rewrite.
        instantiate (1:=D ∪ Ds) in AGR.
        eapply locally_sep_ext; eauto.
        pe_rewrite.
        eapply renamedApart_disj in H15; pe_rewrite.
        revert H12 H15. clear_all. cset_tac.
  - econstructor; eauto.
  - econstructor; eauto.
  - exploit regAssign_renamedApart_agreeF' as Agr1;
      eauto using regAssign_renamedApart_agree'. reflexivity.
    instantiate (1:=D) in Agr1.
    exploit regAssign_renamedApart_agree as Agr2;
      try eapply EQ0; simpl; eauto using live_sound.
    assert (AGR:agree_on _eq lv (findt ϱ default_var) (findt x default_var)). {
      eapply agree_on_incl; eauto.
      rewrite disj_minus_eq; eauto using disj_D_defVars.
    }
    exploit (IHLS p); try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
    + assert (DDISJ:forall n  DD' Zs, get F n Zs -> get bns n DD' ->
                                 disj D (defVars Zs DD')). {
        eapply defVars_disj_D; eauto with cset.
      }
      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          inv_get. rename x1 into Zs.
          edestruct (regAssignF_get p (fst (getAnn x0) ∪ snd (getAnn x0)
                                           ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H22; eauto with len.
          exploit H1; eauto. pe_rewrite.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H12; clear_all; cset_tac.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply disj_lv_take; eauto.
            simpl in *.
            setoid_rewrite <- H12 at 1.
            eapply injective_on_fresh_list; eauto with len.
            + eapply injective_on_incl; eauto.
              eapply H2; eauto.
            + eapply disj_intersection.
              eapply disj_2_incl.
              eapply fresh_list_stable_spec.
              reflexivity.
            + edestruct H2; eauto.
            + eapply fresh_list_stable_nodup; eauto using least_fresh_part_fresh.
          - exploit H2; eauto; dcr.
            eapply sep_agree. eapply agree_on_incl; eauto.
            + rewrite <- incl_right.
              rewrite disj_minus_eq; eauto.
              eapply disj_lv_take; eauto.
            + eapply sep_update_list; eauto.
          - eapply locally_sep_ext; eauto.
            reflexivity.
            pe_rewrite.
            eapply regAssign_renamedApart_agreeF' in H19;
              eauto using get_drop, drop_length_stable; try reflexivity.
            + eapply regAssign_renamedApart_agree' in EQ0; simpl; eauto using live_sound.
              etransitivity; eapply agree_on_incl; try eassumption.
              * rewrite disj_minus_eq. reflexivity.
                eapply disj_fst_snd_ra; eauto.
              * pe_rewrite.
                rewrite disj_minus_eq. reflexivity.
                eapply disj_fst_snd_Dt; eauto.
            + intros.
              eapply regAssign_renamedApart_agree'; eauto using get_drop, drop_get.
        }
      * pe_rewrite.
        eapply sep_agree; eauto.
        etransitivity; eapply agree_on_incl; eauto.
Qed.



(** ** Bound on the number of registers used *)

Fixpoint largest_live_set (a:ann (set var)) : set var :=
  match a with
    | ann0 gamma => gamma
    | ann1 gamma a => max_set gamma (largest_live_set a)
    | ann2 gamma a b => max_set gamma (max_set (largest_live_set a) (largest_live_set b))
    | annF gamma s b => max_set gamma (max_set (fold_left (fun gamma b => max_set gamma (largest_live_set b)) s ∅)
                                      (largest_live_set b))
  end.

Fixpoint size_of_largest_live_set (p:var -> bool) (a:ann (set var)) : nat :=
  let sz := (fun gamma => SetInterface.cardinal (filter p gamma)) in
  match a with
    | ann0 gamma => SetInterface.cardinal gamma
    | ann1 gamma a => max (sz gamma) (size_of_largest_live_set p  a)
    | ann2 gamma a b => max (sz gamma)
                       (max (size_of_largest_live_set p a)
                            (size_of_largest_live_set p b))
    | annF gamma a b => max (sz gamma)
                       (max (list_max (List.map (size_of_largest_live_set p) a))
                            (size_of_largest_live_set p b))
  end.

Lemma size_of_largest_live_set_live_set p al
  : SetInterface.cardinal (filter p (getAnn al))
    <= size_of_largest_live_set p al.
Proof.
  destruct al; simpl; eauto using Max.le_max_l.
  rewrite cardinal_filter; eauto.
Qed.

Require Import AllocationAlgoCorrect AnnP BoundedIn VarP.

Definition regbnd p k (x:positive) := part_1 p x -> (x <= Pos.of_nat (2*k))%positive.


Lemma regAssign_assignment_small k p VD (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (RA:renamedApart s ra)
      (INCL:ann_R Subset1 alv ra)
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (bounded_in VD k) alv)
      (up:For_all (regbnd p k) (lookup_set (findt ϱ default_var) (getAnn alv)))
  : ann_P (For_all (regbnd p k)) (mapAnn (lookup_set (findt ϱ' default_var)) alv).
Proof.
  general induction LS; invt ann_P; invt renamedApart; invt @ann_R; simpl in *.
  - econstructor; eauto.
    + exploit regAssign_renamedApart_agree; eauto using live_sound.
      pe_rewrite.
      admit.
    + eapply IHLS; eauto.
      * eapply injective_on_agree; [|eapply map_update_update_agree].
        eapply injective_on_update_fresh; eauto using injective_on_incl.
        eapply least_fresh_part_fresh.
      * rewrite <- map_update_update_agree.
        eapply sep_update_part.
        eauto using sep_incl.
      * admit.
  - monadS_inv allocOK.
    exploit regAssign_renamedApart_agree; eauto using live_sound. pe_rewrite.
    exploit regAssign_renamedApart_agree; try eapply EQ; eauto using live_sound. pe_rewrite.
    exploit regAssign_renamedApart_agree'; eauto. pe_rewrite.
    econstructor; eauto.
    + rewrite <- lookup_set_agree; eauto.
      change _eq with (@eq var).
      etransitivity; eauto using agree_on_incl.
    + exploit IHLS1; eauto.
      * eauto using injective_on_incl; eauto.
      * rewrite H0. eauto.
      * admit.
    + exploit IHLS2; try eapply EQ0; eauto.
      * eapply injective_on_agree; swap 1 2.
        change _eq with (@eq var).
        eapply agree_on_incl. eapply H3. etransitivity; eauto.
        eauto using injective_on_incl; eauto.
      * rewrite H1. eapply sep_agree. eauto using agree_on_incl.
        eauto.
      * rewrite <- lookup_set_agree; swap 1 4.
        change _eq with (@eq var). eapply agree_on_incl; eauto. etransitivity; eauto.
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
    + admit.
    + intros. inv_get.
      admit.
    + admit.
Qed.

Lemma regAssign_assignment_small k p VD (ϱ:Map [var,var]) ZL Lv s alv ϱ'
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ default_var))
      (SEP:sep var p (getAnn alv) (findt ϱ default_var))
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (BND:ann_P (bounded_in VD k) alv)
      (up:For_all (regbnd p k) (lookup_set (findt ϱ default_var) (getAnn alv)))
  : ann_P (For_all (regbnd p k)) (mapAnn (lookup_set (findt ϱ default_var)) alv).
Proof.


  exploit regAssign_renamedApart_agree; eauto using live_sound.
  rewrite lookup_set_agree in up; swap 1 4.
  eapply agree_on_incl; eauto; swap 1 2. eapply filter_incl. eauto. eauto. eauto.
  clear H.
  general induction LS; invt renamedApart; simpl in * |- *.
  - assert (singleton (findt ϱ' default_var x)
                      ⊆ vars_up_to (ofNat (size_of_largest_live_set (part_1 p) al))). {
      intros.
      eapply regAssign_renamedApart_agree in allocOK; eauto.
      rewrite <- allocOK; [|pe_rewrite; eauto with cset].
      unfold findt at 1. rewrite MapFacts.add_eq_o; eauto.
      eapply incl_singleton. eapply in_vars_up_to.
      unfold least_fresh_part. cases.
      admit.
      (*rewrite <- size_of_largest_live_set_live_set.
      rewrite <- sep_filter_map_comm.
      rewrite filter_difference; eauto.
      rewrite cardinal_map; eauto.
      rewrite filter_singleton_in; try cases; eauto.
      rewrite cardinal_difference'; [|eauto with cset].
      rewrite singleton_cardinal.
      assert (SetInterface.cardinal
                (filter (fun x0 : nat => if [x0 <= c] then true else false)
                        (getAnn al)) > 0). {
        rewrite <- (add_minus_single_eq H1).
        rewrite filter_add_in.
        rewrite add_cardinal_2. omega. cset_tac; intuition.
        intuition. cases; eauto.
      }
      unfold var in *. omega.
      rewrite <- (add_minus_single_eq H1).
      rewrite filter_add_in; try cases; eauto.
      cset_tac.
       *)
      admit.
    }
    exploit IHLS; eauto.
    + admit.
    + admit.
    + pe_rewrite.
      rewrite <- incl. eauto with cset.
    + pe_rewrite.
      instantiate (1:=(max (size_of_largest_live_set c al) n)).
      decide (x <= c).
      * rewrite filter_add_in; try cases; eauto.
        rewrite lookup_set_add; eauto.
        rewrite up.
        rewrite vars_up_to_max, add_union; eauto.
        rewrite H2; eauto.
      * rewrite filter_add_notin; try cases; eauto.
        rewrite up.
        rewrite vars_up_to_max; eauto.
    + pe_rewrite. rewrite H9.
      decide (x <= c).
      * rewrite filter_add_in; try cases; eauto.
        rewrite lookup_set_add; eauto. rewrite H3.
        repeat rewrite vars_up_to_max.
        rewrite add_union, H2.
        clear_all. cset_tac. eauto.
      * rewrite filter_add_notin; try cases; eauto.
        rewrite H3. repeat rewrite vars_up_to_max.
        clear_all. cset_tac.
  - monadS_inv allocOK.
    exploit IHLS1; eauto; pe_rewrite.
    + rewrite <- incl; eauto.
    + rewrite lookup_set_agree; eauto.
      eapply agree_on_incl; try eapply regAssign_renamedApart_agree;
      try eapply EQ0; eauto using live_sound.
      rewrite H12; simpl; eauto.
    + exploit IHLS2; try eapply EQ0; eauto; pe_rewrite.
      * rewrite <- incl; eauto.
      * simpl. eauto.
      * rewrite <- H7.
        rewrite lookup_set_union; eauto.
        rewrite H3.
        rewrite lookup_set_agree; eauto. rewrite H2.
        repeat (try rewrite <- Nat.add_max_distr_r; rewrite vars_up_to_max).
        clear_all; cset_tac; intuition.
        eapply agree_on_incl.
        symmetry.
        eapply regAssign_renamedApart_agree';
          try eapply EQ0; eauto. rewrite H12; simpl.
        instantiate (1:=Ds). revert H6; clear_all; cset_tac; intuition; eauto.

  - rewrite H8. rewrite lookup_set_empty; cset_tac; intuition; eauto.
  - rewrite H2. rewrite lookup_set_empty; cset_tac; intuition; eauto.

  - repeat (try rewrite <- Nat.add_max_distr_r; rewrite vars_up_to_max).
    monadS_inv allocOK.
    rewrite <- H13, lookup_set_union; eauto.
    eapply union_incl_split.
    + rewrite lookup_set_list_union; [ | eauto | eapply lookup_set_empty; eauto ].
      eapply list_union_incl; intros; eauto with cset.
      assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                              disj D (defVars Zs DD')).
      {
        intros. eapply renamedApart_disj in sd; simpl in *.
        eapply disj_2_incl; eauto. rewrite <- H13.
        eapply incl_union_left. eapply incl_list_union; eauto.
        eapply zip_get; eauto. reflexivity.
      }
      inv_map H4. inv_zip H5. edestruct get_length_eq; try eapply H; eauto.
      edestruct regAssignF_get; eauto; dcr.
      edestruct H2; eauto.
      edestruct H8; eauto; dcr.
      exploit H1; eauto.
      rewrite H21. rewrite <- incl.
      eauto with cset.
      rewrite H21.
      instantiate (1:=max (list_max List.map size_of_largest_live_set als) n).
      rewrite lookup_set_union; eauto.
      eapply union_incl_split.
      {
        rewrite <- map_update_list_update_agree in H20; eauto.
        exploit regAssign_renamedApart_agree'; try eapply H18; eauto.
        rewrite <- lookup_set_agree.
        Focus 4. etransitivity; eapply agree_on_incl. eapply H20.
        rewrite disj_minus_eq; [ | eauto using defVars_take_disj].
        unfold defVars. eauto. eauto.
        rewrite disj_minus_eq; eauto.
        exploit H7; eauto. eapply renamedApart_disj in H24.
        eapply disj_1_incl; eauto. rewrite H21.
        rewrite <- incl. eauto with cset.
        rewrite lookup_set_update_with_list_in_union_length; eauto.
        rewrite diff_subset_equal. rewrite lookup_set_empty.
        rewrite least_fresh_list_small_vars_up_to.
        eapply union_incl_split; eauto. clear_all; cset_tac; intuition.
        eapply vars_up_to_incl.
        rewrite cardinal_map; eauto.
        rewrite cardinal_difference'.
        rewrite cardinal_of_list_nodup; eauto.
        etransitivity; [|eapply Max.le_max_l].
        assert (length (fst x1) <= SetInterface.cardinal (getAnn x0)).
        rewrite <- (diff_inter_cardinal (getAnn x0) (of_list (fst x1))).
        assert (getAnn x0 ∩ of_list (fst x1) [=] of_list (fst x1)).
        revert H16; clear_all; cset_tac; intuition.
        rewrite H24. rewrite cardinal_of_list_nodup; eauto. omega.
        etransitivity;[| eapply list_max_get; eauto; eapply map_get_1; eauto].
        rewrite <- size_of_largest_live_set_live_set. omega.
        eauto. eauto. eauto. eauto. eauto.
      }
      {
        exploit regAssign_renamedApart_agreeF; eauto using drop_get, get_drop, drop_length_stable,
                                               regAssign_renamedApart_agree'. reflexivity.
        rewrite vars_up_to_max. eapply incl_union_right.
        exploit regAssign_renamedApart_agree'; try eapply EQ0; eauto.
        rewrite lookup_set_agree; try eapply up; eauto.
        etransitivity; eapply agree_on_incl; eauto.
        instantiate (1:=D). rewrite disj_minus_eq; eauto.
        eapply renamedApart_disj in sd.
        eapply disj_2_incl. eauto.
        unfold getAnn, snd. rewrite <- H13.
        eapply incl_union_left.
        rewrite <- drop_zip.
        eapply list_union_drop_incl; eauto.
        instantiate (1:=D). pe_rewrite.
        eapply renamedApart_disj in H10. pe_rewrite.
        rewrite disj_minus_eq; eauto.
      }

      unfold defVars. rewrite lookup_set_union; eauto.
      eapply union_incl_split.
      * assert (FLEQ:lookup_set (findt ϱ' 0) (of_list (fst x1)) ⊆
                           of_list (fresh_list least_fresh
                                               (SetConstructs.map (findt ϱ 0) (getAnn x0 \ of_list (fst x1)))
                                               (length (fst x1)))).
        {
          rewrite <- map_update_list_update_agree in H20; eauto.
          exploit regAssign_renamedApart_agreeF;
            eauto using drop_get, get_drop, drop_length_stable,
            regAssign_renamedApart_agree'. reflexivity.
          exploit regAssign_renamedApart_agree'; try eapply EQ0; eauto.
          exploit regAssign_renamedApart_agree'; eauto.
          rewrite <- lookup_set_agree.
          Focus 4.
          etransitivity; [| eapply agree_on_incl; try eapply X1].
          etransitivity; [| eapply agree_on_incl; try eapply X0].
          etransitivity; [| eapply agree_on_incl; try eapply X2].
          eapply agree_on_incl; try apply H20.
          rewrite disj_minus_eq; [ | eauto using defVars_take_disj].
          unfold defVars. eapply incl_left. eauto.
          rewrite disj_minus_eq; eauto.
          exploit H7; eauto. eapply renamedApart_disj in H29.
          eapply disj_1_incl; eauto. rewrite H21.
          rewrite <- incl. eauto with cset. eauto.
          rewrite disj_minus_eq; [ | eauto using defVars_drop_disj].
          eapply incl_left. eauto.
          rewrite disj_minus_eq; eauto.

          pe_rewrite.
          assert (getAnn x0 [=] getAnn x0 \ of_list (fst x1) ∪ of_list (fst x1)).
          revert H16; clear_all; cset_tac; intuition.
          rewrite H29.
          symmetry. eapply disj_app; split. symmetry.
          eapply disj_1_incl. eapply disj_2_incl.
          eapply renamedApart_disj in sd. eapply sd. simpl.
          rewrite <- H13. eapply incl_right.
          simpl. rewrite H19; eauto.
          symmetry.
          eapply renamedApart_disj in H10. pe_rewrite.
          eapply disj_1_incl; eauto.
          rewrite lookup_set_update_with_list_in_union_length; eauto.
          rewrite diff_subset_equal. rewrite lookup_set_empty.
          clear_all; cset_tac; intuition. intuition. reflexivity.
          eauto. eauto.
        }
        rewrite FLEQ.
        rewrite least_fresh_list_small_vars_up_to.
        eapply incl_union_left. eapply incl_union_right.
        eapply incl_union_left.
        eapply vars_up_to_incl.
        rewrite cardinal_map; eauto.
        rewrite cardinal_difference'.
        rewrite cardinal_of_list_nodup; eauto.
        assert (length (fst x1) <= SetInterface.cardinal (getAnn x0)).
        rewrite <- (diff_inter_cardinal (getAnn x0) (of_list (fst x1))).
        assert (getAnn x0 ∩ of_list (fst x1) [=] of_list (fst x1)).
        revert H16; clear_all; cset_tac; intuition.
        rewrite H24. rewrite cardinal_of_list_nodup; eauto. omega.
        etransitivity;[| eapply list_max_get; eauto; eapply map_get_1; eauto].
        rewrite <- size_of_largest_live_set_live_set. omega.
        eauto.

      * erewrite lookup_set_agree; eauto. erewrite H22; eauto.
        repeat (try rewrite <- Nat.add_max_distr_r; rewrite vars_up_to_max); eauto.
        setoid_rewrite vars_up_to_incl at 1.
        instantiate (1:=list_max List.map size_of_largest_live_set als).
        clear_all; cset_tac; intuition.
        eapply list_max_get. eapply map_get_1; eauto.
        eapply regAssign_renamedApart_agree' in EQ0; eauto. symmetry in EQ0.
        etransitivity; eapply agree_on_incl; eauto.
        pe_rewrite. rewrite disj_minus_eq. reflexivity. eauto with cset.
        symmetry.
        eapply regAssign_renamedApart_agreeF;
          intros; eauto using get_drop, drop_length_stable.
        eapply regAssign_renamedApart_agree'; eauto using get_drop. reflexivity.
        rewrite disj_minus_eq. reflexivity.
        eapply disj_1_incl. eapply defVars_drop_disj; eauto. unfold defVars.
        eauto with cset.

    + exploit IHLS; eauto.
      * pe_rewrite. rewrite <- incl; eauto.
      * pe_rewrite.
        instantiate (1:=max (list_max (List.map size_of_largest_live_set als)) n).
        repeat (try rewrite <- Nat.add_max_distr_r; rewrite vars_up_to_max).
        rewrite up; eauto with cset.
      * pe_rewrite.
        repeat (try rewrite <- Nat.add_max_distr_r in H4; rewrite vars_up_to_max in H4).
        rewrite H4. clear_all; cset_tac; intuition.
Qed.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_assignment_small]
    above, which we did prove by induction. *)


Lemma regAssign_assignment_small' s ang ϱ ϱ' (alv:ann (set var)) ZL Lv n
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> noUnreachableCode isCalled s
  -> regAssign s alv ϱ = Success ϱ'
  -> lookup_set (findt ϱ 0) (fst (getAnn ang)) ⊆ vars_up_to n
  -> lookup_set (findt ϱ' 0) (fst (getAnn ang) ∪ snd (getAnn ang)) ⊆ vars_up_to (max (size_of_largest_live_set alv) n).
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in H0.
  exploit regAssign_assignment_small; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac.
  rewrite lookup_set_union; eauto.
  rewrite H6.
  rewrite <- lookup_set_agree; eauto using regAssign_renamedApart_agree.
  rewrite H5. repeat rewrite vars_up_to_max. cset_tac.
Qed.
*)