Require Import CMap MapNotations CSet Le Arith.Compare_dec.

Require Import Plus Util Status Take Subset1 Filter.
Require Import Val Var Env IL Annotation Liveness Fresh MoreList SetOperations.
Require Import Coherence Allocation RenamedApart AllocationAlgo InfinitePartition.

Set Implicit Arguments.


(*
Lemma sep_lookup_set c p (G:set var) (ϱ:var -> var) x
      (SEP:sep p G ϱ) (NotIn:x ∉ G)
  : ~ x <= c -> x ∉ lookup_set ϱ G.
Proof.
  destruct SEP as [GT LE].
  intros Gt. unfold lookup_set; intro In.
  eapply map_iff in In; eauto.
  destruct In as [y [In EQ]]. hnf in EQ; subst.
  destruct (part_cover p y).
  - exploit LE; eauto.
  - exploit GT; eauto.
Qed.
 *)

Require Import MapNotations.
(*
Lemma sep_update c p lv (x:var) (ϱ:Map[var,var])
      (SEP : sep c p (lv \ singleton x) (findt ϱ 0))
      (CARD : cardinal (filter (fun x => B[x <= c]) (map (findt ϱ 0) (lv \ singleton x))) < c)
  : sep c p lv (findt (ϱ [-x <- least_fresh_P c (map (findt ϱ 0) (lv \ singleton x)) x -]) 0).
Proof.
  destruct SEP as [GT LE].
  split; intros.
  - unfold findt.
    decide (x === x0).
    + rewrite MapFacts.add_eq_o; eauto.
      rewrite least_fresh_P_gt.
      hnf in e; subst. congruence.
    + rewrite MapFacts.add_neq_o; eauto.
      exploit GT; eauto. cset_tac.
  - unfold findt.
    decide (x === x0).
    + rewrite MapFacts.add_eq_o; eauto.
      rewrite least_fresh_P_le.
      * rewrite (@least_fresh_filter_small c); eauto.
        unfold findt in CARD. unfold var in *. omega.
      * hnf in e; congruence.
    + rewrite MapFacts.add_neq_o; eauto.
      cases; try omega.
      rewrite <- LE; eauto.
      unfold findt. rewrite <- Heq; eauto.
      cset_tac.
Qed.

Lemma sep_nd c G ϱ G'
      (SEP:sep c G (findt ϱ 0)) (Disj: disj G' G)
  : forall x : nat, x > c -> x ∈ G' -> x ∈ map (findt ϱ 0) G -> False.
Proof.
  intros. cset_tac'. destruct SEP as [GT LE].
  decide (x0 <= c).
  - exploit LE; eauto; try omega.
  - exploit GT; eauto. cset_tac'.
    eapply Disj; eauto; congruence.
Qed.

Lemma sep_lookup_list c (G s:set var) (ϱ:var -> var) x
      (SEP:sep c (G \ s) ϱ)
  : x > c -> x ∈ s -> x ∉ map ϱ (G \ s).
Proof.
  destruct SEP as [GT LE].
  intros Gt. intros In InMap.
  eapply map_iff in InMap; eauto.
  destruct InMap as [y [In' EQ]]. hnf in EQ; subst.
  decide (y <= c).
  - exploit LE; eauto. omega.
  - cset_tac.
Qed.

Lemma sep_update_list c ϱ lv Z
      (AL:forall x, x > c -> x ∈ of_list Z -> x ∈ map (findt ϱ 0) (lv \ of_list Z) -> False)
      (ND: NoDupA eq Z)
      (Card: crd c (map (findt ϱ 0) (lv \ of_list Z)) Z)
      (SEP:sep c (lv \ of_list Z) (findt ϱ 0))
  : sep c lv (findt (ϱ [-Z <-- fresh_list_P c (map (findt ϱ 0) (lv \ of_list Z)) Z -]) 0).
Proof.
  destruct SEP as [GT LE].
  eapply sep_agree.
  setoid_rewrite <- map_update_list_update_agree'; eauto with len.
  reflexivity.
  split; intros.
  - decide (x ∈ of_list Z).
    + edestruct update_with_list_lookup_in_list; try eapply i; dcr.
      Focus 2.
      rewrite H4. cset_tac'.
      edestruct fresh_list_get; try eapply H3; inv_get; eauto.
      dcr. inv_get. exfalso; eauto.
      eauto with len.
    + rewrite lookup_set_update_not_in_Z; eauto.
      eapply GT; eauto with cset. cset_tac.
  - decide (x ∈ of_list Z).
    + edestruct update_with_list_lookup_in_list; try eapply i; dcr.
      Focus 2.
      rewrite H4. cset_tac'.
      edestruct fresh_list_get; try eapply H3; inv_get; eauto.
      dcr. inv_get.
      eauto with len.
    + rewrite lookup_set_update_not_in_Z; eauto.
      eapply LE; eauto with cset. cset_tac.
Qed.
*)
(** ** the algorithm produces a locally injective renaming *)

(*


Lemma crd_of_list (c:var) k (LT:k < c) (lv:set var) Z ϱ
      (SEP:sep c (lv \ of_list Z) ϱ)
      (Card:cardinal (filter (fun x => B[x <= c]) lv) <= k)
      (Incl: of_list Z ⊆ lv)
  : crd c (map ϱ (lv \ of_list Z)) Z.
Proof.
  unfold crd. rewrite <- sep_filter_map_comm; eauto.
  rewrite cardinal_map; eauto.
  rewrite filter_difference; [|clear; intuition].
  rewrite cardinal_difference'.
  - unfold var in *.
    assert (cardinal (filter (fun x => B[x <= c]) lv) >=
            cardinal (filter (fun x => B[x <= c]) (of_list Z))). {
      eapply subset_cardinal. eapply subset_filter. clear; intuition. eauto.
    }
    unfold var in *. rewrite of_list_filter_set. omega. clear; intuition.
  - eapply subset_filter; eauto.
Qed.

Lemma sep_update_cmap k c (LE : k < c) x lv lv' (ϱ:Map[var,var])
      (BND:bounded_below c k lv')
      (SEP:sep c (lv \ singleton x) (findt ϱ 0))
      (incl:lv \ singleton x ⊆ lv')
  : sep c lv
        (findt (ϱ [-x <- least_fresh_P c (map (findt ϱ 0)
                                             (lv \ singleton x)) x -]) 0).
  eapply sep_update; eauto.
  hnf in BND. rewrite <- sep_filter_map_comm; eauto.
  rewrite cardinal_map; eauto.
  rewrite incl. unfold var in *. omega.
Qed.

 *)

Lemma injective_on_update_cmap_fresh p lv x (ϱ:Map[var, var])
      (inj : injective_on (lv \ singleton x) (findt ϱ 0))
  : injective_on lv
                 (findt (ϱ [-x <- least_fresh_part p (lookup_set (findt ϱ 0) (lv \ singleton x)) x -]) 0).
Proof.
  eapply injective_on_agree; [| eapply map_update_update_agree].
  eapply injective_on_incl.
  eapply injective_on_fresh; eauto using injective_on_incl.
  eapply least_fresh_part_fresh; eauto.
  eauto with cset.
Qed.

Lemma regAssign_correct p (ϱ:Map [var,var]) ZL Lv s alv ϱ' ra
      (allocOK:regAssign p s alv ϱ = Success ϱ')
      (LS:live_sound FunctionalAndImperative ZL Lv s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (sd:renamedApart s ra)
      (incl:getAnn alv ⊆ fst (getAnn ra))
: locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  general induction LS; simpl in *;
    try monadS_inv allocOK; invt renamedApart;
      pe_rewrite; simpl in *; set_simpl.
  - exploit regAssign_renamedApart_agree; eauto.
    exploit IHLS; eauto.
    + eapply injective_on_update_cmap_fresh; eauto using injective_on_incl.
    + pe_rewrite. eauto with cset.
    + econstructor; eauto.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      rewrite map_update_update_agree; eauto.
      pe_rewrite.
      revert H5 incl; clear_all; cset_tac.
  - exploit regAssign_renamedApart_agree; try eapply EQ; eauto.
    pe_rewrite.
    exploit IHLS1; try eapply EQ; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto using agree_on_incl.
    + pe_rewrite. eauto with cset.
    + econstructor; eauto.
      * exploit regAssign_renamedApart_agree; eauto. pe_rewrite.
        assert (agree_on eq D (findt ϱ 0) (findt ϱ' 0)). {
          etransitivity; eauto.
        }
        eapply injective_on_agree; eauto using agree_on_incl.
      * eapply locally_inj_live_agree; eauto; pe_rewrite;[| eauto with cset].
        exploit regAssign_renamedApart_agree' as AGR;
          try eapply EQ0; simpl; eauto using live_sound.
        pe_rewrite. instantiate (1:=D ∪ Ds) in AGR.
        eapply agree_on_incl; eauto with cset.
  - econstructor; eauto.
  - econstructor; eauto.
  - exploit regAssign_renamedApart_agreeF;
    eauto using regAssign_renamedApart_agree'. reflexivity.
    exploit regAssign_renamedApart_agree;
      try eapply EQ0; simpl; eauto using live_sound.
    instantiate (1:=D) in H4.
    assert (AGR:agree_on _eq lv (findt ϱ 0) (findt x 0)). {
      eapply agree_on_incl; eauto.
      rewrite disj_minus_eq; eauto using disj_D_defVars.
    }
    exploit (IHLS p); try eapply EQ0; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
    + pe_rewrite. etransitivity; eauto.
    + assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                                 disj D (defVars Zs DD')). {
        eapply defVars_disj_D; eauto with cset.
      }
      econstructor; eauto.
      * {
          intros. edestruct get_length_eq; try eapply H6; eauto.
          edestruct (regAssignF_get p (fst (getAnn x0) ∪ snd (getAnn x0)
                                           ∪ getAnn alv)); eauto; dcr.
          rewrite <- map_update_list_update_agree in H20; eauto.
          exploit (H1 _ _ _ H13 H14 p); try eapply H19; eauto.
          - assert (getAnn alv \ of_list (fst Zs) ∪ of_list (fst Zs) [=] getAnn alv).
            edestruct H2; eauto.
            revert H16; clear_all; cset_tac'.
            eapply injective_on_agree.
            Focus 2.
            eapply agree_on_incl.
            eauto. rewrite <- incl_right.
            rewrite disj_minus_eq; eauto.
            eapply disj_lv_take; eauto.
            simpl in *.
            setoid_rewrite <- H16 at 1.
            eapply injective_on_fresh_list; eauto with len.
            + eapply injective_on_incl; eauto.
              eapply H2; eauto.
            + eapply disj_intersection.
              eapply disj_2_incl. eapply fresh_list_stable_spec, least_fresh_part_fresh.
              reflexivity.
            + edestruct H8; eauto.
            + eapply fresh_list_stable_nodup; eauto using least_fresh_part_fresh.
          - eapply lv_incl_fst_ra; eauto.
          - eapply locally_inj_live_agree; try eapply H20; eauto.
            eapply regAssign_renamedApart_agreeF in H17;
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
            + eapply lv_incl_fst_ra; eauto.
          - eauto with len.
        }
      * eapply injective_on_agree; try eapply inj; eauto.
        etransitivity; eapply agree_on_incl; eauto. pe_rewrite. eauto.
Qed.


Require Import Restrict RenamedApart_Liveness LabelsDefined.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_correct]
    above, which we did prove by induction. *)

Lemma regAssign_correct' p s ang ϱ ϱ' (alv:ann (set var)) ZL Lv
  : renamedApart s ang
  -> live_sound Imperative ZL Lv s alv
  -> bounded (Some ⊝ Lv \\ ZL) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> noUnreachableCode isCalled s
  -> injective_on (getAnn alv) (findt ϱ 0)
  -> regAssign p s alv ϱ = Success ϱ'
  -> locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply regAssign_correct; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac.
Qed.