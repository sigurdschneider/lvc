Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status Take.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh MoreList SetOperations.
Require Import Coherence Allocation RenamedApart AllocationAlgo.
Require Import RenamedApart_Liveness LabelsDefined Restrict.

Set Implicit Arguments.


(** ** Bound on the number of registers used *)

Fixpoint largest_live_set (a:ann (set var)) : set var :=
  match a with
    | ann0 gamma => gamma
    | ann1 gamma a => max_set gamma (largest_live_set a)
    | ann2 gamma a b => max_set gamma (max_set (largest_live_set a) (largest_live_set b))
    | annF gamma s b => max_set gamma (max_set (fold_left (fun gamma b => max_set gamma (largest_live_set b)) s ∅)
                                      (largest_live_set b))
  end.

Notation "'list_max' L" := (fold_left max L 0) (at level 50).

Lemma list_max_swap L x
: max (list_max L) x = fold_left max L x.
Proof.
  general induction L; simpl; eauto.
  setoid_rewrite <- IHL; eauto.
  setoid_rewrite Max.max_comm at 4.
  rewrite Max.max_assoc; eauto.
Qed.

Lemma list_max_get L n x
: get L n x
  -> x <= list_max L.
Proof.
  intros. general induction L; eauto; invt get; simpl.
  - rewrite <- list_max_swap. eapply Max.le_max_r.
  - rewrite <- list_max_swap. rewrite <- Max.le_max_l; eauto.
Qed.

Fixpoint size_of_largest_live_set (a:ann (set var)) : nat :=
  match a with
    | ann0 gamma => SetInterface.cardinal gamma
    | ann1 gamma a => max (SetInterface.cardinal gamma) (size_of_largest_live_set a)
    | ann2 gamma a b => max (SetInterface.cardinal gamma)
                       (max (size_of_largest_live_set a)
                            (size_of_largest_live_set b))
    | annF gamma a b => max (SetInterface.cardinal gamma)
                       (max (list_max (List.map size_of_largest_live_set a))
                            (size_of_largest_live_set b))
  end.

Lemma size_of_largest_live_set_live_set al
: SetInterface.cardinal (getAnn al) <= size_of_largest_live_set al.
Proof.
  destruct al; simpl; eauto using Max.le_max_l.
Qed.

Lemma add_minus_single_eq X `{OrderedType X} x s
  : x ∈ s
    -> {x; s \ singleton x} [=] s.
Proof.
  cset_tac. decide (x === a); eauto.
Qed.

Hint Resolve add_minus_single_eq : cset.

Lemma add_union X `{OrderedType X} x s
  : {x; s} [=] singleton x ∪ s.
Proof.
  cset_tac.
Qed.

Lemma minus_incl_incl_union X `{OrderedType X} s t u
  : s \ t ⊆ u
    -> s ⊆ t ∪ u.
Proof.
  cset_tac. decide (a ∈ t); cset_tac; intuition.
Qed.

Hint Resolve minus_incl_incl_union | 10: cset.

Lemma regAssign_assignment_small (ϱ:Map [var,var]) LV s alv ϱ' al n
      (LS:live_sound Functional LV s alv)
      (allocOK:regAssign s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
      (up:lookup_set (findt ϱ 0) (fst (getAnn al)) ⊆ vars_up_to n)
: lookup_set (findt ϱ' 0) (snd (getAnn al)) ⊆ vars_up_to (max (size_of_largest_live_set alv) n).
Proof.
  exploit regAssign_renamedApart_agree; eauto using live_sound.
  rewrite lookup_set_agree in up; eauto. clear H.
  general induction LS; invt renamedApart; simpl in * |- *.
  - assert ( singleton (findt ϱ' 0 x)
                       ⊆ vars_up_to (size_of_largest_live_set al)). {
      eapply regAssign_renamedApart_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      cset_tac. invc H2. eapply in_vars_up_to.
      rewrite least_fresh_small.
      rewrite cardinal_map; eauto.
      rewrite cardinal_difference'.
      rewrite <- size_of_largest_live_set_live_set.
      rewrite singleton_cardinal.
      assert (SetInterface.cardinal (getAnn al) > 0).
      rewrite <- (add_minus_single_eq H1).
      rewrite add_cardinal_2. omega. cset_tac; intuition.
      omega.
      eauto with cset.
      pe_rewrite. eauto with cset.
    }
    exploit IHLS; eauto.
    + pe_rewrite.
      rewrite <- incl. eauto with cset.
    + pe_rewrite.
      instantiate (1:=(max (size_of_largest_live_set al) n)).
      rewrite lookup_set_add; eauto.
      rewrite up.
      rewrite vars_up_to_max, add_union, H2; eauto.
    + pe_rewrite. rewrite H9.
      rewrite lookup_set_add; eauto. rewrite H3.
      repeat rewrite vars_up_to_max.
      rewrite add_union, H2.
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

  - rewrite H7. rewrite lookup_set_empty; cset_tac; intuition; eauto.
  - rewrite H2. rewrite lookup_set_empty; cset_tac; intuition; eauto.
  - assert ( singleton (findt ϱ' 0 x)
                       ⊆ vars_up_to (size_of_largest_live_set al)). {
      eapply regAssign_renamedApart_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      cset_tac. invc H2. eapply in_vars_up_to.
      rewrite least_fresh_small.
      rewrite cardinal_map; eauto.
      rewrite cardinal_difference'.
      rewrite <- size_of_largest_live_set_live_set.
      rewrite singleton_cardinal.
      assert (SetInterface.cardinal (getAnn al) > 0).
      rewrite <- (add_minus_single_eq H1).
      rewrite add_cardinal_2. omega. cset_tac; intuition. omega.
      eauto with cset.
      pe_rewrite. eauto with cset.
    }
    exploit IHLS; eauto.
    + pe_rewrite. eauto with cset.
    + pe_rewrite.
      instantiate (1:=(max (size_of_largest_live_set al) n)).
      rewrite lookup_set_add; eauto.
      rewrite up.
      rewrite vars_up_to_max. rewrite add_union, H2. reflexivity.
    + pe_rewrite. rewrite H10.
      rewrite lookup_set_add, H3, add_union, H2; eauto.
      repeat rewrite vars_up_to_max.
      clear_all. cset_tac.

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
        rewrite cardinal_of_list_unique; eauto.
        etransitivity; [|eapply Max.le_max_l].
        assert (length (fst x1) <= SetInterface.cardinal (getAnn x0)).
        rewrite <- (diff_inter_cardinal (getAnn x0) (of_list (fst x1))).
        assert (getAnn x0 ∩ of_list (fst x1) [=] of_list (fst x1)).
        revert H16; clear_all; cset_tac; intuition.
        rewrite H24. rewrite cardinal_of_list_unique; eauto. omega.
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
        eapply list_union_drop_incl; eauto. congruence.
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
        rewrite cardinal_of_list_unique; eauto.
        assert (length (fst x1) <= SetInterface.cardinal (getAnn x0)).
        rewrite <- (diff_inter_cardinal (getAnn x0) (of_list (fst x1))).
        assert (getAnn x0 ∩ of_list (fst x1) [=] of_list (fst x1)).
        revert H16; clear_all; cset_tac; intuition.
        rewrite H24. rewrite cardinal_of_list_unique; eauto. omega.
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


Lemma regAssign_assignment_small' s ang ϱ ϱ' (alv:ann (set var)) Lv n
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> bounded (live_global ⊝ Lv) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> LabelsDefined.noUnreachableCode s
  -> regAssign s alv ϱ = Success ϱ'
  -> lookup_set (findt ϱ 0) (fst (getAnn ang)) ⊆ vars_up_to n
  -> lookup_set (findt ϱ' 0) (fst (getAnn ang) ∪ snd (getAnn ang)) ⊆ vars_up_to (max (size_of_largest_live_set alv) n).
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply live_sound_overapproximation_F in H0.
  exploit regAssign_assignment_small; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac; intuition.
  rewrite lookup_set_union; intuition.
  rewrite H6.
  rewrite <- lookup_set_agree; eauto using regAssign_renamedApart_agree; intuition.
  rewrite H5. repeat rewrite vars_up_to_max. cset_tac; intuition.
Qed.
