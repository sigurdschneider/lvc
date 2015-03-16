Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh Sim MoreList.
Require Import Coherence Allocation RenamedApart.

Set Implicit Arguments.


Fixpoint linear_scan (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtLet x e s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
        linear_scan s ans (ϱ[x<- xv])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- linear_scan s ans ϱ;
        linear_scan t ant ϱ'
    | stmtApp _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtExtern x f Y s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
      linear_scan s ans (ϱ[x<- xv])
    | stmtFun Z s t, ann2 _ ans ant =>
      let Z' := fresh_list least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\of_list Z)) (length Z) in
      sdo ϱ' <- linear_scan s ans (ϱ[Z <-- Z']);
        linear_scan t ant ϱ'
    | _, _ => Error "linear_scan: Annotation mismatch"
 end.

Lemma linear_scan_renamedApart_agree' i s al ϱ ϱ' LV alv G
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (G \ snd (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  general induction LS; inv sd; simpl in * |- *; try monadS_inv allocOK; eauto.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in X.
    rewrite H9 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv.
    eapply X.
    instantiate (1:=G). rewrite H10.
    revert H5; clear_all; cset_tac; intuition; eauto.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H11 in X. rewrite H12 in X0. simpl in *.
    etransitivity; eapply agree_on_incl; eauto.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in X.
    rewrite H10 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv. eapply X.
    instantiate (1:=G).
    rewrite H11. simpl in *.
    revert H6; clear_all; cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite <- map_update_list_update_agree in X.
    rewrite H9 in X. rewrite H12 in X0. simpl in *.
    etransitivity; try eapply X0.
    eapply agree_on_incl. eapply update_with_list_agree_inv; try eapply X; eauto.
    rewrite fresh_list_length; eauto.
    instantiate (1:=G). rewrite <- H7.
    revert H5; clear_all; cset_tac; intuition; eauto.
    eapply agree_on_incl; eauto. instantiate (1:=G).
    rewrite <- H7. clear_all; cset_tac; intuition; eauto.
    rewrite fresh_list_length; eauto.
Qed.

Lemma linear_scan_renamedApart_agree i s al ϱ ϱ' LV alv
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  eapply agree_on_incl.
  eapply linear_scan_renamedApart_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  exploit renamedApart_disj; eauto.
  revert X. unfold disj.
  clear_all; cset_tac; intuition; eauto.
Qed.

Lemma locally_inj_live_agree s ϱ ϱ' ara alv LV
      (LS:live_sound FunctionalAndImperative LV s alv)
      (sd: renamedApart s ara)
      (inj: locally_inj ϱ s alv)
      (agr: agree_on eq (fst (getAnn ara) ∪ snd (getAnn ara)) ϱ ϱ')
      (incl:getAnn alv ⊆ fst (getAnn ara))
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction inj; invt renamedApart; invt live_sound; simpl in *.
  - econstructor; eauto.
    + eapply IHinj; eauto.
      rewrite H8 in agr.
      rewrite H7; simpl. eapply agree_on_incl; eauto. cset_tac; intuition.
      rewrite H7; simpl.
      rewrite <- incl, <- H13.
      clear_all; cset_tac; intuition.
      decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; try eapply agr.
      rewrite H8. rewrite incl. eapply incl_left.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto. rewrite incl. eapply incl_left.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite incl. eapply incl_left.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    rewrite incl. eapply incl_left.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H8; simpl; eauto.
      eapply agree_on_incl; eauto. rewrite H9.
      clear_all; cset_tac; intuition.
      rewrite H8. simpl. rewrite <- incl, <- H14.
      clear_all; cset_tac; intuition.
      decide (x === a); intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      rewrite incl. eapply incl_left.
  - econstructor; eauto.
    + eapply IHinj1; eauto.
      eapply agree_on_incl; eauto.
      rewrite H7; simpl. rewrite <- H5. clear_all; cset_tac; intuition.
      rewrite H7; simpl. rewrite <- incl. rewrite <- H18.
      clear_all; cset_tac; intuition.
    + eapply IHinj2; eauto.
      eapply agree_on_incl; eauto.
      rewrite H10. simpl. rewrite <- H5. cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl. rewrite <- H19. reflexivity.
    +  eapply injective_on_agree; eauto.
       eapply agree_on_incl; eauto.
       rewrite incl. eapply incl_left.
Qed.

Lemma linear_scan_correct (ϱ:Map [var,var]) LV s alv ϱ' al
      (LS:live_sound FunctionalAndImperative LV s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (allocOK:linear_scan s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
: locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  general induction LS; simpl in *; try monadS_inv allocOK; invt renamedApart;
    eauto 10 using locally_inj, injective_on_incl.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_incl.
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eapply injective_on_incl; eauto. eapply incl_right.
    + rewrite H9. simpl in *. rewrite <- incl, <- H0.
      clear_all; cset_tac; intuition.
      decide (x === a); eauto.
    + exploit linear_scan_renamedApart_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H5 incl; clear_all; cset_tac; intuition. invc H0. eauto.
  - exploit linear_scan_renamedApart_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_renamedApart_agree; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H11 in X. rewrite H12 in X0.
    simpl in *.
    exploit IHLS1; eauto using injective_on_incl.
    rewrite H11; simpl. rewrite <- incl; eauto.
    exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
    eapply injective_on_incl; eauto.
    eapply injective_on_agree; eauto using agree_on_incl.
    rewrite H12; simpl. rewrite <- incl; eauto.
    econstructor; eauto.
    assert (agree_on eq D (findt ϱ 0) (findt ϱ' 0)). etransitivity; eauto.
    eapply injective_on_agree; eauto. eauto using agree_on_incl.
    eapply locally_inj_live_agree. eauto. eauto. eauto.
    rewrite H11; simpl; eauto.
    exploit linear_scan_renamedApart_agree'; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H12 in X3. simpl in *.
    eapply agree_on_incl. eapply X3. instantiate (1:=D ++ Ds).
    pose proof (renamedApart_disj H9). unfold disj in H2.
    rewrite H12 in H2. simpl in *.
    revert H6 H2; clear_all; cset_tac; intuition; eauto.
    rewrite H11; simpl. rewrite <- incl; eauto.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_incl.
      eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eauto.
    + rewrite H10. simpl in *. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a); eauto. right; eapply H0; cset_tac; intuition.
    + exploit linear_scan_renamedApart_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H10 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H6 incl; clear_all; cset_tac; intuition. invc H0. eauto.
  - simpl in *.
    exploit linear_scan_renamedApart_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_renamedApart_agree; try eapply EQ0; simpl; eauto using live_sound.
    rewrite <- map_update_list_update_agree in X.
    exploit IHLS1; eauto.
    + eapply injective_on_agree; [| eapply map_update_list_update_agree].
      eapply injective_on_incl.
      instantiate (1:=getAnn als \ of_list Z ++ of_list Z).
      eapply injective_on_fresh_list; eauto.
      eapply injective_on_incl; eauto.
      rewrite fresh_list_length; eauto.
      eapply fresh_list_spec. eapply least_fresh_spec.
      eapply fresh_list_unique, least_fresh_spec.
      clear_all; cset_tac; intuition.
      decide (a ∈ of_list Z); intuition.
      rewrite fresh_list_length; eauto.
    + rewrite H9. simpl. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition.
      decide (a ∈ of_list Z); intuition.
    + assert (injective_on lv (findt ϱ' 0)).
      eapply injective_on_incl.
      eapply injective_on_agree; try eapply inj; eauto.
      etransitivity.
      eapply agree_on_incl.
      eapply update_with_list_agree_inv; try eapply X; eauto.
      rewrite fresh_list_length; eauto.
      rewrite H9; simpl. rewrite incl.
      revert H5; clear_all; cset_tac; intuition; eauto.
      eapply agree_on_incl; eauto. rewrite H12; simpl; eauto. reflexivity.
      exploit IHLS2; try eapply EQ0; eauto using injective_on_incl.
      * eapply injective_on_incl.
        eapply injective_on_agree; try eapply inj; eauto.
        eapply agree_on_incl.
        eapply update_with_list_agree_inv; try eapply X; eauto.
        rewrite fresh_list_length; eauto.
        rewrite H9; simpl. rewrite incl.
        revert H5; clear_all; cset_tac; intuition; eauto. eauto.
      * rewrite H12. simpl. simpl in *. rewrite <- incl. eauto.
      * econstructor; eauto.
        eapply locally_inj_live_agree; eauto.
        rewrite H9. simpl.
        eapply agree_on_incl.
        eapply linear_scan_renamedApart_agree'; try eapply EQ0; eauto.
        rewrite H12; simpl. instantiate (1:=(of_list Z ++ D) ++ Ds).
        pose proof (renamedApart_disj sd). unfold disj in H3.
        simpl in *. rewrite <- H7 in H3.
        revert H5 H6 H3; clear_all; cset_tac; intuition eauto; eauto.
        rewrite H9. simpl. rewrite <- incl.
        revert H0; clear_all; cset_tac; intuition.
        specialize (H0 a). cset_tac; intuition.
        decide (a ∈ of_list Z); intuition.
    + rewrite fresh_list_length; eauto.
Qed.

Fixpoint largest_live_set (a:ann (set var)) : set var :=
  match a with
    | ann0 gamma => gamma
    | ann1 gamma a => max_set gamma (largest_live_set a)
    | ann2 gamma a b => max_set gamma (max_set (largest_live_set a) (largest_live_set b))
  end.

Fixpoint size_of_largest_live_set (a:ann (set var)) : nat :=
  match a with
    | ann0 gamma => SetInterface.cardinal gamma
    | ann1 gamma a => max (SetInterface.cardinal gamma) (size_of_largest_live_set a)
    | ann2 gamma a b => max (SetInterface.cardinal gamma)
                       (max (size_of_largest_live_set a) (size_of_largest_live_set b))
  end.

Lemma size_of_largest_live_set_live_set al
: SetInterface.cardinal (getAnn al) <= size_of_largest_live_set al.
Proof.
  destruct al; simpl; eauto using Max.le_max_l.
Qed.

Lemma linear_scan_assignment_small (ϱ:Map [var,var]) LV s alv ϱ' al n
      (LS:live_sound Functional LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
      (up:lookup_set (findt ϱ 0) (fst (getAnn al)) ⊆ vars_up_to n)
: lookup_set (findt ϱ' 0) (snd (getAnn al)) ⊆ vars_up_to (max (size_of_largest_live_set alv) n).
Proof.
  exploit linear_scan_renamedApart_agree; eauto using live_sound.
  rewrite lookup_set_agree in up; eauto. clear X.
  general induction LS; invt renamedApart; simpl in * |- *.
  - assert ( singleton (findt ϱ' 0 x)
                       ⊆ vars_up_to (size_of_largest_live_set al)). {
      eapply linear_scan_renamedApart_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      cset_tac. invc H2. eapply in_vars_up_to.
      rewrite least_fresh_small.
      rewrite cardinal_map; eauto.
      rewrite cardinal_difference'.
      rewrite <- size_of_largest_live_set_live_set.
      assert ({x;{}} [=] singleton x) by (cset_tac; intuition).
      rewrite H2. rewrite singleton_cardinal.
      assert (SetInterface.cardinal (getAnn al) > 0).
      assert ({x; getAnn al \ singleton x } [=] getAnn al).
      cset_tac; intuition. invc H4; eauto. decide (x === a); eauto.
      rewrite <- H3. rewrite add_cardinal_2. omega. cset_tac; intuition.
      omega.
      cset_tac; intuition.
      rewrite H9; simpl. cset_tac; intuition.
    }
    exploit IHLS; eauto.
    + rewrite H9. simpl.
      rewrite <- incl. revert H0. clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition. decide (x === a); intuition.
    + rewrite H9. simpl in *.
      instantiate (1:=(max (size_of_largest_live_set al) n)).
      rewrite lookup_set_add; eauto.
      rewrite up.
      rewrite vars_up_to_max. cset_tac; intuition.
    + rewrite H9 in X. simpl in *. rewrite H10.
      rewrite lookup_set_add; eauto. rewrite X.
(*      rewrite <- NPeano.Nat.add_max_distr_r. *)
      repeat rewrite vars_up_to_max.
      cset_tac; intuition; eauto.
  - monadS_inv allocOK.
    exploit IHLS1; eauto.
    rewrite H11; eauto. simpl. rewrite <- incl; eauto.
    rewrite H11; simpl.
    rewrite lookup_set_agree; eauto.
    eapply agree_on_incl; try eapply linear_scan_renamedApart_agree;
    try eapply EQ0; eauto using live_sound.
    rewrite H12; simpl; eauto.
    exploit IHLS2; try eapply EQ0; eauto.
    rewrite H12; simpl. rewrite <- incl; eauto.
    rewrite H12. simpl. eauto.
    rewrite H11 in X; rewrite H12 in X0. simpl in *.
    rewrite <- H7.
    rewrite lookup_set_union; eauto.
    rewrite X0.
    rewrite lookup_set_agree; eauto. rewrite X.
    repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
    clear_all; cset_tac; intuition.
    unfold findt; intuition.
    unfold findt; intuition.
    eapply agree_on_incl.
    symmetry.
    eapply linear_scan_renamedApart_agree'; try eapply EQ0; eauto. rewrite H12; simpl.
    instantiate (1:=Ds). revert H6; clear_all; cset_tac; intuition; eauto.
  - rewrite H7. rewrite lookup_set_empty; cset_tac; intuition; eauto.
  - rewrite H2. rewrite lookup_set_empty; cset_tac; intuition; eauto.
  - assert ( singleton (findt ϱ' 0 x)
                       ⊆ vars_up_to (size_of_largest_live_set al)). {
      eapply linear_scan_renamedApart_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      cset_tac. invc H2. eapply in_vars_up_to.
      rewrite least_fresh_small.
      rewrite cardinal_map; eauto.
      rewrite cardinal_difference'.
      rewrite <- size_of_largest_live_set_live_set.
      assert ({x;{}} [=] singleton x) by (cset_tac; intuition).
      rewrite H2. rewrite singleton_cardinal.
      assert (SetInterface.cardinal (getAnn al) > 0).
      assert ({x; getAnn al \ singleton x } [=] getAnn al).
      cset_tac; intuition. invc H4; eauto. decide (x === a); eauto.
      rewrite <- H3. rewrite add_cardinal_2. omega. cset_tac; intuition.
      omega.
      cset_tac; intuition.
      rewrite H10; simpl. cset_tac; intuition.
    }
    exploit IHLS; eauto.
    + rewrite H10. simpl.
      rewrite <- incl. revert H0. clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition. decide (x === a); intuition.
    + rewrite H10. simpl in *.
      instantiate (1:=(max (size_of_largest_live_set al) n)).
      rewrite lookup_set_add; eauto.
      rewrite up.
      rewrite vars_up_to_max. cset_tac; intuition.
    + rewrite H10 in X. simpl in *.
      rewrite H11. rewrite lookup_set_add, X; eauto.
      repeat rewrite vars_up_to_max.
      cset_tac; intuition.
  - monadS_inv allocOK.
    simpl in *.
    exploit linear_scan_renamedApart_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_renamedApart_agree; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H9 in *. rewrite H12 in *. simpl in *.
    assert (D [=] (of_list Z ++ D) \ of_list Z). {
      revert H5. clear_all; cset_tac; intuition.
      specialize (H0 a). intuition.
    }
   assert (SetInterface.cardinal
             (SetConstructs.map (findt ϱ 0) (getAnn als \ of_list Z)) +
           length Z <= size_of_largest_live_set als). {
      rewrite cardinal_map.
      rewrite <- size_of_largest_live_set_live_set.
      exploit (diff_inter_cardinal (getAnn als) (of_list Z)).
      assert (getAnn als ∩ of_list Z [=] of_list Z).
      revert H; clear_all; cset_tac; intuition.
      rewrite H3 in X1. simpl in *.
      rewrite <- X1.
      rewrite cardinal_of_list_unique. omega. eauto. eauto.
    }
    rewrite <- map_update_list_update_agree in X.
    assert (agree_on eq D (findt ϱ 0) (findt ϱ' 0)). etransitivity; eauto.
    eapply update_with_list_agree_inv in X; try eapply X; eauto.
    rewrite <- H2 in X; eauto. rewrite fresh_list_length; eauto.
    exploit IHLS1; eauto.
    + rewrite H9. simpl. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition.
      decide (a ∈ of_list Z); intuition.
    + rewrite H9. simpl.
      instantiate (1:=(max (size_of_largest_live_set als) n)).
      rewrite <- lookup_set_agree; try eapply X; eauto.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      rewrite <- H2.
      rewrite lookup_set_agree; try eapply H3; eauto.
      rewrite up.
      repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
      rewrite least_fresh_list_small_vars_up_to.
      intros.
      rewrite (vars_up_to_incl H3).
      cset_tac; intuition.
      rewrite fresh_list_length; eauto.
    + exploit IHLS2; eauto.
      * rewrite H12. simpl. simpl in *. rewrite <- incl. eauto.
      * instantiate (1:=(max (size_of_largest_live_set alb) n)).
        rewrite H9 in X1. simpl in *.
        rewrite H12 in *. simpl in *.
        rewrite up.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        eauto.
      * rewrite H9 in X1. rewrite H12 in X2.
        simpl in *.
        rewrite <- H7. repeat rewrite lookup_set_union; eauto.
        rewrite X2. rewrite lookup_set_agree; eauto. rewrite X1.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        erewrite lookup_set_agree with (m':=
          MapUpdate.update_with_list Z (fresh_list least_fresh
                                       (SetConstructs.map (findt ϱ 0) (getAnn als \ of_list Z))
                                       (length Z))
                                     (findt ϱ 0)); eauto.
        rewrite update_with_list_lookup_set_incl; eauto.
        rewrite least_fresh_list_small_vars_up_to.
        rewrite (vars_up_to_incl H3).
        cset_tac; intuition.
        rewrite fresh_list_length; eauto.
        symmetry.
        etransitivity.
        eapply agree_on_incl.
        rewrite map_update_list_update_agree.
        eapply linear_scan_renamedApart_agree'; try eapply EQ; eauto.
        rewrite fresh_list_length; eauto.
        instantiate (1:=of_list Z). rewrite H9. simpl.
        generalize (renamedApart_disj H8).
        rewrite H9. simpl. unfold disj. clear_all; cset_tac; intuition; eauto.
        eapply agree_on_incl.
        eapply linear_scan_renamedApart_agree'; try eapply EQ0; eauto.
        instantiate (1:=of_list Z). rewrite H12. simpl.
        revert H6. clear_all; cset_tac; intuition; eauto.
        symmetry.
        eapply agree_on_incl.
        eapply linear_scan_renamedApart_agree'; try eapply EQ0; eauto.
        instantiate (1:=Ds). rewrite H12. simpl.
        revert H6; clear_all; cset_tac; intuition; eauto.
    + rewrite fresh_list_length; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
