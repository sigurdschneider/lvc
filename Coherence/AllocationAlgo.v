Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh Sim MoreList.
Require Import Coherence Allocation.

Set Implicit Arguments.


Fixpoint linear_scan (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtExp x e s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
        linear_scan s ans (ϱ[x<- xv])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- linear_scan s ans ϱ;
        linear_scan t ant ϱ'
    | stmtGoto _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtExtern x f Y s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
      linear_scan s ans (ϱ[x<- xv])
    | stmtLet Z s t, ann2 _ ans ant =>
      let Z' := fresh_list least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\of_list Z)) (length Z) in
      sdo ϱ' <- linear_scan s ans (ϱ[Z <-- Z']);
        linear_scan t ant ϱ'
    | _, _ => Error "linear_scan: Annotation mismatch"
 end.

Lemma linear_scan_ssa_agree' i s al ϱ ϱ' LV alv G
      (sd:ssa s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (G \ (snd (getAnn al) \ fst (getAnn al))) (findt ϱ 0) (findt ϱ' 0).
Proof.
  general induction LS; inv sd; simpl in * |- *; try monadS_inv allocOK; eauto.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in X.
    rewrite H8 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv.
    eapply X.
    instantiate (1:=G).
    pose proof (ssa_incl H7); eauto. rewrite H8 in H1. simpl in *.
    revert H4 H1; clear_all; cset_tac; intuition.
    invc H. specialize (H1 a). cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite H11 in X. rewrite H12 in X0. simpl in *.
    etransitivity; eapply agree_on_incl; eauto.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
    instantiate (1:=G). rewrite <- H7. clear_all; intro; cset_tac; intuition.
  - exploit IHLS; eauto.
    rewrite <- map_update_update_agree in X.
    rewrite H9 in X; simpl in *.
    eapply agree_on_incl.
    eapply agree_on_update_inv. eapply X.
    instantiate (1:=G).
    pose proof (ssa_incl H8); eauto. rewrite H9 in H1. simpl in *.
    revert H5 H1; clear_all; cset_tac; intuition.
    invc H. specialize (H1 a). cset_tac; intuition.
  - exploit IHLS1; eauto.
    exploit IHLS2; eauto.
    rewrite <- map_update_list_update_agree in X.
    rewrite H9 in X. rewrite H12 in X0. simpl in *.
    etransitivity; try eapply X0.
    eapply agree_on_incl. eapply update_with_list_agree_inv; try eapply X; eauto.
    rewrite fresh_list_length; eauto.
    instantiate (1:=G). rewrite <- H7.
    pose proof (ssa_incl H8); eauto. rewrite H9 in H2. simpl in *.
    revert H5 H2; clear_all; cset_tac; intuition; eauto.
    specialize (H2 a). specialize (H3 a). cset_tac; intuition.
    eapply agree_on_incl; eauto. instantiate (1:=G).
    rewrite <- H7. clear_all; cset_tac; intuition; eauto.
    rewrite fresh_list_length; eauto.
Qed.

Lemma linear_scan_ssa_agree i s al ϱ ϱ' LV alv
      (sd:ssa s al)
      (LS:live_sound i LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  eapply agree_on_incl.
  eapply linear_scan_ssa_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  cset_tac; intuition.
Qed.

Lemma locally_inj_live_agree s ϱ ϱ' ara alv LV
      (LS:live_sound Functional LV s alv)
      (sd: ssa s ara)
      (inj: locally_inj ϱ s alv)
      (agr: agree_on eq (snd (getAnn ara)) ϱ ϱ')
      (incl:getAnn alv ⊆ fst (getAnn ara))
: locally_inj ϱ' s alv.
Proof.
  intros.
  general induction inj; invt ssa; invt live_sound; simpl in *.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H8; simpl; eauto.
      rewrite H8; simpl.
      revert H13 incl; clear_all; cset_tac; intuition.
      specialize (H13 a). decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H7; eauto.
      rewrite H8 in *.
      simpl in *. rewrite incl in H13.
      revert H13 X; clear_all; cset_tac; intuition.
      specialize (X a); specialize (H13 a); cset_tac; intuition; eauto.
      decide (x === a); eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply IHinj1; eauto.
      rewrite H9; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H9; simpl. rewrite <- incl; eauto.
    + eapply IHinj2; eauto.
      rewrite H10; simpl. eapply agree_on_incl; eauto. rewrite <- H5; cset_tac; intuition.
      rewrite H10; simpl. rewrite <- incl; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
  - econstructor; eauto.
    eapply injective_on_agree; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
  - econstructor; eauto.
    + eapply IHinj; eauto. rewrite H9; simpl; eauto.
      rewrite H9; simpl.
      revert H14 incl; clear_all; cset_tac; intuition.
      specialize (H14 a). decide (x === a); cset_tac; intuition.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H8; eauto.
      rewrite H9 in *.
      simpl in *. rewrite incl in H14.
      revert H14 X; clear_all; cset_tac; intuition.
      specialize (X a); specialize (H14 a); cset_tac; intuition; eauto.
      decide (x === a); eauto.
  - econstructor; eauto.
    eapply IHinj1; eauto.
    eapply agree_on_incl; eauto.
    exploit ssa_incl; try eapply H7; eauto. rewrite H8 in X. simpl in *.
    rewrite H8; simpl. rewrite <- H6. cset_tac; intuition.
    rewrite H8; simpl. rewrite <- incl. rewrite <- H19.
    clear_all; cset_tac; intuition.
    eapply IHinj2; eauto.
    eapply agree_on_incl; eauto.
    rewrite H11. simpl. rewrite <- H6. cset_tac; intuition.
    rewrite H11; simpl. rewrite <- incl. rewrite <- H20. reflexivity.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; eauto. simpl in *. etransitivity; eauto.
    + eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto.
      exploit ssa_incl; try eapply H7; eauto. rewrite H8 in X. simpl in *.
      rewrite <- H6. rewrite <- X, <- incl, <- H19.
      clear_all; cset_tac; intuition.
      decide (a ∈ of_list Z); eauto.
Qed.

Lemma linear_scan_correct (ϱ:Map [var,var]) LV s alv ϱ' al
      (LS:live_sound Functional LV s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (allocOK:linear_scan s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:ssa s al)
: locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  general induction LS; simpl in *; try monadS_inv allocOK; invt ssa;
    eauto 10 using locally_inj, injective_on_incl.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_incl.
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eauto.
    + rewrite H8. simpl in *. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a); eauto. left; eapply H0; cset_tac; intuition.
    + exploit linear_scan_ssa_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H8 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H4 incl; clear_all; cset_tac; intuition. invc H0. eauto.
      exploit locally_injective; eauto.
      eapply injective_on_agree; try eapply X0.
      Focus 2.
      eapply agree_on_incl; eauto. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a). intuition.
      left. eapply H0; eauto. cset_tac; intuition.
      eapply injective_on_incl.
      eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_fresh; eauto.
      Focus 2.
      eapply least_fresh_spec.
      eapply injective_on_incl; eauto.
      cset_tac; intuition.
  - exploit linear_scan_ssa_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_ssa_agree; try eapply EQ0; simpl; eauto using live_sound.
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
    exploit linear_scan_ssa_agree'; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H12 in X3. simpl in *. instantiate (1:=Ds) in X3.
    eapply agree_on_incl. eapply X3.
    revert H6; clear_all; cset_tac; intuition. specialize (H6 a). intuition.
    rewrite H11; simpl. rewrite <- incl; eauto.
  - exploit IHLS; try eapply allocOK; eauto.
    + eapply injective_on_incl.
      eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_fresh; eauto using injective_on_incl, least_fresh_spec.
      eauto.
    + rewrite H9. simpl in *. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a); eauto. left; eapply H0; cset_tac; intuition.
    + exploit linear_scan_ssa_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H5 incl; clear_all; cset_tac; intuition. invc H0. eauto.
      exploit locally_injective; eauto.
      eapply injective_on_agree; try eapply X0.
      Focus 2.
      eapply agree_on_incl; eauto. rewrite <- incl.
      revert H0; clear_all; cset_tac; intuition.
      decide (x === a). intuition.
      left. eapply H0; eauto. cset_tac; intuition.
      eapply injective_on_incl.
      eapply injective_on_agree; [| eapply map_update_update_agree].
      eapply injective_on_fresh; eauto.
      Focus 2.
      eapply least_fresh_spec.
      eapply injective_on_incl; eauto.
      cset_tac; intuition.
  - simpl in *.
    exploit linear_scan_ssa_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_ssa_agree; try eapply EQ0; simpl; eauto using live_sound.
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
        eapply linear_scan_ssa_agree'; try eapply EQ0; eauto.
        rewrite H12; simpl. instantiate (1:=Ds).
        revert H6; clear_all; cset_tac; intuition eauto.
        specialize (H6 a); intuition.
        rewrite H9. simpl. rewrite <- incl.
        revert H0; clear_all; cset_tac; intuition.
        specialize (H0 a). cset_tac; intuition.
        decide (a ∈ of_list Z); intuition.
        eapply injective_on_incl. instantiate (1:=(getAnn als \ of_list Z) ∪ of_list Z).
        eapply injective_on_agree with
        (ϱ:=MapUpdate.update_with_list Z
                             (fresh_list least_fresh
                                         (SetConstructs.map (findt ϱ 0) (getAnn als \ of_list Z))
                                         (length Z)) (findt ϱ 0)).
        eapply injective_on_fresh_list; eauto using injective_on_incl.
        rewrite fresh_list_length; eauto.
        eapply fresh_list_spec. eapply least_fresh_spec.
        eapply fresh_list_unique. eapply least_fresh_spec.
        etransitivity. eapply agree_on_incl; eauto.
        rewrite H9; simpl. rewrite H0, incl. cset_tac; intuition.
        eapply agree_on_incl.
        exploit linear_scan_ssa_agree'; try eapply EQ0; simpl; eauto using live_sound.
        rewrite H12; simpl. instantiate (1:=D ++ of_list Z).
        exploit ssa_incl; try eapply H8. rewrite H9 in X3; simpl in *.
        rewrite H0. rewrite incl.
        revert X3 H6; clear_all; cset_tac; intuition.
        specialize (X3 a); specialize (H6 a); cset_tac; intuition.
        clear_all; cset_tac; intuition. decide (a ∈ of_list Z); eauto.
    + rewrite fresh_list_length; eauto.
Qed.


Definition max_set {X} `{OrderedType X} (a:set X) (b:set X) :=
  if [SetInterface.cardinal a < SetInterface.cardinal b] then
    b
  else
    a.

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

Lemma cardinal_difference {X} `{OrderedType X} (s t: set X)
: SetInterface.cardinal (s \ t) <= SetInterface.cardinal s.
Proof.
  erewrite <- (diff_inter_cardinal s t).
  omega.
Qed.

Instance plus_le_morpism
: Proper (Peano.le ==> Peano.le ==> Peano.le) Peano.plus.
Proof.
  unfold Proper, respectful.
  intros. omega.
Qed.

Instance plus_S_morpism
: Proper (Peano.le ==> Peano.le) S.
Proof.
  unfold Proper, respectful.
  intros. omega.
Qed.

Instance cardinal_morph {X} `{OrderedType X}
: Proper (@Subset X _ _ ==> Peano.le)  SetInterface.cardinal.
Proof.
  unfold Proper, respectful; intros.
  eapply subset_cardinal; eauto.
Qed.

Lemma cardinal_map {X} `{OrderedType X} {Y} `{OrderedType Y} (s: set X) (f:X -> Y) `{Proper _ (_eq ==> _eq) f}
: SetInterface.cardinal (SetConstructs.map f s) <= SetInterface.cardinal s.
Proof.
  pattern s. eapply set_induction.
  - intros. repeat rewrite SetProperties.cardinal_1; eauto.
    hnf. intros; intro. eapply map_iff in H3. dcr.
    eapply H2; eauto. eauto.
  - intros.
    erewrite (SetProperties.cardinal_2 H3 H4); eauto.
    decide (f x ∈ SetConstructs.map f s0).
    + assert (SetConstructs.map f s0 [=] {f x; SetConstructs.map f s0}).
      cset_tac; intuition. rewrite <- H6; eauto.
      rewrite <- H2. rewrite H5.
      assert (SetConstructs.map f s' ⊆ {f x; SetConstructs.map f s0}).
      hnf; intros.
      eapply map_iff in H6.
      cset_tac; intuition; eauto.
      specialize (H4 x0). eapply H4 in H8. destruct H8.
      left. rewrite H6; eauto.
      right. eapply map_iff; eauto. eauto.
      rewrite <- H6. omega.
    + rewrite <- H2. erewrite <- cardinal_2; eauto.
      split; intros.
      decide (f x === y); eauto.
      eapply map_iff in H5; dcr.
      right. eapply map_iff; eauto.
      decide (x0 === x). exfalso. eapply n0. rewrite <- e. eauto.
      eexists x0. split; eauto. specialize (H4 x0).
      rewrite H4 in H7. destruct H7; eauto. exfalso. eapply n1; eauto.
      eauto. eapply map_iff; eauto.
      destruct H5.
      eexists x; split; eauto. eapply H4. eauto.
      eapply map_iff in H5; eauto. dcr.
      eexists x0; split; eauto.
      eapply H4. eauto.
Qed.

Lemma cardinal_of_list_unique {X} `{OrderedType X} (Z:list X)
: unique Z -> SetInterface.cardinal (of_list Z) = length Z.
Proof.
  general induction Z; simpl in * |- *.
  - eapply empty_cardinal.
  - dcr. erewrite cardinal_2. rewrite IHZ; eauto.
    intro. eapply H1. eapply InA_in; eauto.
    hnf; cset_tac; intuition.
Qed.

Lemma vars_up_to_incl n m
: n <= m -> vars_up_to n ⊆ vars_up_to m.
Proof.
  intros. general induction H; eauto. reflexivity.
  simpl. rewrite IHle. cset_tac; intuition.
Qed.

Lemma linear_scan_assignment_small (ϱ:Map [var,var]) LV s alv ϱ' al n
      (LS:live_sound Functional LV s alv)
      (allocOK:linear_scan s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:ssa s al)
      (up:lookup_set (findt ϱ' 0) (fst (getAnn al)) ⊆ vars_up_to n)
: lookup_set (findt ϱ' 0) (snd (getAnn al)) ⊆ vars_up_to (max (size_of_largest_live_set alv + 1) n).
Proof.
  general induction LS; invt ssa; simpl in * |- *.
  - exploit IHLS; eauto.
    + rewrite H8. simpl.
      rewrite <- incl. revert H0. clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition. decide (x === a); intuition.
    + rewrite H8. simpl in *.
      instantiate (1:=(max (size_of_largest_live_set al + 1) n)).
      rewrite lookup_set_union; try now (unfold findt; intuition).
      rewrite up. rewrite lookup_set_singleton; try now (unfold findt; intuition).
      eapply linear_scan_ssa_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      assert ({least_fresh (SetConstructs.map (findt ϱ 0) (getAnn al \ {x; {}})); {} }
                ⊆ vars_up_to (size_of_largest_live_set al + 1)).
      cset_tac. invc H1. eapply in_vars_up_to'.
      etransitivity; [eapply least_fresh_small|].
      etransitivity; [eapply cardinal_map|]. unfold findt; intuition.
      etransitivity; [eapply cardinal_difference|].
      eapply size_of_largest_live_set_live_set.
      rewrite vars_up_to_max, H1. cset_tac; intuition.
      rewrite H8; simpl. cset_tac; intuition.
    + rewrite H8 in X. simpl in *.
      rewrite X.
      rewrite <- NPeano.Nat.add_max_distr_r.
      repeat rewrite vars_up_to_max.
      cset_tac; intuition.
  - monadS_inv allocOK.
    exploit IHLS1; eauto.
    rewrite H11; eauto. simpl. rewrite <- incl; eauto.
    rewrite H11; simpl.
    rewrite lookup_set_agree; eauto.
    eapply agree_on_incl; try eapply linear_scan_ssa_agree; try eapply EQ0; eauto using live_sound.
    rewrite H12; simpl; eauto. reflexivity.
    exploit IHLS2; try eapply EQ0; eauto.
    rewrite H12; simpl. rewrite <- incl; eauto.
    rewrite H12. simpl. eauto.
    rewrite H11 in X; rewrite H12 in X0. simpl in *.
    rewrite <- H7.
    rewrite lookup_set_union.
    rewrite X0.
    rewrite lookup_set_agree. rewrite X.
    repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
    clear_all; cset_tac; intuition.
    unfold findt; intuition.
    unfold findt; intuition.
    eapply agree_on_incl.
    symmetry.
    eapply linear_scan_ssa_agree'; try eapply EQ0; eauto. rewrite H12; simpl.
    instantiate (1:=Ds). revert H6; clear_all; cset_tac; intuition.
    specialize (H6 a). intuition.
    unfold findt; intuition.
  - rewrite <- H7. rewrite up. rewrite vars_up_to_max.
    cset_tac; intuition.
  - rewrite <- H2. rewrite up. rewrite vars_up_to_max.
    cset_tac; intuition.
  - exploit IHLS; eauto.
    + rewrite H9. simpl.
      rewrite <- incl. revert H0. clear_all; cset_tac; intuition.
      specialize (H0 a). cset_tac; intuition. decide (x === a); intuition.
    + rewrite H9. simpl in *.
      instantiate (1:=(max (size_of_largest_live_set al + 1) n)).
      rewrite lookup_set_union; try now (unfold findt; intuition).
      rewrite up. rewrite lookup_set_singleton; try now (unfold findt; intuition).
      eapply linear_scan_ssa_agree in allocOK; eauto.
      rewrite <- allocOK. unfold findt at 1.
      rewrite MapFacts.add_eq_o; eauto.
      assert ({least_fresh (SetConstructs.map (findt ϱ 0) (getAnn al \ {x; {}})); {} }
                ⊆ vars_up_to (size_of_largest_live_set al + 1)).
      cset_tac. invc H1. eapply in_vars_up_to'.
      etransitivity; [eapply least_fresh_small|].
      etransitivity; [eapply cardinal_map|]. unfold findt; intuition.
      etransitivity; [eapply cardinal_difference|].
      eapply size_of_largest_live_set_live_set.
      rewrite vars_up_to_max, H1. cset_tac; intuition.
      rewrite H9; simpl. cset_tac; intuition.
    + rewrite H9 in X. simpl in *.
      rewrite X.
      rewrite <- NPeano.Nat.add_max_distr_r.
      repeat rewrite vars_up_to_max.
      cset_tac; intuition.
  - monadS_inv allocOK.
    simpl in *.
    exploit linear_scan_ssa_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit linear_scan_ssa_agree; try eapply EQ0; simpl; eauto using live_sound.
    rewrite H9 in *. rewrite H12 in *. simpl in *.
    assert (D [=] (of_list Z ++ D) \ of_list Z). {
      revert H5. clear_all; cset_tac; intuition.
      specialize (H0 a). intuition.
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
    + assert (Proper (_eq ==> _eq) (findt ϱ 0)) by intuition.
      rewrite H9. simpl.
      instantiate (1:=(max (size_of_largest_live_set als + 1) n)).
      rewrite <- lookup_set_agree; try eapply X.
      rewrite lookup_set_update_with_list_in_union_length.
      rewrite <- H2.
      rewrite lookup_set_agree; try eapply H3.
      rewrite up.
      repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
      rewrite least_fresh_list_small_vars_up_to.
      intros.
      assert (SetInterface.cardinal
        (SetConstructs.map (findt ϱ 0) (getAnn als \ of_list Z)) +
              length Z <= size_of_largest_live_set als + 1). {
        rewrite cardinal_map.
        rewrite <- size_of_largest_live_set_live_set.
        exploit (diff_inter_cardinal (getAnn als) (of_list Z)).
        assert (getAnn als ∩ of_list Z [=] of_list Z).
        revert H; clear_all; cset_tac; intuition.
        rewrite H11 in X1. simpl in *.
        rewrite <- X1.
        rewrite cardinal_of_list_unique. omega. eauto.
        unfold findt; intuition.
      }
      rewrite (vars_up_to_incl H11).
      cset_tac; intuition.
      unfold findt; intuition.
      unfold findt; intuition.
      unfold findt; intuition.
      rewrite fresh_list_length; eauto.
      intuition.
      unfold findt; intuition.
    + exploit IHLS2; eauto.
      * rewrite H12. simpl. simpl in *. rewrite <- incl. eauto.
      * instantiate (1:=(max (size_of_largest_live_set alb + 1) n)).
        rewrite H9 in X1. simpl in *.
        rewrite H12 in *. simpl in *.
        rewrite up.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        eauto.
      * rewrite H9 in X1. rewrite H12 in X2.
        simpl in *.
        rewrite <- H7. rewrite lookup_set_union.
        rewrite X2. rewrite lookup_set_agree. rewrite X1.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        clear_all; cset_tac; intuition.
        unfold findt; intuition.
        unfold findt; intuition.
        eapply agree_on_incl. symmetry.
        eapply linear_scan_ssa_agree'; try eapply EQ0; eauto.
        instantiate (1:=Ds). rewrite H12; simpl.
        revert H6; clear_all; cset_tac; intuition. specialize (H6 a); intuition.
        unfold findt; intuition.
    + rewrite fresh_list_length; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
