Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map CMap Status.
Require Import Val Var Env EnvTy IL Annotation Liveness Fresh MoreList SetOperations.
Require Import Coherence Allocation RenamedApart.

Set Implicit Arguments.

(** * SSA-based register assignment formulated for IL *)


Definition regAssignF
           (regAssign : stmt -> ann (set var) -> Map [var, var] -> status (Map [var, var]))
  := fix regAssignF
           (ϱ:Map [var, var]) (F:list (list var * stmt)) (ans: list (ann (set var)))
: status (Map [var, var]) :=
  match F, ans with
    | Zs::F, a::ans =>
      let Z := fst Zs in let s := snd Zs in
      let Z' := fresh_list least_fresh (SetConstructs.map (findt ϱ 0) (getAnn a\of_list Z)) (length Z) in
      sdo ϱ' <- regAssign s a (ϱ[Z <-- Z']);
        regAssignF ϱ' F ans

    | nil, nil => Success ϱ
    | _, _ => Error "regAssignF: function annotation mismatch"
  end.

Fixpoint regAssign (st:stmt) (an: ann (set var)) (ϱ:Map [var, var])
  : status (Map [var, var]) :=
 match st, an with
    | stmtLet x e s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
        regAssign s ans (ϱ[x<- xv])
    | stmtIf _ s t, ann2 lv ans ant =>
      sdo ϱ' <- regAssign s ans ϱ;
        regAssign t ant ϱ'
    | stmtApp _ _, ann0 _ => Success ϱ
    | stmtReturn _, ann0 _ => Success ϱ
    | stmtExtern x f Y s, ann1 lv ans =>
      let xv := least_fresh (SetConstructs.map (findt ϱ 0) (getAnn ans\{{x}})) in
      regAssign s ans (ϱ[x<- xv])
    | stmtFun F t, annF _ ans ant =>
      sdo ϱ' <- regAssignF regAssign ϱ F ans;
        regAssign t ant ϱ'
    | _, _ => Error "regAssign: Annotation mismatch"
 end.

(** The algorithm only changes bound variables in the mapping [ϱ] *)

Lemma regAssign_renamedApart_agreeF G F ans als ϱ ϱ'
      (allocOK:regAssignF regAssign ϱ F als = Success ϱ')
      (REN:forall (n : nat) (Zs : params * stmt) (a : ann (set var * set var)),
             get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (LEN1:length F = length als)
      (LEN2:length F = length ans)
      (IH:(forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
             get F n Zs ->
             get als n a ->
             forall (al : ann (set var * set var)) (ϱ0 ϱ'0 : Map  [var, var])
               (G0 : set var),
               renamedApart (snd Zs) al ->
               regAssign (snd Zs) a ϱ0 = Success ϱ'0 ->
               agree_on eq (G0 \ snd (getAnn al)) (findt ϱ0 0) (findt ϱ'0 0)))
: forall G' : set var,
    list_union zip defVars F ans[<=]G' ->
    agree_on eq (G \ G') (findt ϱ 0) (findt ϱ' 0).
Proof.
 intros G' INCL.
 length_equify. general induction LEN1; inv LEN2; simpl in * |- *; try monadS_inv allocOK; eauto.
 exploit IHLEN1; eauto using get. etransitivity; try eapply INCL.
 norm_lunion. eauto with cset.
 exploit IH; eauto using get.
 rewrite <- map_update_list_update_agree in X1; eauto.
 etransitivity; try eapply X0.
 eapply agree_on_incl. eapply update_with_list_agree_inv; try eapply X1; eauto.
 instantiate (1:=G). rewrite minus_union.
 eapply incl_minus_lr; eauto.
 erewrite <- INCL. norm_lunion. unfold defVars. eauto with cset.
Qed.

Lemma regAssign_renamedApart_agree' i s al ϱ ϱ' LV alv G
      (allocOK:regAssign s alv ϱ = Success ϱ')
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
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
  - exploit IHLS; eauto.
    etransitivity; [| eapply agree_on_incl; try eapply X].
    eapply agree_on_incl; try eapply regAssign_renamedApart_agreeF; eauto; try reflexivity.
    rewrite <- H13. eapply incl_minus_lr; eauto; try reflexivity.
    eapply incl_minus_lr; try reflexivity. rewrite <- H13. pe_rewrite; eauto with cset.
Qed.

Lemma regAssign_renamedApart_agree i s al ϱ ϱ' LV alv
      (sd:renamedApart s al)
      (LS:live_sound i LV s alv)
      (allocOK:regAssign s alv ϱ = Success ϱ')
: agree_on eq (fst (getAnn al)) (findt ϱ 0) (findt ϱ' 0).
Proof.
  eapply agree_on_incl.
  eapply regAssign_renamedApart_agree'; eauto.
  instantiate (1:=fst (getAnn al)).
  exploit renamedApart_disj; eauto.
  revert X. unfold disj.
  clear_all; cset_tac; intuition; eauto.
Qed.

Fixpoint take n X (L:list X) :=
  match n, L with
    | S n, x::L => x::take n L
    | _, _ => nil
  end.

Ltac eadmit := exfalso; clear_all; admit.

Lemma regAssignF_get G F ans alv n Zs a ϱ ϱ' an Lv i D Dt lv
: regAssignF regAssign ϱ F alv = Success ϱ'
  -> (forall n Zs a, get F n Zs -> get ans n a -> renamedApart (snd Zs) a)
  -> (forall n Zs a, get F n Zs ->
               get alv n a ->
               live_sound i Lv (snd Zs) a)
  -> (forall (n : nat) (Zs : params * stmt) (a : ann (set var)),
       get F n Zs ->
       get alv n a ->
       of_list (fst Zs)[<=]getAnn a /\ getAnn a \ of_list (fst Zs)[<=]lv)
  -> (forall n Zs a, get F n Zs -> get ans n a -> disj D (defVars Zs a))
  -> Indexwise.indexwise_R (funConstr D Dt) F ans
  -> pairwise_ne disj (zip defVars F ans)
  -> get F n Zs
  -> get alv n a
  -> get ans n an
  -> lv ⊆ D
  -> exists ϱ1 ϱ2, regAssign (snd Zs) a ϱ1 = Success ϱ2
             /\ regAssignF regAssign ϱ2 (drop (S n) F) (drop (S n) alv) = Success ϱ'
             /\ agree_on eq (G \ list_union (zip defVars (take n F) (take n ans)))
                        (findt (ϱ[fst Zs <-- fresh_list least_fresh
                                      (SetConstructs.map (findt ϱ 0) (getAnn a \ of_list (fst Zs)))
                                      (length (fst Zs))]) 0)
                        (findt ϱ1 0).
Proof.
  intros EQ REN LV LVINC DDISJ FUNC PWDISJ GET1 GET2 GET3 incl.
  general induction GET1; inv GET2; inv GET3; simpl in * |- *; monadS_inv EQ; eauto.
  - do 2 eexists; split; eauto. split. rewrite EQ0. reflexivity. reflexivity.
  - exploit (IHGET1 G); hnf; intros; eauto using get; dcr.
    do 2 eexists; split; eauto. split; eauto.
    rewrite EQ0. simpl. rewrite EQ1; eauto.
    etransitivity; eapply agree_on_incl; eauto; try reflexivity.
    + repeat rewrite <- map_update_list_update_agree; eauto.
      erewrite least_fresh_list_ext; eauto.
      eapply update_with_list_agree; eauto.
      eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
      rewrite <- map_update_list_update_agree in EQ0; eauto.
      eapply update_with_list_agree_inv in EQ0; eauto.
      eapply agree_on_incl; eauto. norm_lunion.
      instantiate (1:=G \ list_union zip defVars (take n xl) (take n xl1)).
      unfold defVars at 1. clear_all; cset_tac; intuition.
      eapply lookup_set_agree; eauto.
      eapply regAssign_renamedApart_agree' in EQ0; eauto using get.
      rewrite <- map_update_list_update_agree in EQ0; eauto.
      eapply update_with_list_agree_inv in EQ0; eauto.
      eapply agree_on_incl; eauto.
      instantiate (1:=getAnn a \ of_list (fst x)).
      setoid_rewrite minus_union at 1.
      assert (disj (getAnn a \ of_list (fst x)) (snd (getAnn x'1) ∪ of_list (fst x'))). {
        exploit PWDISJ; [| eauto using get| econstructor 2; eapply zip_get; eauto|].
        omega. unfold defVars in X.
        exploit (LVINC (S n)); eauto using get; dcr.
        rewrite H5. rewrite incl. rewrite union_comm. eapply DDISJ; eauto using get.
      }
      setoid_rewrite disj_minus_eq at 2; eauto.
    + norm_lunion. clear_all; cset_tac; intuition.
Qed.

Lemma get_take_lt k X (L:list X) n x
: get (take k L) n x -> n < k.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  - inv H; eauto; try omega.
    + exploit IHk; eauto. omega.
Qed.

Lemma get_take k X (L:list X) n x
: get (take k L) n x -> get L n x.
Proof.
  intros. general induction k; destruct L; simpl in *; isabsurd.
  inv H; eauto using get.
Qed.

Lemma defVars_take_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (take n F) (take n ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros.
  inv_zip H2.
  eapply H. Focus 3. eapply zip_get; eauto.
  Focus 2.
  eapply zip_get; eauto using get_take.
  exploit get_take_lt; eauto. omega.
Qed.

Lemma defVars_drop_disj F ans n Zs a
:  pairwise_ne disj (zip defVars F ans)
   -> get F n Zs
   -> get ans n a
   -> disj (defVars Zs a) (list_union zip defVars (drop (S n) F) (drop (S n) ans)).
Proof.
  intros.
  symmetry. rewrite <- list_union_disjunct; intros.
  inv_zip H2.
  eapply H. Focus 3. eapply zip_get; eauto.
  Focus 2. eapply zip_get; eauto using get_drop. omega.
Qed.

Lemma defVars_disj_D F ans D Dt D'
      (D'def:list_union zip defVars F ans ++ Dt[=]D')
      (Ddisj: disj D D')
: forall n  DD' Zs, get F n Zs -> get ans n DD' ->
               disj D (defVars Zs DD').
Proof.
  intros.
  eapply disj_2_incl; eauto. rewrite <- D'def.
  eapply incl_union_left. eapply incl_list_union; eauto.
  eapply zip_get; eauto. reflexivity.
Qed.

(** ** the algorithm produces a locally injective renaming *)

Lemma regAssign_correct (ϱ:Map [var,var]) LV s alv ϱ' al
      (LS:live_sound FunctionalAndImperative LV s alv)
      (inj:injective_on (getAnn alv) (findt ϱ 0))
      (allocOK:regAssign s alv ϱ = Success ϱ')
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
    + exploit regAssign_renamedApart_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H9 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H5 incl; clear_all; cset_tac; intuition. invc H0. eauto.
  - exploit regAssign_renamedApart_agree; try eapply EQ; simpl; eauto using live_sound.
    exploit regAssign_renamedApart_agree; try eapply EQ0; simpl; eauto using live_sound.
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
    exploit regAssign_renamedApart_agree'; try eapply EQ0; simpl; eauto using live_sound.
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
    + exploit regAssign_renamedApart_agree; try eapply allocOK; simpl; eauto using live_sound.
      rewrite H10 in *.
      simpl in *.
      econstructor. eauto using injective_on_incl.
      eapply injective_on_agree; try eapply inj.
      eapply agree_on_incl.
      eapply agree_on_update_inv.
      etransitivity. eapply map_update_update_agree.
      eapply X0.
      revert H6 incl; clear_all; cset_tac; intuition. invc H0. eauto.
  -
    exploit regAssign_renamedApart_agreeF; eauto using regAssign_renamedApart_agree'. reflexivity.
    exploit regAssign_renamedApart_agree; try eapply EQ0; simpl; eauto using live_sound.
    exploit IHLS; eauto.
    + eapply injective_on_incl; eauto.
      eapply injective_on_agree; eauto.
      eapply agree_on_incl; eauto. instantiate (1:=D).
      rewrite disj_minus_eq; eauto. simpl in *.
      symmetry. rewrite <- list_union_disjunct.
      intros. inv_zip H4. edestruct H8; eauto; dcr.
      unfold defVars. rewrite meet_comm. eapply disj_app; split; eauto.
      symmetry; eauto.
      exploit H7; eauto. eapply renamedApart_disj in X1.
      eapply disj_1_incl; eauto. rewrite H14. eauto with cset.
    + pe_rewrite. etransitivity; eauto.
    +
      assert (DDISJ:forall n  DD' Zs, get F n Zs -> get ans n DD' ->
                              disj D (defVars Zs DD')).
      {
        eapply renamedApart_disj in sd. eauto using defVars_disj_D.
      }

      econstructor; eauto.
      * intros. edestruct get_length_eq; try eapply H6; eauto.
        edestruct (regAssignF_get (fst (getAnn x0) ++ snd (getAnn x0) ++ getAnn alv)); eauto; dcr.
        rewrite <- map_update_list_update_agree in H18; eauto.
        exploit H1; try eapply H16; eauto.
        assert (getAnn alv \ of_list (fst Zs) ++ of_list (fst Zs) [=] getAnn alv).
        edestruct H2; eauto. revert H14; clear_all; cset_tac; intuition.
        decide (a ∈ of_list (fst Zs)); eauto.
        eapply injective_on_agree.
        Focus 2.
        eapply agree_on_incl.
        eauto. do 2 rewrite <- incl_right.
        rewrite disj_minus_eq; eauto.
        eapply renamedApart_disj in sd.
        simpl in *.
        rewrite <- H14. symmetry. rewrite disj_app. split; symmetry.
        eapply disj_1_incl. eapply disj_2_incl. eapply sd.
        rewrite <- H13. eapply incl_union_left.
        hnf; intros. eapply list_union_get in H17. destruct H17. dcr.
        inv_zip H17.
        eapply incl_list_union. eapply zip_get.
        eapply get_take; eauto. eauto using get_take. reflexivity. eauto.
        cset_tac; intuition.
        edestruct H2; eauto; dcr. rewrite <- incl. eauto.
        eapply disj_1_incl.
        eapply defVars_take_disj; eauto. unfold defVars.
        eauto with cset.
        setoid_rewrite <- H14 at 1.
        eapply injective_on_fresh_list; eauto.
        eapply injective_on_incl; eauto.
        eapply H2; eauto.
        eapply disj_2_incl. eapply fresh_list_spec. eapply least_fresh_spec.
        reflexivity.
        edestruct H8; eauto.
        eapply fresh_list_unique, least_fresh_spec.
        edestruct H8; eauto; dcr. rewrite H14.
        exploit H2; eauto; dcr. rewrite incl in H20.
        revert H20; clear_all; cset_tac; intuition.
        decide (a ∈ of_list (fst Zs)); intuition.
        eapply locally_inj_live_agree; try eapply X2; eauto.
        eapply regAssign_renamedApart_agreeF in H15;
          eauto using regAssign_renamedApart_agree', get_drop, drop_length_stable; try reflexivity.
        eapply regAssign_renamedApart_agree' in EQ0; simpl; eauto using live_sound.
        etransitivity; eapply agree_on_incl; eauto.
        rewrite disj_minus_eq. reflexivity.
        {
          edestruct H8; eauto; dcr. rewrite H14.
          rewrite union_comm. rewrite <- union_assoc.
          symmetry; rewrite disj_app; split; symmetry.
          - eapply disj_1_incl. eapply defVars_drop_disj; eauto.
            unfold defVars. eauto with cset.
          - eapply renamedApart_disj in sd; simpl in sd.
            eapply disj_2_incl; eauto.
            rewrite <- H13. eapply incl_union_left.
            rewrite <- drop_zip; eauto.
            eapply list_union_drop_incl; eauto.
        }
        pe_rewrite.
        rewrite disj_minus_eq. reflexivity.
        {
          edestruct H8; eauto; dcr. rewrite H14.
          rewrite union_comm. rewrite <- union_assoc.
          symmetry; rewrite disj_app; split; symmetry.
          rewrite union_comm; eauto.
          eapply renamedApart_disj in H10. pe_rewrite. eapply H10.
        }
        edestruct H8; eauto; dcr. rewrite H14.
        exploit H2; eauto; dcr. rewrite incl in H20.
        revert H20; clear_all; cset_tac; intuition.
        decide (a ∈ of_list (fst Zs)); intuition.
      * eapply injective_on_agree; try eapply inj; eauto.
        etransitivity; eapply agree_on_incl; eauto.
        rewrite disj_minus_eq; eauto. simpl in *.
        symmetry. rewrite <- list_union_disjunct.
        intros. inv_zip H4. edestruct H8; eauto; dcr.
        unfold defVars. rewrite meet_comm. eapply disj_app; split; eauto.
        symmetry; eauto.
        exploit H7; eauto. eapply renamedApart_disj in X2.
        eapply disj_1_incl; eauto. rewrite H14. eauto with cset.
        pe_rewrite. eauto.
Qed.


Require Import Restrict RenamedApart_Liveness.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_correct]
    above, which we did prove by induction. *)

Lemma regAssign_correct' s ang ϱ ϱ' (alv:ann (set var)) Lv
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> bounded (live_globals Lv) (fst (getAnn ang))
  -> ann_R Subset1 alv ang
  -> LabelsDefined.noUnreachableCode s
  -> injective_on (getAnn alv) (findt ϱ 0)
  -> regAssign s alv ϱ = Success ϱ'
  -> locally_inj (findt ϱ' 0) s alv.
Proof.
  intros.
  eapply renamedApart_live_imperative_is_functional in H0; eauto using bounded_disjoint, renamedApart_disj, meet1_Subset1, live_sound_annotation, renamedApart_annotation.
  eapply regAssign_correct; eauto using locally_inj_subset, meet1_Subset, live_sound_annotation, renamedApart_annotation.
  eapply ann_R_get in H2. destruct (getAnn ang); simpl; cset_tac; intuition.
Qed.

Require Import LabelsDefined.

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
  setoid_rewrite NPeano.Nat.max_comm at 4.
  rewrite NPeano.Nat.max_assoc; eauto.
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

Lemma regAssign_assignment_small (ϱ:Map [var,var]) LV s alv ϱ' al n
      (LS:live_sound Functional LV s alv)
      (allocOK:regAssign s alv ϱ = Success ϱ')
      (incl:getAnn alv ⊆ fst (getAnn al))
      (sd:renamedApart s al)
      (up:lookup_set (findt ϱ 0) (fst (getAnn al)) ⊆ vars_up_to n)
: lookup_set (findt ϱ' 0) (snd (getAnn al)) ⊆ vars_up_to (max (size_of_largest_live_set alv) n).
Proof.
  exploit regAssign_renamedApart_agree; eauto using live_sound.
  rewrite lookup_set_agree in up; eauto. clear X.
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
        rewrite X0.
        rewrite lookup_set_agree; eauto. rewrite X.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        clear_all; cset_tac; intuition.
        unfold findt; intuition.
        unfold findt; intuition.
        eapply agree_on_incl.
        symmetry.
        eapply regAssign_renamedApart_agree'; try eapply EQ0; eauto. rewrite H12; simpl.
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
  - repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
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
      rewrite H22. rewrite <- incl.
      revert H20. clear_all; cset_tac; intuition.
      decide (a ∈ of_list (fst x1)); intuition.
      rewrite H22. instantiate (1:=max (list_max List.map size_of_largest_live_set als) n).
      rewrite lookup_set_union; eauto.
      eapply union_incl_split.
      {
        rewrite <- map_update_list_update_agree in H21; eauto.
        exploit regAssign_renamedApart_agree'; try eapply H19; eauto.
        rewrite <- lookup_set_agree.
        Focus 4. etransitivity; eapply agree_on_incl. eapply H21.
        rewrite disj_minus_eq; [ | eauto using defVars_take_disj].
        unfold defVars. eauto. eauto.
        rewrite disj_minus_eq; eauto.
        exploit H7; eauto. eapply renamedApart_disj in X0.
        eapply disj_1_incl; eauto. rewrite H22.
        rewrite <- incl. revert H20.
        clear_all; cset_tac; intuition.
        decide (a ∈ of_list (fst x1)); intuition.
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
        revert H17; clear_all; cset_tac; intuition.
        rewrite H23 at 1. rewrite cardinal_of_list_unique; eauto. omega.
        etransitivity;[| eapply list_max_get; eauto; eapply map_get_1; eauto].
        rewrite <- size_of_largest_live_set_live_set. omega.
        eauto. intuition. eauto. intuition. intuition.
      }
      {
        exploit regAssign_renamedApart_agreeF; eauto using drop_get, get_drop, drop_length_stable,
                                               regAssign_renamedApart_agree'. reflexivity.
        rewrite vars_up_to_max. eapply incl_union_right.
        exploit regAssign_renamedApart_agree'; try eapply EQ0; eauto.
        rewrite lookup_set_agree; try eapply up; intuition.
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
          rewrite <- map_update_list_update_agree in H21; eauto.
          exploit regAssign_renamedApart_agreeF; eauto using drop_get, get_drop, drop_length_stable,
                                                 regAssign_renamedApart_agree'. reflexivity.
          exploit regAssign_renamedApart_agree'; try eapply EQ0; eauto.
          exploit regAssign_renamedApart_agree'; eauto.
          rewrite <- lookup_set_agree.
          Focus 4.
          etransitivity; [| eapply agree_on_incl; try eapply X1].
          etransitivity; [| eapply agree_on_incl; try eapply X0].
          etransitivity; [| eapply agree_on_incl; try eapply X2].
          eapply agree_on_incl; try apply H21.
          rewrite disj_minus_eq; [ | eauto using defVars_take_disj].
          unfold defVars. eapply incl_left.
          rewrite disj_minus_eq; eauto.
          exploit H7; eauto. eapply renamedApart_disj in X3.
          eapply disj_1_incl; eauto. rewrite H22.
          rewrite <- incl. revert H20. clear_all; cset_tac; intuition.
          decide (a ∈ of_list (fst x1)); intuition.
          rewrite disj_minus_eq; [ | eauto using defVars_drop_disj].
          eapply incl_left.
          rewrite disj_minus_eq; eauto.
          pe_rewrite.
          assert (getAnn x0 [=] getAnn x0 \ of_list (fst x1) ∪ of_list (fst x1)).
          revert H17; clear_all; cset_tac; intuition.
          decide (a ∈ of_list (fst x1)); eauto. rewrite H23.
          symmetry. eapply disj_app; split. symmetry.
          eapply disj_1_incl. eapply disj_2_incl.
          eapply renamedApart_disj in sd. eapply sd. simpl.
          rewrite <- H13. eapply incl_right.
          simpl. rewrite H20; eauto.
          symmetry.
          eapply renamedApart_disj in H10. pe_rewrite.
          eapply disj_1_incl; eauto. eapply incl_left.
          rewrite lookup_set_update_with_list_in_union_length; eauto.
          rewrite diff_subset_equal. rewrite lookup_set_empty.
          clear_all; cset_tac; intuition. intuition. reflexivity.
          intuition. intuition.
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
        revert H17; clear_all; cset_tac; intuition.
        rewrite H23 at 1. rewrite cardinal_of_list_unique; eauto. omega.
        etransitivity;[| eapply list_max_get; eauto; eapply map_get_1; eauto].
        rewrite <- size_of_largest_live_set_live_set. omega.
        eauto.
      * erewrite lookup_set_agree; eauto. erewrite X; eauto.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max); eauto.
        setoid_rewrite vars_up_to_incl at 1. instantiate (1:=list_max List.map size_of_largest_live_set als).
        clear_all; cset_tac; intuition.
        eapply list_max_get. eapply map_get_1; eauto.
        eapply regAssign_renamedApart_agree' in EQ0; eauto. symmetry in EQ0.
        etransitivity; eapply agree_on_incl; eauto.
        pe_rewrite. rewrite disj_minus_eq. reflexivity. eauto with cset.
        symmetry.
        eapply regAssign_renamedApart_agreeF; intros; eauto using get_drop, drop_length_stable.
        eapply regAssign_renamedApart_agree'; eauto using get_drop. reflexivity.
        rewrite disj_minus_eq. reflexivity.
        eapply disj_1_incl. eapply defVars_drop_disj; eauto. unfold defVars.
        eauto with cset.
    + exploit IHLS; eauto.
      * pe_rewrite. rewrite <- incl; eauto.
      * pe_rewrite. instantiate (1:=max (list_max (List.map size_of_largest_live_set als)) n).
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r; rewrite vars_up_to_max).
        rewrite up; eauto with cset.
      * pe_rewrite.
        repeat (try rewrite <- NPeano.Nat.add_max_distr_r in X; rewrite vars_up_to_max in X).
        rewrite X. clear_all; cset_tac; intuition.
Qed.

(** ** Theorem 8 from the paper. *)
(** One could prove this theorem directly by induction, however, we exploit that
    under the assumption of the theorem, the liveness information [alv] is also
    sound for functional liveness and we can thus rely on theorem [regAssign_assignment_small]
    above, which we did prove by induction. *)


Lemma regAssign_assignment_small' s ang ϱ ϱ' (alv:ann (set var)) Lv n
  : renamedApart s ang
  -> live_sound Imperative Lv s alv
  -> bounded (live_globals Lv) (fst (getAnn ang))
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
  rewrite X.
  rewrite <- lookup_set_agree; eauto using regAssign_renamedApart_agree; intuition.
  rewrite H5. repeat rewrite vars_up_to_max. cset_tac; intuition.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: ((".." "Lvc")) ***
*** End: ***
*)
