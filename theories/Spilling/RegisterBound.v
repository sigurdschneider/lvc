Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation AutoIndTac.
Require Import Liveness.Liveness LabelsDefined.
Require Import SpillSound DoSpill DoSpillRm SpillUtil ReconstrLive.
Require Import ReconstrLiveSmall ReconstrLiveSound InVD AnnP ReconstrLiveUtil SetUtil.
Require Import ReconstrLiveG ToBeOutsourced BoundedIn.


Set Implicit Arguments.


(** * RegisterBound *)

(***************************************************************************)

Lemma bounded_in_incl
      (VD G G' : ⦃var⦄)
      (k : nat)
      (Lv : list ⦃var⦄)
      (ZL : list (list var))
      (s : stmt)
      (an :  (ann (option (list ⦃var⦄))))
  :
    VD ∩ G' ⊆ VD ∩ G
    -> ann_P (bounded_in VD k) (reconstr_live Lv ZL G s an)
    -> ann_P (bounded_in VD k) (reconstr_live Lv ZL G' s an)
.
Proof.
  intros Gincl base.
  assert (bounded_in VD k G') as biG'.
  {
    apply ann_P_get in base.
    unfold bounded_in in base.
    unfold bounded_in.
    rewrite subset_cardinal with (s':=VD ∩ (getAnn (reconstr_live Lv ZL G s an))); eauto.
    rewrite reconstr_live_G_eq.
    rewrite Gincl.
    clear; cset_tac.
  }
  unfold bounded_in.
  unfold bounded_in in base.
  unfold bounded_in in biG'.
  destruct s, an;
    simpl;
    try destruct a;
    simpl; try eassumption;
      invc base;
      econstructor; try eassumption;
      clear biG';
      erewrite subset_cardinal; try eassumption;
        repeat rewrite union_meet_distr_l;
        rewrite Gincl; try reflexivity.
Qed.


Lemma register_bound_loads
      (k : nat)
      (ZL : list params)
      (Lv : list ⦃var⦄)
      (VD R : ⦃var⦄)
      (s : stmt)
      (slot : var -> var)
      (xs : list var)
      (an : lvness_fragment)
      (x : var)
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> singleton x ⊆ R
    -> of_list xs ⊆ R
    -> bounded_in VD k R
    -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R
    -> (forall (x' : var),
          singleton x' ⊆ R
          -> of_list xs ⊆ R
          -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R
          -> bounded_in VD k R
          -> ann_P (bounded_in VD k)
                  (reconstr_live Lv ZL (singleton x') s an)
      )
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL
                           (singleton x)
                           (write_moves xs (slot ⊝ xs) s)
                           (add_anns ⎣⎦ (length xs) an)
            )
.
Proof.
  intros disj_VD R_VD x_R xs_R
         bound_R H  base.
  unfold bounded_in in bound_R.
  general induction xs;
    simpl in *; eauto.
  rewrite add_anns_S.
  rewrite add_union_singleton in xs_R.
  apply union_incl_split2 in xs_R as [a_R xs_R].
  econstructor.
  - unfold bounded_in.
    rewrite reconstr_live_write_loads; [ | | eauto];
      [ | rewrite xs_R, R_VD; clear; cset_tac].
    rewrite subset_cardinal with (s':=VD ∩ R); eauto.
    apply incl_meet_split; [clear; cset_tac | ].
    setoid_rewrite union_comm at 3.
    rewrite union_minus_incl.
    repeat rewrite union_meet_distr_l.
    repeat apply union_incl_split; eauto.
    + rewrite incl_minus.
      rewrite H.
      clear; cset_tac.
    + rewrite disj_empty_cut; eauto.
      * clear; cset_tac.
      * rewrite xs_R, R_VD; clear; cset_tac.
    + rewrite <- map_singleton; eauto.
      rewrite disj_empty_cut; eauto.
      * clear; cset_tac.
      * rewrite a_R, R_VD; clear; cset_tac.
    + rewrite <- x_R.
      clear; cset_tac.
  - eapply IHxs with (R:=R); eauto.
    intros x' x'_R' xs_R' al_R' bound_R'.
    eapply base; eauto.
    rewrite add_union_singleton, a_R, xs_R.
    clear; cset_tac.
Qed.


(*
Lemma register_bound_empty
 *)


Lemma register_bound_spills
      (k : nat)
      (ZL : list params)
      (Lv : list ⦃var⦄)
      (VD R G : ⦃var⦄)
      (s : stmt)
      (slot : var -> var)
      (xs : list var)
      (an : lvness_fragment)
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> of_list xs ⊆ R
    -> bounded_in VD k R
    -> VD ∩ G ⊆ R
    -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL G s an)
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL
                           G
                           (write_moves (slot ⊝ xs) xs s)
                           (add_anns ⎣⎦ (length xs) an)
                 )
.
Proof.
  intros disj_VD R'_VD xs_R'
         bound_G G_rkl H base.
  unfold bounded_in in bound_G.
  general induction xs;
    simpl in *; eauto.
  rewrite add_anns_S.
  rewrite add_union_singleton in xs_R'.
  apply union_incl_split2 in xs_R' as [a_R' xs_R'].
  econstructor.
  - unfold bounded_in.
    rewrite reconstr_live_write_spills; eauto;
      [ | rewrite xs_R', R'_VD; clear; cset_tac].
    rewrite subset_cardinal with (s':=VD ∩ R); eauto.
    apply incl_meet_split; [clear; cset_tac | ].
    setoid_rewrite union_comm at 3.
    rewrite union_minus_incl.
    repeat rewrite union_meet_distr_l.
    repeat apply union_incl_split; eauto.
    + rewrite incl_minus.
      rewrite H.
      clear; cset_tac.
    + rewrite xs_R'.
      clear; cset_tac.
    + rewrite a_R'.
      clear; cset_tac.
  - eapply IHxs with (R:=R) ; eauto.
    rewrite <- map_singleton; eauto.
    rewrite disj_empty_cut; eauto.
    + clear; cset_tac.
    + rewrite a_R', R'_VD.
      reflexivity.
    + eapply bounded_in_incl; eauto.
      rewrite <- map_singleton; eauto.
      rewrite disj_empty_cut; eauto.
      * clear; cset_tac.
      * rewrite a_R', R'_VD.
        reflexivity.
Qed.


Lemma meet_minus_assoc
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    (s ∩ t) \ u [=] s ∩ (t \ u)
.
Proof.
  cset_tac.
Qed.




Lemma register_bound_s
      (k : nat)
      (ZL : list params)
      (Lv : list ⦃var⦄)
      (VD R G : ⦃var⦄)
      (s : stmt)
      (slot : var -> var)
      (xs ys : list var)
      (an : lvness_fragment)
  :
    disj VD (map slot VD)
    -> R ⊆ VD
    -> of_list xs ⊆ R
    -> of_list ys ⊆ VD
    -> cardinal R <= k
    -> bounded_in VD k (getAnn (reconstr_live Lv ZL ∅ s an) ∪ of_list ys)
    -> VD ∩ G ⊆ R
    -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R ∪ of_list ys
    -> (forall (G' R' : ⦃var⦄),
          VD ∩ G' ⊆ R'
          -> of_list ys ⊆ R'
          -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R'
          -> cardinal R' <= k
          -> ann_P (bounded_in VD k)
                  (reconstr_live Lv ZL G' s an)
      )
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL
                           G
                           (write_moves (slot ⊝ xs) xs
                                         (write_moves ys (slot ⊝ ys) s)
                           )
                           (add_anns ⎣⎦ (length xs + length ys) an)
            )
.
Proof.
  intros disj_VD R_VD xs_R ys_VD bound_R2 bound_al_L G_R al_R base.
  assert (bounded_in VD k R) as bound_R.
  {
    clear - bound_R2.
    unfold bounded_in.
    rewrite subset_cardinal; eauto.
    cset_tac.
  }
  rewrite add_anns_add.
  destruct ys.
  - simpl in *.
    apply register_bound_spills with (R:=R); eauto.
      rewrite add_anns_zero.
    + rewrite al_R; clear; cset_tac.
    + eapply base with (R':=R); eauto.
      * clear; cset_tac.
      * rewrite al_R; clear; cset_tac.
  - eapply register_bound_spills with (R:=R); eauto.
      {
        rewrite reconstr_live_write_loads; eauto.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        - rewrite <- meet_minus_assoc.
          rewrite al_R.
          clear; cset_tac.
        - rewrite disj_empty_cut; eauto.
          clear; cset_tac.
        - clear; cset_tac.
      }
      simpl in *.
      rewrite add_union_singleton in ys_VD.
      apply union_incl_split2 in ys_VD as [v_VD ys_VD].
      rewrite add_anns_S.
      econstructor.
    + unfold bounded_in.
      rewrite reconstr_live_write_loads; eauto.
      repeat rewrite union_meet_distr_l.
      rewrite <- meet_minus_assoc.
      repeat rewrite union_meet_distr_l.
      rewrite <- meet_minus_assoc.
      rewrite al_R.
      assert (forall (x : var) (s t u v : ⦃var⦄),
                 ((s ∪ {x; t}) \ t ∪ (v ∩ u) ∪ (v ∩ singleton x) ) \ singleton x
               ⊆ ((s ∪ (v ∩ u))))
        as seteq by (clear; cset_tac).
      rewrite seteq.
      rewrite subset_cardinal with (s':=VD ∩ R); eauto.
      repeat apply union_incl_split; eauto.
      * clear - R_VD; cset_tac.
      * rewrite disj_empty_cut; eauto.
        clear; cset_tac.
      * rewrite <- map_singleton; eauto.
        rewrite disj_empty_cut; eauto.
        clear; cset_tac.
      * rewrite G_R.
        clear - R_VD; cset_tac.
    + eapply register_bound_loads
      with (R:=VD ∩ getAnn (reconstr_live Lv ZL ∅ s an)
                  ∪ {n; of_list ys}); eauto.
      * rewrite add_union_singleton, v_VD, ys_VD.
        clear; cset_tac.
      * clear; cset_tac.
      * clear; cset_tac.
      * unfold bounded_in.
        assert (forall (s t u : ⦃var⦄),
                   s ∩ (s ∩ t ∪ u) ⊆ s ∩ (t ∪ u))
          as setsub by (clear; cset_tac).
        rewrite setsub.
        assumption.

      * intros.
        eapply base; eauto.
        -- rewrite H.
           clear; cset_tac.
        -- clear; cset_tac.
        -- unfold bounded_in in H2.
           rewrite subset_cardinal; eauto.
           apply union_incl_split.
           ++ clear; cset_tac.
           ++ rewrite union_meet_distr_l.
              apply incl_union_right.
              apply incl_meet_split; eauto.
              rewrite add_union_singleton, v_VD, ys_VD.
              clear; cset_tac.
Qed.

Lemma slot_lift_args_RMapp_incl
      (slot : var -> var)
      (Y : args)
      RM RMapp Z
  :
    (forall (n : nat) (y : op), get Y n y -> isVar y)
    -> (list_union (Op.freeVars ⊝ Y) ⊆ fst RMapp ∪ snd RMapp)
    -> list_union (Op.freeVars ⊝ slot_lift_args slot RM RMapp Y Z)
                 ⊆ fst RMapp ∪ map slot (snd RMapp).
Proof.
  general induction Y; destruct Z; simpl in *; only 1,2,3: eauto with cset.
  revert H0.
  exploit H as IV; eauto using get. invc IV. simpl.
  repeat cases; simpl; norm_lunion; intro;
    rewrite IHY; eauto using get; intros; clear IHY H.
  - assert (v ∈ fst RMapp ∪ snd RMapp). cset_tac.
    unfold choose_y; simpl; repeat cases; simpl.
    + revert COND1. clear_all. cset_tac.
    + revert COND1 COND2. clear_all. cset_tac.
    + revert COND1. clear_all. cset_tac.
    + revert H NOTCOND. clear_all. cset_tac.
    + revert COND1. clear_all. cset_tac.
    + exfalso. cset_tac.
    + revert COND0 COND2. clear_all. cset_tac.
    + revert COND0. clear_all. cset_tac.
    + revert COND0. clear_all. cset_tac.
    + revert COND1. clear_all. cset_tac.
    + exfalso. revert H NOTCOND0 NOTCOND1. cset_tac.
    + revert NOTCOND0 H. clear_all. cset_tac.
  - rewrite <- H0. cset_tac.
  - assert (v ∈ fst RMapp ∪ snd RMapp). cset_tac.
    unfold choose_y; simpl; repeat cases; simpl.
    + revert COND1. clear_all. cset_tac.
    + revert NOTCOND0 H. clear_all. cset_tac.
  - rewrite <- H0. cset_tac.
  - assert (v ∈ fst RMapp ∪ snd RMapp). cset_tac.
    unfold choose_y; simpl; repeat cases; simpl.
    + revert COND0. clear_all. cset_tac.
    + revert NOTCOND1 H. clear_all. cset_tac.
    + revert COND. clear_all. cset_tac.
    + revert NOTCOND2 H. clear_all. cset_tac.
  - rewrite <- H0. cset_tac.
Qed.



Lemma register_bounded
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M VD : ⦃var⦄)
      (s : stmt)
      (Lv : list ⦃var⦄)
      (sl : spilling)
      (al : ann ⦃var⦄)
      (ra : ann (⦃var⦄ * ⦃var⦄))
  :
    cardinal R <= k
    -> injective_on VD slot
    -> disj VD (map slot VD)
    -> R ⊆ VD
    -> M ⊆ VD
    -> union_fs (getAnn ra) ⊆ VD
    -> app_expfree s
    -> renamedApart s ra
    -> spill_sound k ZL Λ (R,M) s sl
    -> spill_live VD sl al
    -> live_sound Imperative ZL Lv s al
    -> PIR2 Equal (merge ⊝ Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> (forall (n : nat) Z blv,
          get ZL n Z ->
          get Lv n blv ->
          of_list Z [<=] blv)
    -> VD ∩ G ⊆ R
    -> ann_P (bounded_in VD k)
            (reconstr_live_do_spill slot Λ ZL G s sl)
.
Proof.
  intros card_R inj_VD disj_VD R_VD M_VD ra_VD
         aeFree rena spillSnd spilli lvSnd
         H16 Z_VD Z_LV G_R.
  unfold reconstr_live_do_spill.
  general induction lvSnd;
    invc aeFree;
    inv rena;
    inv spilli;
    inv spillSnd;
    eapply renamedApart_incl in rena; eauto;
      simpl in *; eauto;
        unfold count;
        simpl;
        do 2 rewrite <- elements_length.

  - eapply register_bound_s with (VD:=VD) (R:=R); simpl; eauto.
    + rewrite of_list_elements, H19.
      reflexivity.
    + rewrite of_list_elements, H20, H19, R_VD, M_VD.
      clear; cset_tac.
    + unfold bounded_in.
      rewrite of_list_elements.
      rewrite reconstr_live_small with (VD:=VD) (R:={x; (R\K ∪ L) \ Kx}) (M:=Sp ∪ M); eauto.
      * rewrite subset_cardinal with (s':=R \K ∪ L); eauto.
        assert (forall (x : var) (s t : ⦃var⦄),
                   ({x; s} ∪ t ∪ singleton x) \ singleton x
                                              ⊆ s ∪ t)
          as setsub by (clear; cset_tac).
        rewrite setsub.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        -- clear; cset_tac.
        -- rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H19, R_VD, M_VD.
              clear; cset_tac.
        -- rewrite H22. clear; cset_tac.
        -- clear; cset_tac.
        -- clear; cset_tac.
      * rewrite H20, H19, R_VD, M_VD.
        eapply x_VD in H10; eauto.
        revert H10; clear; cset_tac.
      * rewrite H19, M_VD, R_VD.
        clear; cset_tac.
      * rewrite rena, <- ra_VD.
        eauto.
    + rewrite of_list_elements.
      rewrite reconstr_live_small with (VD:=VD) (R:={x; (R\K ∪ L) \ Kx}) (M:=Sp ∪ M); eauto.
      * assert (forall (x : var) (s t : ⦃var⦄),
                   ({x; s} ∪ t ∪ singleton x) \ singleton x
                                              ⊆ s ∪ t)
          as setsub by (clear; cset_tac).
        rewrite setsub.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        -- clear; cset_tac.
        -- rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H19, R_VD, M_VD.
              clear; cset_tac.
        -- rewrite H22. clear; cset_tac.
        -- clear; cset_tac.
      * rewrite H20, H19, R_VD, M_VD.
        eapply x_VD in H10; eauto.
        revert H10; clear; cset_tac.
      * rewrite H19, M_VD, R_VD.
        clear; cset_tac.
      * rewrite rena, <- ra_VD.
        eauto.
    + intros G' R' G'_R' L_R' al_R' bound_R'.
      rewrite of_list_elements in L_R'.
      econstructor.
      * unfold bounded_in.
        rewrite subset_cardinal with (s':=R'); eauto.
        -- rewrite union_meet_distr_l.
           rewrite G'_R'.
           rewrite empty_neutral_union_r in al_R'.
           rewrite al_R'.
           clear; cset_tac.
      * eapply IHlvSnd with (R:={x; (R\K ∪ L) \ Kx})
                              (M:=Sp ∪ M); eauto;
          eauto using M'_VD.
        -- eapply Rx_VD with (VD:=VD) (M:=M); eauto.
           eapply x_VD; eauto.
        -- rewrite rena, <- ra_VD; eauto.
        -- clear; cset_tac.

  - destruct rena as [rena1 rena2].
    eapply register_bound_s with (VD:=VD) (R:=R); simpl; eauto.
    + rewrite of_list_elements; assumption.
    + rewrite of_list_elements, H25, H24, R_VD, M_VD.
      clear; cset_tac.
    + unfold bounded_in.
      rewrite of_list_elements.
      rewrite subset_cardinal; eauto.
      rewrite reconstr_live_small with (VD:=VD) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
      * rewrite reconstr_live_small with (VD:=VD) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- repeat rewrite union_meet_distr_l.
           clear - H24 H25 H26 R_VD M_VD disj_VD.
           assert (VD ∩ map slot (Sp ∪ M) ⊆ R \ K ∪ L) as goal37.
           {
             rewrite disj_empty_cut; eauto.
             - clear; cset_tac.
             - rewrite H24, R_VD, M_VD; cset_tac.
           }
           repeat apply union_incl_split; eauto; try rewrite H26;
            clear; cset_tac.
        -- rewrite H25, H24, R_VD, M_VD. clear; cset_tac.
        -- rewrite H24, R_VD, M_VD; clear; cset_tac.
        -- rewrite rena2, <- ra_VD; eauto.
      * rewrite H25, H24, R_VD, M_VD. clear; cset_tac.
      * rewrite H24, R_VD, M_VD; clear; cset_tac.
      * rewrite rena1, <- ra_VD; eauto.
    + rewrite of_list_elements.
      rewrite reconstr_live_small with (VD:=VD) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
      * rewrite reconstr_live_small with (VD:=VD) (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- repeat rewrite union_meet_distr_l.
           clear - H24 H25 H26 R_VD M_VD disj_VD.
           assert (VD ∩ map slot (Sp ∪ M) ⊆ R ∪ L) as goal37.
           {
             rewrite disj_empty_cut; eauto.
             - clear; cset_tac.
             - rewrite H24, R_VD, M_VD; cset_tac.
           }
           repeat apply union_incl_split; eauto;
             try rewrite H26; clear; cset_tac.
        -- rewrite H25, H24, R_VD, M_VD. clear; cset_tac.
        -- rewrite H24, R_VD, M_VD; clear; cset_tac.
        -- rewrite rena2, <- ra_VD; eauto.
      * rewrite H25, H24, R_VD, M_VD. clear; cset_tac.
      * rewrite H24, R_VD, M_VD; clear; cset_tac.
      * rewrite rena1, <- ra_VD; eauto.
    + intros G' R' G'_R' L_R' al_R' bound_R'.
      rewrite of_list_elements in L_R'.
      econstructor.
      * unfold bounded_in.
        rewrite subset_cardinal with (s':=R'); eauto.
        -- rewrite union_meet_distr_l.
           rewrite G'_R'.
           rewrite empty_neutral_union_r in al_R'.
           rewrite al_R'.
           clear; cset_tac.
      * eapply IHlvSnd1 with (R:=R\K ∪ L)
                              (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (VD:=VD) (M:=M); eauto.
        -- eapply M'_VD with (VD:=VD) (M:=M) (R:=R); eauto.
        -- rewrite rena1, <- ra_VD; eauto.
        -- clear; cset_tac.
      * eapply IHlvSnd2 with (R:=R\K ∪ L)
                               (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (VD:=VD) (M:=M); eauto.
        -- eapply M'_VD with (VD:=VD) (M:=M) (R:=R); eauto.
        -- rewrite rena2, <- ra_VD; eauto.
        -- clear; cset_tac.

  - eapply register_bound_s with (VD:=VD) (R:=R); simpl; eauto.
    + rewrite of_list_elements; assumption.
    + rewrite of_list_elements, H13, H12, R_VD, M_VD.
      clear; cset_tac.
    + erewrite nth_zip; eauto.
      unfold bounded_in.
      rewrite subset_cardinal; eauto.
      erewrite !get_nth; eauto using map_get_1. simpl.
      rewrite slot_lift_args_RMapp_incl; simpl; eauto; [|rewrite H22; reflexivity].
      rewrite of_list_elements.
      eapply PIR2_nth in H16; eauto; dcr. inv_get. unfold merge in H8. simpl in *.
      rewrite of_list_slot_lift_params; [|rewrite Z_LV; eauto; rewrite H8; reflexivity].
      unfold union_fs in ra_VD. simpl in *.
      rewrite H9 in *; clear H9 D'.
      rewrite H23.
      assert (M'VD:M' [<=] VD). {
        rewrite H24, H12, R_VD, M_VD. eauto with cset.
      }
      assert (M_fVD:M_f ⊆ VD). {
        rewrite Mf_VD with (R:=R) (M:=M) (VD:=VD); eauto.
      }
      rewrite empty_neutral_union_r.
      repeat rewrite union_meet_distr_l.
      rewrite (@disj_empty_cut VD); eauto.
      rewrite minus_dist_union.
      repeat rewrite union_meet_distr_l.
      rewrite (@incl_minus _ _ (map slot M_f)).
      rewrite (@disj_empty_cut VD); eauto.
      rewrite empty_neutral_union_r.
      assert (of_list Z ∩ R_f ⊆ of_list Z \ (M_f \ R_f) ∪ map slot (of_list Z \ (R_f \ M_f))). {
        clear_all. cset_tac.
      }
      rewrite <- H4.
      revert H20. clear_all. cset_tac.
    + erewrite nth_zip; eauto.
      rewrite slot_lift_args_RMapp_incl; eauto; simpl; [|rewrite H22; reflexivity].
      erewrite !get_nth; eauto using map_get_1.
      rewrite of_list_elements.
      rewrite slp_union_minus_incl; eauto; simpl.
      assert (M'VD:M' [<=] VD). {
        rewrite H24, H12, R_VD, M_VD. eauto with cset.
      }
      assert (M_fVD:M_f ⊆ VD). {
        rewrite Mf_VD with (R:=R) (M:=M) (VD:=VD); eauto.
      }
      * rewrite H20, H23.
        rewrite empty_neutral_union_r.
        repeat rewrite union_meet_distr_l.
        rewrite (@disj_empty_cut VD); eauto.
        rewrite minus_incl with (t:=map slot (of_list Z0)).
        rewrite (@disj_empty_cut VD); eauto.
        clear_all. cset_tac.
      * rewrite Rf_VD with (R:=R) (M:=M) (VD:=VD) (L:=L); eauto.
      * rewrite Mf_VD with (R:=R) (M:=M) (VD:=VD); eauto.
    + intros G' R'' G'_R' L_R' al_R' bound_R'.
      econstructor.
      unfold bounded_in.
      rewrite subset_cardinal; eauto.
      rewrite union_meet_distr_l.
      rewrite empty_neutral_union_r in al_R'.
      rewrite al_R', G'_R'.
      clear; cset_tac.
  - eapply register_bound_s with (VD:=VD) (R:=R); simpl; eauto.
    + rewrite of_list_elements; assumption.
    + rewrite of_list_elements, H9, H8, R_VD, M_VD.
      clear; cset_tac.
    + unfold bounded_in.
      rewrite of_list_elements.
      rewrite subset_cardinal; eauto.
      rewrite H10.
      clear; cset_tac.
    + rewrite H10, of_list_elements.
      clear; cset_tac.
    + intros G' R' G'_R' L_R' al_R' bound_R'.
      rewrite empty_neutral_union_r in al_R'.
      econstructor.
      unfold bounded_in.
      rewrite subset_cardinal; eauto.
      rewrite union_meet_distr_l, G'_R', al_R'.
      clear; cset_tac.

  - destruct rena as [renaF rena2].
    eapply register_bound_s with (VD:=VD) (R:=R); simpl; eauto.
    + rewrite of_list_elements; assumption.
    + rewrite of_list_elements, H29, H28, R_VD, M_VD; clear; cset_tac.
    + unfold bounded_in.
      rewrite fst_zip_pair; eauto with len.
      rewrite slot_lift_params_app; eauto with len.
      rewrite slot_merge_app.
      rewrite subset_cardinal; eauto.
      rewrite reconstr_live_small with (VD:=VD) (R:=R\K∪L) (M:=Sp ∪ M); eauto.
      * rewrite of_list_elements, !empty_neutral_union_r.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        -- clear; cset_tac.
        -- clear; cset_tac.
        -- rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H28, R_VD, M_VD; clear; cset_tac.
        -- clear; cset_tac.
      * eapply R'_VD with (VD:=VD) (L:=L) (M:=M); eauto.
      * rewrite H28, R_VD, M_VD; clear; cset_tac.
      * rewrite rena2, <- ra_VD; eauto.
      * eapply getAnn_als_EQ_merge_rms; eauto.
      * intros.
        eapply get_ofl_VD; eauto.
    + rewrite fst_zip_pair; eauto with len.
      rewrite slot_lift_params_app; eauto with len.
      rewrite slot_merge_app.
      rewrite reconstr_live_small with (VD:=VD) (R:=R\K∪L) (M:=Sp ∪ M); eauto.
      * rewrite of_list_elements, !empty_neutral_union_r.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        -- clear; cset_tac.
        -- clear; cset_tac.
        -- rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H28, R_VD, M_VD; clear; cset_tac.
      * eapply R'_VD with (VD:=VD) (L:=L) (M:=M); eauto.
      * rewrite H28, R_VD, M_VD; clear; cset_tac.
      * rewrite rena2, <- ra_VD; eauto.
      * eapply getAnn_als_EQ_merge_rms; eauto.
      * intros.
        eapply get_ofl_VD; eauto.
    + intros G' R' G'_R' L_R' al_R' bound_R'.
      rewrite fst_zip_pair; eauto with len.
      rewrite slot_lift_params_app; eauto with len.
      rewrite slot_merge_app.

      rewrite fst_zip_pair in al_R'; eauto with len.
      rewrite slot_lift_params_app in al_R'; eauto with len.
      rewrite slot_merge_app in al_R'.

      econstructor.
      * unfold bounded_in.
        rewrite subset_cardinal; eauto.
        rewrite union_meet_distr_l.
        rewrite empty_neutral_union_r in al_R'.
        rewrite G'_R', al_R'.
        clear; cset_tac.
      * intros; inv_get.
        exploit H10 as funConstr; eauto.
        exploit renaF as renaF'; eauto.
        exploit H34 as spillSnd'; eauto.
        exploit H20 as rm_VD; eauto.
        destruct rm_VD as [f_x2_VD s_x2_VD]; eauto.
        rewrite pair_eta with (p:=x2) in spillSnd'.
        destruct funConstr as [funConstr _].
        apply incl_from_union_eq in funConstr as funConstr1.
        rewrite union_comm in funConstr.
        apply incl_from_union_eq in funConstr as funConstr2.
        simpl.
        eapply H1 with (R:=fst x2) (M:=snd x2); eauto.
        -- rewrite renaF', <- ra_VD; eauto.
        -- eapply getAnn_als_EQ_merge_rms; eauto.
        -- intros.
           eapply get_ofl_VD; eauto.
        -- intros.
           eapply get_app_cases in H4 as [?|[? ?]]; inv_get.
           edestruct H2; eauto. len_simpl.
           eapply get_app_ge in H14. len_simpl.
           rewrite <- H in *.
           eapply Z_LV; eauto. len_simpl. rewrite <- H. eauto.
        -- setoid_rewrite pair_eta with (p:=x2) at 1.
           rewrite pair_eta with (p:=x2) in H22.
           eapply al_sub_RfMf in H22; eauto.
           rewrite ofl_slp_sub_rm; eauto.
           ++ rewrite union_meet_distr_l.
              apply union_incl_split.
              ** clear; cset_tac.
              ** rewrite disj_empty_cut; eauto.
                 clear; cset_tac.
           ++ exploit H2 as H2'; eauto.
      * eapply IHlvSnd with (R:=R\K ∪ L) (M:=Sp ∪ M); eauto.
        -- eapply R'_VD with (VD:=VD) (L:=L) (M:=M); eauto.
        -- rewrite H28, R_VD, M_VD; eauto.
           clear; cset_tac.
        -- rewrite rena2, <- ra_VD; eauto.
        -- apply getAnn_als_EQ_merge_rms; eauto.
        -- intros.
           eapply get_ofl_VD; eauto.
        -- intros.
           eapply get_app_cases in H4 as [?|[? ?]]; inv_get.
           edestruct H2; eauto. len_simpl.
           eapply get_app_ge in H5. len_simpl.
           rewrite <- H in *.
           eapply Z_LV; eauto. len_simpl. rewrite <- H. eauto.
        -- clear; cset_tac.
Qed.
