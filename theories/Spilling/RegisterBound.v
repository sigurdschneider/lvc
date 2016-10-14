Require Import List Map Env AllInRel Exp AppExpFree RenamedApart.
Require Import IL Annotation InRel AutoIndTac.
Require Import Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm SpillUtil ReconstrLive.
Require Import ReconstrLiveSmall ReconstrLiveSound InVD AnnP ReconstrLiveUtil SetUtil.
Require Import ReconstrLiveG ToBeOutsourced.


Set Implicit Arguments.
(* TODO: outsource *)

Definition compute_ib
           (Z : params)
           (RM : ⦃var⦄ * ⦃var⦄)
  : list bool
  :=
    mark_elements Z (fst RM ∩ snd RM)
.


Definition reconstr_live_do_spill
           (slot : var -> var)
           (Λ : list (⦃var⦄ * ⦃var⦄))
           (ZL : list params)
           (G : ⦃var⦄)
           (s : stmt)
           (sl : spilling)
  : ann ⦃var⦄
  :=
    reconstr_live (slot_merge slot Λ)
                  ((slot_lift_params slot) ⊜ Λ ZL)
                  G
                  (do_spill slot s sl (compute_ib ⊜ ZL Λ))
                  (do_spill_rm slot sl)
.


Lemma union_meet_distr_l
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    s ∩ (t ∪ u) [=] (s ∩ t) ∪ (s ∩ u)
.
Proof.
  cset_tac.
Qed.

Lemma meet_union_distr_r
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    (s ∩ t) ∪ u [=] (s ∪ u) ∩ (t ∪ u)
.
Proof.
  cset_tac.
Qed.

Lemma meet_union_distr_l
      (X : Type)
      `{OrderedType X}
      (s t u : ⦃X⦄)
  :
    s ∪ (t ∩ u) [=] (s ∪ t) ∩ (s ∪ u)
.
Proof.
  cset_tac.
Qed.


(***************************************************************************)


Definition bounded_in
           (X : Type)
           `{OrderedType X}
           (D : ⦃X⦄)
           (k : nat)
  : ⦃X⦄ -> Prop
  :=
    fun a => cardinal (D ∩ a) <= k
.



Lemma bounded_in_incl
      (VD G G' : ⦃var⦄)
      (k : nat)
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (s : stmt)
      (an : lvness_fragment)
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
    simpl; eauto;
      invc base;
      econstructor;
      eauto;
      clear biG';
  erewrite subset_cardinal; eauto;
  repeat rewrite union_meet_distr_l;
  rewrite Gincl;
  clear; cset_tac.
Qed.



Lemma register_bound_loads
      (k : nat)
      (ZL : list params)
      (Lv : list ⦃var⦄)
      (VD R' G : ⦃var⦄)
      (s : stmt)
      (slot : var -> var)
      (xs : list var)
      (an : lvness_fragment)
  :
    disj VD (map slot VD)
    -> R' ⊆ VD
    -> of_list xs ⊆ R'
    -> bounded_in VD k R'
    -> VD ∩ G ⊆ R'
    -> VD ∩ getAnn (reconstr_live Lv ZL ∅ s an) ⊆ R'
    -> (forall x : var,
          x ∈ of_list xs
          -> ann_P (bounded_in VD k)
                  (reconstr_live Lv ZL (singleton x) s an)
      )
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL G s an)
    -> ann_P (bounded_in VD k)
            (reconstr_live Lv ZL
                           G
                           (write_loads slot xs s)
                           (add_anns ⎣⎦ (length xs) an)
            )
.
Proof.
  intros disj_VD R'_VD xs_R'
         bound_G G_rkl H Lbase base.
  unfold bounded_in in bound_G.
  general induction xs;
    simpl in *; eauto.
  rewrite add_anns_S.
  rewrite add_union_singleton in xs_R'.
  apply union_incl_split2 in xs_R' as [a_R' xs_R'].
  econstructor.
  - unfold bounded_in.
    rewrite reconstr_live_write_loads; [ | | eauto];
      [ | rewrite xs_R', R'_VD; clear; cset_tac].
    rewrite subset_cardinal with (s':=VD ∩ R'); eauto.
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
      * rewrite xs_R', R'_VD; clear; cset_tac.
    + rewrite <- map_singleton.
      rewrite disj_empty_cut; eauto.
      * clear; cset_tac.
      * rewrite a_R', R'_VD; clear; cset_tac.
  - eapply IHxs with (R':=R') ; eauto.
    + rewrite <- a_R'.
      clear; cset_tac.
    + intros x x_in.
      apply Lbase.
      apply incl_singleton in x_in.
      rewrite <- x_in.
      clear; cset_tac.
    + apply Lbase.
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
                           (write_spills slot xs s)
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
    rewrite <- map_singleton.
    rewrite disj_empty_cut; eauto.
    + clear; cset_tac.
    + rewrite a_R', R'_VD.
      reflexivity.
    + eapply bounded_in_incl; eauto.
      rewrite <- map_singleton.
      rewrite disj_empty_cut; eauto.
      * clear; cset_tac.
      * rewrite a_R', R'_VD.
        reflexivity.
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
    -> PIR2 Equal (merge Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> G ⊆ R
    -> ann_P (bounded_in VD k)
            (reconstr_live_do_spill slot Λ ZL G s sl)
.
Proof.
  intros card_R inj_VD disj_VD R_VD M_VD ra_VD
         aeFree rena spillSnd spilli lvSnd
         H16 Z_VD G_R.
  unfold reconstr_live_do_spill.
  general induction lvSnd;
    invc aeFree;
    inv rena;
    inv spillSnd;
    invc spilli;
    eapply renamedApart_incl in rena; eauto;
    simpl in *; eauto.
  - unfold count.
    rewrite add_anns_add; simpl.
    do 2 rewrite <- elements_length.
    eapply register_bound_spills with (R:=R); eauto.
    + rewrite of_list_elements. assumption.
    + unfold bounded_in.
      rewrite subset_cardinal with (s':=R); eauto.
      clear; cset_tac.
    + rewrite G_R; clear; cset_tac.
    + rewrite reconstr_live_write_loads; eauto;
        rewrite of_list_elements;
        [ | rewrite H17, H13, R_VD, M_VD;
            clear; cset_tac ].
      simpl.
      replace (compute_ib ⊜ ZL Λ)
      with (mark_elements ⊜ ZL ((fun RM => fst RM ∩ snd RM) ⊝ Λ))
        by admit.
      rewrite reconstr_live_small with (R:={x; (R\K ∪ L) \Kx}) (M:=Sp ∪ M) (VD:=VD); eauto.
      * assert (forall (s t : ⦃var⦄) (x : var),
                   ({x; s} ∪ t ∪ singleton x) \ singleton x
                                              ⊆ s ∪ t)
          as kill_x by (clear; cset_tac).
        rewrite kill_x.
        repeat rewrite minus_dist_union.
        repeat rewrite union_meet_distr_l.
        repeat apply union_incl_split.
        -- clear; cset_tac.
        -- clear; cset_tac.
        -- rewrite minus_incl.
           rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H13, R_VD, M_VD; clear; cset_tac.
        -- rewrite H20.
           clear; cset_tac.
        -- clear; cset_tac.
        -- rewrite disj_empty_cut; eauto.
           ++ clear; cset_tac.
           ++ rewrite H17, H13, R_VD, M_VD; clear; cset_tac.
        -- clear; cset_tac.
      * eapply Rx_VD with (R:=R) (M:=M) (L:=L); eauto.
        eapply x_VD; eauto.
      * rewrite H13, R_VD, M_VD; clear; cset_tac.
      * rewrite rena.
        unfold union_fs in ra_VD.
        assumption.
    + decide (L [=] ∅).
      * eapply register_bound_loads with (R':=R); eauto.
        ++ rewrite of_list_elements.
           rewrite e0.
           clear; cset_tac.
        ++ unfold bounded_in.
           rewrite subset_cardinal with (s':=R); eauto.
           clear; cset_tac.
        ++ rewrite G_R; clear; cset_tac.
        ++ admit.
        ++ intros x0 x0_in. (**********************************)
      * eapply register_bound_loads with (R':=R \ K ∪ L); eauto.
      ++ eapply R'_VD with (R:=R) (M:=M) (VD:=VD) (Sp:=Sp); eauto.
      ++ rewrite of_list_elements.
        clear; cset_tac.
      ++ unfold bounded_in.
        rewrite subset_cardinal with (s':=R \ K ∪ L); eauto.
        clear; cset_tac.
      ++ rewrite G'_R.



Theorem register_bounded
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
    -> PIR2 Equal (merge Λ) Lv
    -> (forall (Z : params) n,
          get ZL n Z
          -> of_list Z ⊆ VD)
    -> exists al', live_sound Imperative
                 ((slot_lift_params slot) ⊜ Λ ZL)
                 (slot_merge slot Λ)
                 (do_spill slot s sl (compute_ib ⊜ ZL Λ))
                 al'
             /\ ann_P (fun a => cardinal (VD ∩ a) <= k) al'
.
Proof.
  intros.
  exists (reconstr_live (slot_merge slot Λ)
                                ((slot_lift_params slot) ⊜ Λ ZL)
                                (do_spill slot s sl (compute_IB ZL Λ))
                                (do_spill_rm slot sl)).
  split.
  - eapply reconstr_live_sound with (VD:=VD)
                                    (R:=R)
                                    (M:=M); eauto.
  - eapply register_bound_reconstr_spill with (VD:=VD)
                                              (R:=R)
                                              (M:=M); eauto.
Qed.
