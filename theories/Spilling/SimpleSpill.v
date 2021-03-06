Require Import List Map Envs AllInRel Exp.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import ExpVarsBounded SpillSound.

(** * SimpleSpill *)

Fixpoint simpleSpill
         (R : ⦃var⦄)
         (s : stmt)
         (Lv : ann (⦃var⦄))
  : spilling
  :=
    match s,Lv with
    | stmtLet x e t, ann1 LV lv
      => ann1 (R, Exp.freeVars e, nil) (simpleSpill (singleton x) t lv)

    | stmtReturn e, _
      => ann0 (R, Ops.freeVars e, nil)

    | stmtIf e t v, ann2 LV lv_s lv_t
      => ann2 (R, Ops.freeVars e, nil) (simpleSpill (Ops.freeVars e) t lv_s)
                                       (simpleSpill (Ops.freeVars e) v lv_t)

    | stmtApp f Y, _
      => ann0 (R, ∅, (∅, list_union (Ops.freeVars ⊝ Y))::nil)

    | stmtFun F t, annF LV als lv_t
      => annF (R, ∅, ((fun lv => (∅, lv)) ⊝ getAnn ⊝ als))
              ((fun Zs lv => simpleSpill ∅ (snd Zs) lv) ⊜ F als)
              (simpleSpill ∅ t lv_t)

    | _,_ => ann0 (∅, ∅, nil)

    end.

Lemma simpleSpill_sat_spillSound
      (k:nat)
      (s:stmt)
      (R R' M : ⦃var⦄)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (alv : ann ⦃var⦄)
  : R [=] R'
    -> getAnn alv ⊆ R ∪ M
    -> exp_vars_bounded k s
    -> live_sound Imperative ZL Lv s alv
    -> PIR2 (fun RMf G => fst RMf [=] ∅ /\ snd RMf [=] G) Λ Lv
    -> spill_sound k ZL Λ (R,M) s (simpleSpill R' s alv).
Proof.
  intros ReqR' fvRM fvBound lvSound pir2.
  general induction lvSound;
    inversion_clear fvBound
      as [k0 x0 e0 s0 fvBcard fvBs
         |k0 e0 fvBcard
         |k0 e0 s0 t0 fvBcard fvBs fvBt
         |k0 f0 Y0
         |k0 Z0 s0 t0 fvBs fvBt];
    simpl in *.

  - eapply SpillLet with (K:= R) (Kx := Exp.freeVars e);
      [ rewrite <- ReqR' | rewrite <- ReqR' | | | | | ]; eauto.
    + rewrite <- fvRM.
      apply Exp.freeVars_live; eauto.
    + assert (seteq : singleton x [=] {x; (R\R ∪Exp.freeVars e) \Exp.freeVars e}).
      { cset_tac. }
      eapply IHlvSound; eauto with cset.
      * rewrite seteq. reflexivity.
      * rewrite <- seteq. rewrite <- ReqR'. rewrite <- fvRM.
        rewrite <- H0. clear. cset_tac.
    + assert (seteq : R \ R ∪ Exp.freeVars e [=] Exp.freeVars e).
      { cset_tac. }
      rewrite seteq. rewrite fvBcard. trivial.
    + assert (seteq :{x; (R \ R ∪Exp.freeVars e)\ Exp.freeVars e}
                       [=] singleton x).
      { cset_tac. }
      rewrite seteq. rewrite singleton_cardinal. omega.
  - eapply SpillIf with (K:= R);
      [ rewrite <- ReqR' | rewrite <- ReqR' | | | | ]; eauto.
    + rewrite <- fvRM.
      apply Ops.freeVars_live; eauto.
    + assert (seteq : R\R ∪ Ops.freeVars e [=] Ops.freeVars e).
      { cset_tac. }
      rewrite seteq. rewrite fvBcard. trivial.
    + eapply IHlvSound1; eauto with cset.
      * cset_tac.
      * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
    + eapply IHlvSound2; eauto with cset.
      * cset_tac.
      * rewrite <- ReqR'. rewrite <- fvRM. cset_tac.
  - eapply PIR2_nth_2 with (l:=counted l) in pir2; eauto using zip_get.
    destruct pir2 as [[R_f M_f] [pir2_get [pir2_R pir2_M]]]. simpl in *.
    eapply SpillApp with (K:= R) (R_f:= R_f) (M_f:=M_f);
      try rewrite <- ReqR'; eauto.
    + eauto with cset.
    + assert (EQ: R \ R ∪ ∅ [=] ∅) by cset_tac.
      rewrite EQ.
      rewrite empty_cardinal.
      omega.
    + rewrite pir2_R. clear. cset_tac.
    + rewrite pir2_M. rewrite H1. eauto.
    + cset_tac.
    + rewrite Ops.freeVars_live_list; eauto.
  - eapply SpillReturn with (K:= R);
      [ rewrite <- ReqR' | rewrite <- ReqR' | | ]; eauto with cset.
    + rewrite <- fvRM.
      apply Ops.freeVars_live; eauto.
    + assert (seteq : R\R ∪ Ops.freeVars e [=] Ops.freeVars e) by cset_tac.
      rewrite seteq. rewrite fvBcard. trivial.
  - eapply SpillFun with (K:=R);
    [ rewrite <- ReqR' | rewrite <- ReqR' | | | | | | ];
      eauto with cset.
    + assert (seteq : R \ R ∪ ∅ [=] ∅) by cset_tac.
      rewrite seteq. rewrite empty_cardinal. omega.
    + symmetry. apply zip_length2. eauto.
    + repeat rewrite Coqlib.list_length_map. assumption.
    + intros ; inv_get. simpl. rewrite empty_cardinal. omega.
    + intros ; inv_get. eapply H1; eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get; eauto with len.
      intros ; inv_get. simpl. split; eauto with cset.
    + eapply IHlvSound; eauto.
      * cset_tac.
      * rewrite <- ReqR'. rewrite H3. rewrite fvRM. clear. cset_tac.
      * eapply PIR2_app; eauto.
        eapply PIR2_get; eauto with len.
        intros ; inv_get. simpl. split; eauto with cset.
Qed.
