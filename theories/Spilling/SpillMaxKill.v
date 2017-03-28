Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness RenamedApart.
Require Import ExpVarsBounded SpillSound OneOrEmpty RegLive.
Require Import Take TakeSet.



Set Implicit Arguments.


(* TODO : - adjust spill_min_kill such that no explicit kill set is necessary 
          - prove spill_sound -> spill_min_kill *)


Inductive spill_max_kill (k:nat) :
  (list params)
  -> (list (⦃var⦄ * ⦃var⦄))
  -> (⦃var⦄ * ⦃var⦄)
  -> stmt
  -> ann ⦃var⦄
  -> spilling
  -> Prop
  :=

  | SpillLet
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
      (rlv : ann ⦃var⦄)
    : let K := (R \ (Exp.freeVars e ∪ getAnn rlv)) ∪ (R ∩ L) in
      let Kx:= ((R \ K ∪ L) \ getAnn rlv) in 
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> spill_max_kill k ZL Λ ({x; (R\K ∪ L) \ Kx}, Sp ∪ M) s rlv sl
      -> Exp.freeVars e ⊆ R\K ∪ L
      -> k > 0
      -> cardinal (R\K ∪ L) <= k
      -> cardinal {x; (R\K ∪ L) \ Kx} <= k
      -> spill_max_kill k ZL Λ (R,M) (stmtLet x e s) (ann1 Rlv rlv) (ann1 (Sp,L,nil) sl)
                       
  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv: ⦃var⦄)
      (e : op)
    : let K := (R \ (Op.freeVars e)) ∪ (R ∩ L) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> spill_max_kill k ZL Λ (R,M) (stmtReturn e) (ann0 Rlv) (ann0 (Sp,L,nil))

  | SpillIf
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv: ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)
      (rlv1 rlv2 : ann ⦃var⦄)
    : let K := (R \ (Op.freeVars e ∪ getAnn rlv1 ∪ getAnn rlv2)) ∪ (R ∩ L) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Op.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> spill_max_kill k ZL Λ (R \ K ∪ L, Sp ∪ M) s rlv1 sl_s
      -> spill_max_kill k ZL Λ (R \ K ∪ L, Sp ∪ M) t rlv2 sl_t
      -> spill_max_kill k ZL Λ (R,M) (stmtIf e s t) (ann2 Rlv rlv1 rlv2) (ann2 (Sp,L,nil) sl_s sl_t)

  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L R_f M_f R' M' Rlv : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
    : let K := set_take ((cardinal R + cardinal L) - k) (R \ R_f) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> get ZL (counted f) Z
      -> get Λ (counted f) (R_f,M_f)
      -> R_f \ of_list Z ⊆ R\K ∪ L
      -> M_f \ of_list Z ⊆ Sp ∪ M
      -> list_union (Op.freeVars ⊝ Y) ⊆ (R\K ∪ L) ∪ M'
      -> M' ⊆ Sp ∪ M
      -> spill_max_kill k ZL Λ (R,M) (stmtApp f Y) (ann0 Rlv) (ann0 (Sp,L, (R', M')::nil))

  | SpillFun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L Rlv : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
      (rlv_t : ann ⦃var⦄)
      (rlv_F : list (ann ⦃var⦄))
    : let K := set_take ((cardinal R + cardinal L) - k) (R \ getAnn rlv_t) in
      Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> length F = length sl_F
      -> length F = length rms
      -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
      -> (forall n Zs rm rlv_s sl_s, get rms n rm
                         -> get F n Zs
                         -> get rlv_F n rlv_s
                         -> get sl_F n sl_s
                         -> spill_max_kill k ((fst ⊝ F) ++ ZL)
                                          (rms ++ Λ) rm (snd Zs) rlv_s sl_s
        )
      -> spill_max_kill k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t rlv_t sl_t
      -> spill_max_kill k ZL Λ (R,M) (stmtFun F t) (annF Rlv rlv_F rlv_t) (annF (Sp,L,rms) sl_F sl_t)
.

Lemma Sp_sub_rlv k ZL Λ R M s sl rlv :
  spill_sound k ZL Λ (R,M) s sl
  -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
  -> getSp sl ⊆ getAnn rlv
.
Proof.
  intros spillSnd rlive. general induction spillSnd; invc rlive; simpl; eauto.
Qed.

Lemma card_diff (X:Type) `{OrderedType X} (s t : ⦃X⦄) :
  cardinal (s \ t) = cardinal s - cardinal (s ∩ t)
.
Proof.
  setoid_rewrite <-diff_inter_cardinal with (s':=t) at 2. omega.
Qed.

Lemma card_RKL (X:Type) `{OrderedType X} k (s t u : ⦃X⦄) :
  t ⊆ s
  -> cardinal u <= k
  -> cardinal t = cardinal s + cardinal u - k
  -> cardinal (s \ t ∪ u) <= k
.
Proof.
  intros sub ucard card.
  rewrite union_cardinal_inter. rewrite card_diff. rewrite meet_comm, inter_subset_equal; eauto.
  rewrite card. omega.
Qed.

Lemma incl_minus_union (X:Type) `{OrderedType X} (s t u : ⦃X⦄) :
  t ⊆ u -> s \ t ∪ u [=] s ∪ u
.
Proof.
  intros; cset_tac.
Qed.

Lemma rkl'_incl_rkl (X:Type) `{OrderedType X} (s s' t t1 t2 u v w : ⦃X⦄) (x : X) :
  let t' := s' \ (t1 ∪ t2) ∪ (s' ∩ v) in
  t1 ⊆ s \ t ∪ v
  -> t2 ⊆ {x; (s \ t ∪ v) \ w}
  -> s' ⊆ u
  -> x ∉ u
  -> s' \ t' ∪ v ⊆ s \ t ∪ v
.
Proof.
  intros t' t1_incl t2_incl s'_incl x_nin.
  subst t'.
  cset_tac.
(*  rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
  rewrite minus_minus. rewrite t1_incl.
  rewrite t2_incl. cset_tac.
      cbn in R_sub; clear - R_sub H9. cset_tac.*)
Qed.

Lemma spill_sound_spill_max_kill' k ZL Λ R R' M G s sl rlv ra :
  rlv === reg_live ZL (fst ⊝ Λ) G s sl
  -> renamedApart s ra
  -> spill_sound k ZL Λ (R,M) s sl
  -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
  -> R' ∪ M ⊆ fst (getAnn ra)
  -> getAnn rlv ⊆ R'
  -> spill_max_kill k ZL Λ (R',M) s rlv sl
.
Proof.
  intros rlv_eq rena spillSnd rlive R_sub rlv_sub'.
  general induction spillSnd; invc rlive; invc rlv_eq; invc rena; cbn in rlv_sub'.
  - set (K' := R' \ (Exp.freeVars e ∪ getAnn al) ∪ (R' ∩ L)).
    assert (R' \ K' ∪ L ⊆ R0 \ K ∪ L) as rkl'_in_rkl2.
    {
      clear - H1 H10 spillSnd R_sub H9.
      eapply reg_live_R in spillSnd; [|eapply PIR2_refl; eauto]. cbn in spillSnd.
      apply ann_R_get in H10. rewrite reg_live_G_eq in H10.
      eapply rkl'_incl_rkl; eauto.
      - rewrite H10. apply union_incl_split; [eauto|clear;cset_tac].
      - cbn in R_sub. clear - R_sub; cset_tac.
    }
    subst K'.
    econstructor; eauto;
      set (K' := R' \ (Exp.freeVars e ∪ getAnn al) ∪ (R' ∩ L)) in *;
      set (Kx':= (R' \ K' ∪ L) \ getAnn al) in *.
    + rewrite H13. eauto.
    + eapply IHspillSnd; eauto.
      * invc  H20. cbn. rewrite H14.
        cbn in R_sub. apply union_incl_split.
        -- apply add_struct_incl. rewrite !minus_incl. rewrite H0, H13, rlv_sub'.
           clear - R_sub. cset_tac.
        -- rewrite H13, rlv_sub', R_sub. clear; cset_tac.
      * enough (getAnn al \ singleton x ⊆ (R' \ K' ∪ L) \ Kx') as Hypo.
        { rewrite <-Hypo. clear; cset_tac. }
        rewrite <-inter_subset_equal with (s':=getAnn al);[| clear; cset_tac]. rewrite H17.
        subst K'. rewrite <-minus_union, minus_minus.
        setoid_rewrite <-rlv_sub' at 1. apply not_incl_minus; [clear; cset_tac|].
        subst Kx'. clear; cset_tac.
    (*
      setoid_rewrite <-union_subset_equal with (s0:=lv) at 8;[|eauto].
      setoid_rewrite <-union_subset_equal with (s0:=M0) at 11;[|eauto].
      setoid_rewrite <-H13 at 2. setoid_rewrite <-union_assoc at 2. setoid_rewrite union_assoc at 2.
      setoid_rewrite <-H0 at 2.
      rewrite H13. clear - H17. cset_tac.*)
    + subst K'. rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Exp.freeVars_live in H16. clear - H16; cset_tac.
    + rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto.
    + rewrite subset_cardinal with (s':={x; (R0 \ K ∪ L) \ Kx}); eauto.
      eapply reg_live_R in spillSnd; [|eapply PIR2_refl; eauto].
      subst Kx'. rewrite minus_minus.
      rewrite rkl'_in_rkl2. apply incl_add_eq; split; [clear;cset_tac|].
      rewrite H10, reg_live_G_eq, spillSnd. cbn. clear. cset_tac.
Admitted. (*
  - econstructor; eauto.
    + rewrite H8; eauto.
    + rewrite <-minus_union.
      rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Op.freeVars_live in H10. clear - H10. cset_tac.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus. rewrite H1. rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto.
      clear; cset_tac.
  - eapply reg_live_R in spillSnd1 as spillSnd1'; [|eapply PIR2_refl; eauto].
    eapply reg_live_R in spillSnd2 as spillSnd2'; [|eapply PIR2_refl; eauto].
    (*apply ann_R_get in H10 as al1_eq. apply ann_R_get in H11 as al2_eq.*)
    econstructor; eauto.
    + rewrite H12; eauto.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Op.freeVars_live in H16. clear - H16; cset_tac.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus. rewrite H1.
      rewrite H10, reg_live_G_eq, spillSnd1'. cbn.
      rewrite H11, reg_live_G_eq, spillSnd2'. cbn.
      rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto. 
      cbn in R_sub; clear - R_sub H9; cset_tac.
    + eapply IHspillSnd1; eauto.
      * invc  H21. cbn. rewrite H20. cbn in R_sub.
        rewrite <-minus_union, minus_minus, H6, H17, H18, rlv_sub', H12.
        setoid_rewrite H0 at 4. rewrite H12, rlv_sub'. clear - R_sub. cset_tac.
      * rewrite <-inter_subset_equal with (s':=getAnn al1); [|clear;cset_tac]. setoid_rewrite H17 at 1.
        rewrite <-minus_union, minus_minus. setoid_rewrite rlv_sub' at 1. clear; cset_tac.
(*
      setoid_rewrite <-union_subset_equal with (s0:=lv) at 7;[|eauto].
      setoid_rewrite <-union_subset_equal with (s0:=M0) at 10;[|eauto].
      setoid_rewrite <-H12 at 2. setoid_rewrite <-union_assoc at 2. setoid_rewrite union_assoc at 2.
      setoid_rewrite <-H0 at 2.
      rewrite H12. clear - H17. cset_tac.*)
    + eapply IHspillSnd2; eauto.
      
      * invc  H22. cbn. rewrite H20. cbn in R_sub.
        rewrite <-minus_union, minus_minus, H6, H17, H18, rlv_sub', H12.
        setoid_rewrite H0 at 4. rewrite H12, rlv_sub'. clear - R_sub. cset_tac.
      * rewrite <-inter_subset_equal with (s':=getAnn al2); [|clear;cset_tac]. setoid_rewrite H18 at 1.
        rewrite <-minus_union, minus_minus. setoid_rewrite rlv_sub' at 1. clear; cset_tac.
  - admit.
  - admit.
Admitted.*)


Lemma rlive_min_getAnn k ZL Λ s sl rlv R M :
  rlive_min k ZL Λ ∅ s sl rlv
  -> spill_sound k ZL Λ (R,M) s sl
  -> getAnn rlv ⊆ R
.
Proof.
  intros rliveMin spillSnd. general induction rliveMin; cbn; unfold is_rlive_min in H;
                              rewrite <-minus_empty; try eapply H; eauto.
Qed.

Lemma rlive_min_getAnn_G k ZL Λ G s sl rlv :
  rlive_min k ZL Λ G s sl rlv
  -> (forall R M, spill_sound k ZL Λ (R,M) s sl -> getAnn rlv ⊆ R)
  -> rlive_min k ZL Λ ∅ s sl rlv
.
Proof.
  intros rliveMin isMin.
  general induction rliveMin; econstructor; cbn in *; eauto;
    unfold is_rlive_min; intros; rewrite minus_empty; eapply isMin; eauto.
Qed.

Lemma rlive_min_incl_R k ZL Λ s sl rlv R M G :
  G ⊆ R
  -> spill_sound k ZL Λ (R, M) s sl
  -> rlive_min k ZL Λ G s sl rlv
  -> getAnn rlv ⊆ R
.
Proof.
  intros Geq spillSnd rlive.
  general induction rlive; cbn;
    unfold is_rlive_min in *; rewrite <-union_subset_equal with (s':=R); eauto;
      apply incl_minus_incl_union; [| | | |eapply H1;eauto]; eapply H; eauto.
Qed.

Lemma rlive_min_monotone k ZL Λ s sl G G' rlv :
  G ⊆ G'
  -> rlive_min k ZL Λ G  s sl rlv
  -> rlive_min k ZL Λ G' s sl rlv
.
Proof.
  intros Geq rliveMin.
  general induction rliveMin; econstructor; eauto; unfold is_rlive_min in *; intros; rewrite <-Geq;
    eauto.
Qed.
      


Lemma spill_sound_spill_max_kill k ZL Λ R R' M G s sl rlv ra :
  renamedApart s ra
  -> spill_sound k ZL Λ (R,M) s sl
  -> rlive_min k ZL Λ G s sl rlv
  -> rlive_sound ZL (fst ⊝ Λ) s sl rlv
  -> R' ∪ M ⊆ fst (getAnn ra)
  -> getAnn rlv ⊆ R'
  -> spill_max_kill k ZL Λ (R',M) s rlv sl
.
Proof.
  intros rena spillSnd rliveMin rlive R_sub rlv_sub'.
  general induction spillSnd; invc rlive; invc rena; invc rliveMin; cbn in rlv_sub'.
  - set (K' := R' \ (Exp.freeVars e ∪ getAnn al) ∪ (R' ∩ L)).
    assert (R' \ K' ∪ L ⊆ R0 \ K ∪ L) as rkl'_in_rkl2.
    {
      eapply rkl'_incl_rkl; eauto.
      - eapply rlive_min_incl_R; eauto. clear; cset_tac.
        (* + instantiate (1:=singleton x). clear; cset_tac.
        + specialize (rliveMin (singleton x)). invc rliveMin. eauto.*)
      - cbn in R_sub. clear - R_sub; cset_tac.
    }
    subst K'.
    econstructor; eauto;
      set (K' := R' \ (Exp.freeVars e ∪ getAnn al) ∪ (R' ∩ L)) in *;
      set (Kx':= (R' \ K' ∪ L) \ getAnn al) in *.
    + rewrite H13. eauto.
    + eapply IHspillSnd; eauto.
      * rewrite H14.
        cbn in R_sub. apply union_incl_split.
        -- apply add_struct_incl. rewrite !minus_incl. rewrite H0, H13, rlv_sub'.
           clear - R_sub. cset_tac.
        -- rewrite H13, rlv_sub', R_sub. cbn. clear; cset_tac.
      * enough (getAnn al \ singleton x ⊆ (R' \ K' ∪ L) \ Kx') as Hypo.
        { rewrite <-Hypo. clear; cset_tac. }
        rewrite <-inter_subset_equal with (s':=getAnn al);[| clear; cset_tac]. rewrite H17.
        subst K'. rewrite <-minus_union, minus_minus.
        setoid_rewrite <-rlv_sub' at 1. apply not_incl_minus; [clear; cset_tac|].
        subst Kx'. clear; cset_tac.
    (*
      setoid_rewrite <-union_subset_equal with (s0:=lv) at 8;[|eauto].
      setoid_rewrite <-union_subset_equal with (s0:=M0) at 11;[|eauto].
      setoid_rewrite <-H13 at 2. setoid_rewrite <-union_assoc at 2. setoid_rewrite union_assoc at 2.
      setoid_rewrite <-H0 at 2.
      rewrite H13. clear - H17. cset_tac.*)
    + subst K'. rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Exp.freeVars_live in H16. clear - H16; cset_tac.
    + rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto.
    + rewrite subset_cardinal with (s':={x; (R0 \ K ∪ L) \ Kx}); eauto.
      subst Kx'. rewrite minus_minus. apply incl_add_eq; split; [clear;cset_tac|].
      rewrite rkl'_in_rkl2. eapply rlive_min_incl_R in H20.
      * rewrite H20. clear; cset_tac.
      * clear; cset_tac.
      * eauto. 
  - econstructor; eauto.
    + rewrite H8; eauto.
    + rewrite <-minus_union.
      rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Op.freeVars_live in H10. clear - H10. cset_tac.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus. rewrite H1. rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto.
      clear; cset_tac.
  - eapply rlive_min_incl_R with (G:=∅) in spillSnd1 as spillSnd1'; [|clear;cset_tac|eauto].
    eapply rlive_min_incl_R with (G:=∅) in spillSnd2 as spillSnd2'; [|clear;cset_tac|eauto].
    econstructor; eauto.
    + rewrite H12; eauto.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus, <-rlv_sub'.
      apply Op.freeVars_live in H16. clear - H16; cset_tac.
    + rewrite <-minus_union. rewrite incl_minus_union;[|clear;cset_tac].
      rewrite minus_minus. rewrite H1.
      rewrite spillSnd1'. cbn.
      rewrite spillSnd2'. cbn.
      rewrite subset_cardinal with (s':=R0 \ K ∪ L); eauto. 
      cbn in R_sub; clear - R_sub H9; cset_tac.
    + eapply IHspillSnd1; eauto.
      * cbn in R_sub.
        rewrite <-minus_union, minus_minus, H6, H17, H18, rlv_sub', H12.
        setoid_rewrite H0 at 4. rewrite H12, rlv_sub'.
        rewrite H13. clear - R_sub. cbn. cset_tac.
      * rewrite <-inter_subset_equal with (s':=getAnn al1); [|clear;cset_tac]. setoid_rewrite H17 at 1.
        rewrite <-minus_union, minus_minus. setoid_rewrite rlv_sub' at 1. clear; cset_tac.
    + eapply IHspillSnd2; eauto.      
      * cbn in R_sub.
        rewrite <-minus_union, minus_minus, H6, H17, H18, rlv_sub', H12.
        setoid_rewrite H0 at 4. rewrite H12, rlv_sub'.
        rewrite H19. clear - R_sub. cbn. cset_tac.
      * rewrite <-inter_subset_equal with (s':=getAnn al2); [|clear;cset_tac]. setoid_rewrite H18 at 1.
        rewrite <-minus_union, minus_minus. setoid_rewrite rlv_sub' at 1. clear; cset_tac.
  - admit.
  - admit.
Admitted.

