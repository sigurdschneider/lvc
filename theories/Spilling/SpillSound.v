Require Import List Map Envs AllInRel Exp.
Require Import IL Annotation AnnP AutoIndTac Liveness.Liveness LabelsDefined.
Require Import ExpVarsBounded PartialOrder.
Require Export SpillUtil.

(** * Correctness Predicate with 5 inference rules *)
Inductive spill_sound (k:nat) :
  (list params)
  -> (list (⦃var⦄ * ⦃var⦄))
  -> (⦃var⦄ * ⦃var⦄)
  -> stmt
  -> spilling
  -> Prop
  :=
  | SpillLet
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K Kx : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> spill_sound k ZL Λ ({x;(R\K ∪ L)\Kx }, Sp ∪ M) s sl
      -> Exp.freeVars e ⊆ R\K ∪ L
      -> k > 0
      -> cardinal (R\K ∪ L) <= k
      -> cardinal ({x;((R\K) ∪ L)\Kx }) <= k
      -> spill_sound k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,nil) sl)
  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (e : op)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Ops.freeVars e ⊆ R\K ∪ L
      -> cardinal ((R\K) ∪ L) <= k
      -> spill_sound k ZL Λ (R,M) (stmtReturn e)
                    (ann0 (Sp,L,nil))
  | SpillIf
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> Ops.freeVars e ⊆ R\K ∪ L
      -> cardinal (R\K ∪ L) <= k
      -> spill_sound k ZL Λ (R\K ∪ L, Sp ∪ M) s sl_s
      -> spill_sound k ZL Λ (R\K ∪ L, Sp ∪ M) t sl_t
      -> spill_sound k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,nil) sl_s sl_t)
  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K R_f M_f R' M' : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> get ZL (counted f) Z
      -> get Λ (counted f) (R_f,M_f)
      -> R_f \ of_list Z ⊆ R\K ∪ L
      -> M_f \ of_list Z ⊆ Sp ∪ M
      -> list_union (Ops.freeVars ⊝ Y) [=] R' ∪ M'
      -> R' ⊆ R\K ∪ L
      -> M' ⊆ Sp ∪ M
      -> spill_sound k ZL Λ (R,M) (stmtApp f Y)
                     (ann0 (Sp,L, (R', M')::nil))
  | SpillFun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L K : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
    : Sp ⊆ R
      -> L ⊆ Sp ∪ M
      -> cardinal (R\K ∪ L) <= k
      -> length F = length sl_F
      -> length F = length rms
      -> (forall n rm, get rms n rm -> cardinal (fst rm) <= k)
      -> (forall n Zs rm sl_s, get rms n rm
                         -> get F n Zs
                         -> get sl_F n sl_s
                         -> spill_sound k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) rm (snd Zs) sl_s
        )
      -> spill_sound k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R\K ∪ L, Sp ∪ M) t sl_t
      -> spill_sound k ZL Λ (R,M) (stmtFun F t)
                    (annF (Sp,L,rms) sl_F sl_t)
.


Lemma Sp_sub_R
      (ZL : list params)
      (k : nat)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    spill_sound k ZL Λ (R,M) s sl
    -> getSp sl ⊆ R
.
Proof.
  intros spillSnd.
  invc spillSnd;
    cset_tac.
Qed.


Lemma L_sub_SpM (ZL : list params) (k : nat) (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄) (s : stmt) (sl : spilling)
  : spill_sound k ZL Λ (R,M) s sl -> getL sl ⊆ getSp sl ∪ M .
Proof.
  intros spillSnd.
  invc spillSnd; cset_tac.
Qed.
Inductive spill_live
          (VD : ⦃var⦄)
  :
    spilling -> ann (set var) -> Prop
  :=
  | SomeSpLv0 a b
    : spill_live VD (ann0 a) (ann0 b)
  | SomeSpLv1 a b sl lv
    : spill_live VD sl lv
      -> spill_live VD (ann1 a sl) (ann1 b lv)
  | SomeSpLv2 a b sl1 sl2 lv1 lv2
    : spill_live VD sl1 lv1
      -> spill_live VD sl2 lv2
      -> spill_live VD (ann2 a sl1 sl2) (ann2 b lv1 lv2)
  | SomeSpLvF a b sl_F sl_t lv_F lv_t rms
    : PIR2 Equal (merge ⊝ rms) (getAnn ⊝ lv_F)
      -> spill_live VD sl_t lv_t
      -> (forall n rm,
            get rms n rm
            -> fst rm ⊆ VD /\ snd rm ⊆ VD)
      -> (forall n sl_s lv_s,
            get sl_F n sl_s
            -> get lv_F n lv_s
            -> spill_live VD sl_s lv_s
        )
      -> spill_live VD (annF (a, rms) sl_F sl_t)
                              (annF b lv_F lv_t)
.

Lemma spill_sound_ext Λ Λ' k ZL R M s sl
  : poEq Λ Λ'
    -> spill_sound k ZL Λ  (R,M) s sl
    -> spill_sound k ZL Λ' (R,M) s sl .
Proof.
  intros Λeq spillSnd. general induction spillSnd.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply PIR2_nth in Λeq as [[R_f' M_f'] [get_blk' blk'_eq]]; eauto.
    invc blk'_eq; simpl in *.
    econstructor; eauto.
    + rewrite <- H4, H9. reflexivity.
    + rewrite <- H10, H5. eauto.
  - econstructor; eauto.
    + intros. inv_get. eapply H6; eauto.
      * apply surjective_pairing.
Qed.

Lemma spill_sound_monotone Λ Λ' k ZL R M s sl
  : poLe Λ' Λ
    -> spill_sound k ZL Λ  (R,M) s sl
    -> spill_sound k ZL Λ' (R,M) s sl.
Proof.
  intros Λeq spillSnd. general induction spillSnd.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply PIR2_nth_2 in Λeq as [[R_f' M_f'] [get_blk' blk'_eq]]; eauto. cbn in *. invc blk'_eq.
    econstructor; eauto; cbn in *.
    + rewrite H9. eauto.
    + rewrite H10. eauto.
  - econstructor; eauto.
    + intros. inv_get. eapply H6; eauto.
      * apply surjective_pairing.
Qed.

Lemma list_eq_PIR2 X `{OrderedType X} (L L':list X)
  : L === L' -> PIR2 _eq L L'.
Proof.
  intros. general induction H0; eauto using PIR2.
Qed.

Smpl Add match goal with
         | [ H : S _ < 0 |- _ ] => exfalso; inv H
         | [ H : S _ <=  0 |- _ ] => exfalso; inv H
         end : inv_trivial.

Lemma spill_sound_ext2 (k : nat) (ZL : list params) s (Λ Λ2 : list (⦃var⦄ * ⦃var⦄))
      (R R2 M M2 : ⦃var⦄) (sl sl2 : spilling)
  :
    Λ === Λ2
    -> R [=] R2
    -> M [=] M2
    -> sl === sl2
    -> spill_sound k ZL Λ (R,M) s sl -> spill_sound k ZL Λ2 (R2,M2) s sl2.
Proof.
  intros Λeq Req Meq sleq H.
  general induction H; simpl; eauto.
    destruct sl2; isabsurd;
      destruct a as [[Sp' L'] rm'];
      clear_trivial_eqs.
  - eapply SpillLet with (K:=K) (Kx:=Kx); simpl; eauto with cset.
    + rewrite <-Req, <-H9. assumption.
    + rewrite <-Meq, <-H7, <-H9. assumption.
    + eapply IHspill_sound; eauto.
      * rewrite Req, H7; clear; cset_tac.
      * rewrite H9, Meq; clear; cset_tac.
    + rewrite <-Req, <-H7; assumption.
    + rewrite <-Req, <-H7; assumption.
    + rewrite <-Req, <-H7; assumption.
  - invc sleq. destruct b as [[? ?] ?]. clear_trivial_eqs.
    econstructor; eauto.
    + rewrite <- H4. rewrite <- Req. eauto.
    + rewrite <- H4, <- H5. rewrite <- Meq. eauto.
    + rewrite <- H5. rewrite <- Req. eauto.
    + rewrite <- Req, <- H5. eauto.
  - invc sleq.
    destruct b as [[? ?] ?]. clear_trivial_eqs.
    eapply SpillIf with (K:=K).
    + rewrite <-H8, <-Req. assumption.
    + rewrite <-Meq, <-H8, <-H6; assumption.
    + rewrite <-Req, <-H6; assumption.
    + rewrite <-Req, <-H6; assumption.
    + eapply IHspill_sound1; eauto.
      * rewrite Req, H6; clear; cset_tac.
      * rewrite Meq, H8; clear; cset_tac.
    + eapply IHspill_sound2; eauto.
      * rewrite Req, H6; clear; cset_tac.
      * rewrite Meq, H8; clear; cset_tac.
  - hnf in Λeq. PIR2_inv.
    invc sleq.
    destruct b as [[? ?] ?]. destruct x. simpl in *.
    clear_trivial_eqs.
    destruct y. simpl in *.
    invc H16.
    eapply SpillApp with (K:=K); eauto;
      try rewrite <- H13;
      try rewrite <- H14;
      try rewrite <- Req;
      try rewrite <- Req;
      try rewrite <- Λeq0;
      try rewrite <- Λeq2;
      try rewrite <- H10;
      try rewrite <- H11;
      try rewrite <- Meq; eauto.
  - invc sleq.
    destruct b as [[? ?] ?]. clear_trivial_eqs.
    eapply SpillFun with (K:=K); eauto.
    + rewrite <- H11, <- Req; eauto.
    + rewrite <- H9, <- H11, <- Meq; eauto.
    + rewrite <- H9, <- Req. eauto.
    + eauto with len.
    + hnf in H8. eapply PIR2_length in H8. eauto with len.
    + intros. hnf in H8. inv_get.
      edestruct @PIR2_nth_2; try eapply H8; eauto; dcr.
      exploit H4; eauto.
      rewrite <- H17. eauto.
    + intros. inv_get.
      exploit H7; eauto.
      edestruct @PIR2_nth_2; try eapply H8; eauto; dcr.
      inv_get. destruct x,rm; clear_trivial_eqs.
      eapply H6; eauto.
      * eapply PIR2_app; eauto.
      * eauto.
      * eauto.
      * eapply H14; eauto.
    + eapply IHspill_sound; eauto.
      * eapply PIR2_app; eauto.
      * rewrite <- Req, <- H9. eauto.
      * rewrite <- H11. rewrite <- Meq. eauto.
Qed.

Instance spill_sound_morphX k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound_ext2; eauto; try reflexivity.
    eapply H2. eapply H3.
  - eapply spill_sound_ext2; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_implX k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext2; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_flip_implX k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> flip impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext2; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morphX' k ZL Λ
  : Proper (@pe _ _ ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound_ext2; eauto; try reflexivity.
  - eapply spill_sound_ext2; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Lemma spill_sound_spill_ext k ZL Λ (R0 M0:set var) s sl
  (SPS: spill_sound k ZL Λ (R0, getSp sl ∪ M0) s (clear_Sp sl))
  (Sp_sub : getSp sl [<=] R0)
  (Rsmall : cardinal R0 <= k)
  : spill_sound k ZL Λ (R0, M0) s sl.
Proof.
  destruct sl; invc SPS; simpl in *; clear_trivial_eqs.
  - destruct p. econstructor; eauto.
  - simpl in *. destruct p. econstructor; eauto.
  - destruct p; simpl in *. econstructor; eauto.
    set_simpl. eauto.
  - destruct p; simpl in *. set_simpl.
    econstructor; eauto.
  - destruct a. destruct p.
    econstructor; eauto.
    simpl in *. set_simpl. eauto.
Qed.

Lemma spill_sound_incl_R k ZL Λ R R' s sl M
  (SPS:spill_sound k ZL Λ (R,M) s sl)
  (Incl: R ⊆ R')
  (Card:cardinal R' <= k)
  : spill_sound k ZL Λ (R',M) s sl.
Proof.
  destruct sl; invc SPS; simpl in *.
  - eapply SpillReturn with (K:=K ∪ R' \ R); eauto with cset.
    + rewrite H7.
      revert Incl; clear_all; cset_tac.
    + rewrite <- H8. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
  - eapply SpillApp with (K:=K ∪ R' \ R); eauto.
    + eauto with cset.
    + rewrite <- H4. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
    + rewrite H7.
      revert Incl; clear_all; cset_tac.
    + rewrite H13.
      revert Incl; clear_all; cset_tac.
  - eapply SpillLet with (K:=K ∪ R' \ R); eauto.
    + eauto with cset.
    + assert ({x; (R' \ (K ∪ R' \ R) ∪ L) \ Kx}
                [=] {x; (R \ K ∪ L) \ Kx}). {
        revert Incl; clear_all; cset_tac.
      }
      rewrite H. eauto.
    + rewrite H8.
      revert Incl; clear_all; cset_tac.
    + rewrite <- H11. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
    + rewrite <- H12. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
  - assert (EQ:R' \ (K ∪ R' \ R) ∪ L
              [=] R \ K ∪ L). {
      revert Incl; clear_all; cset_tac.
    }
    eapply SpillIf with (K:=K ∪ R' \ R); eauto;
                                try rewrite EQ; eauto with cset.
  - assert (EQ:R' \ (K ∪ R' \ R) ∪ L
              [=] R \ K ∪ L). {
      revert Incl; clear_all; cset_tac.
    }
    eapply SpillFun with (K:=K ∪ R' \ R); eauto;
                                try rewrite EQ; eauto.
    + eauto with cset.
Qed.

Lemma spill_sound_load_ext k ZL Λ (R0 M0:set var) Ka s sl
      (card:cardinal R0 <= k)
      (card2: cardinal (R0 \ Ka ∪ getL sl) <= k)
      (SPS: spill_sound k ZL Λ (R0 \ Ka ∪ getL sl, M0) s (clear_L sl))
      (L_sub : getL sl [<=] M0)
      (SpE:getSp sl [=] ∅)
  : spill_sound k ZL Λ (R0, M0) s sl.
Proof.
  destruct sl; inv SPS; simpl in *; clear_trivial_eqs;
    try destruct p as [Sp L]; simpl in *.
  - eapply SpillReturn with (K:=Ka).
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H9. cset_tac.
    + eauto.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H11. clear; cset_tac.
    + rewrite H15. clear; cset_tac.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + instantiate (1:=K ∪ Kx).
      rewrite <- minus_union. eauto.
      revert H10; clear. set_simpl. eauto.
    + rewrite H11. clear; cset_tac.
    + rewrite <- H14.
      eapply subset_cardinal.
      clear_all. cset_tac'.
  - eapply SpillIf with (K:=K ∪ Ka).
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H11. clear_all. cset_tac.
    + rewrite <- card2. eapply subset_cardinal. clear; cset_tac.
    + eapply spill_sound_incl_R; eauto.
      * clear; cset_tac.
      * rewrite <- card2. eapply subset_cardinal.
        clear; cset_tac.
    + eapply spill_sound_incl_R; eauto.
      * clear; cset_tac.
      * rewrite <- card2. eapply subset_cardinal.
        clear; cset_tac.
  - destruct a, p; simpl in *.
    econstructor; eauto.
    + rewrite SpE; eauto with cset.
    + rewrite L_sub; eauto with cset.
    + eapply spill_sound_incl_R; eauto.
      * clear; cset_tac.
Qed.
