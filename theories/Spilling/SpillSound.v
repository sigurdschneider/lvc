Require Import List Map Env AllInRel Exp.
Require Import IL Annotation AnnP AutoIndTac Liveness.Liveness LabelsDefined.
Require Import ExpVarsBounded.
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
      -> Op.freeVars e ⊆ R\K ∪ L
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
      -> Op.freeVars e ⊆ R\K ∪ L
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
      -> list_union (Op.freeVars ⊝ Y) [=] R' ∪ M'
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



Lemma L_sub_SpM
      (ZL : list params)
      (k : nat)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  :
    spill_sound k ZL Λ (R,M) s sl
    -> getL sl ⊆ getSp sl ∪ M
.
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


Lemma spill_sound_ext Λ Λ' k ZL R M s sl :
  PIR2 _eq Λ Λ'
  -> spill_sound k ZL Λ  (R,M) s sl
  -> spill_sound k ZL Λ' (R,M) s sl
.
Proof.
  intros Λeq spillSnd. general induction spillSnd.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply PIR2_nth in Λeq as [[R_f' M_f'] [get_blk' blk'_eq]]; eauto. invc blk'_eq.
    econstructor; eauto. clear - H12 H14 H4 H5.
    + rewrite <-H12. eauto.
    + rewrite <-H14. eauto.
  - econstructor; eauto.
    + intros. inv_get. eapply H6; eauto.
      * apply PIR2_app; eauto.
      * apply surjective_pairing.
    + eapply IHspillSnd; eauto.
      apply PIR2_app; eauto.
Qed.


Lemma spill_sound_monotone Λ Λ' k ZL R M s sl :
  PIR2 (fun x y => fst x ⊆ fst y /\ snd x ⊆ snd y) Λ' Λ
  -> spill_sound k ZL Λ  (R,M) s sl
  -> spill_sound k ZL Λ' (R,M) s sl
.
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
      * apply PIR2_app; eauto. eapply PIR2_refl. split; reflexivity.
      * apply surjective_pairing.
    + eapply IHspillSnd; eauto.
      apply PIR2_app; eauto. eapply PIR2_refl. split; reflexivity.
Qed.

Lemma list_eq_PIR2 X `{OrderedType X} (L L':list X)
  : L === L'
    -> PIR2 _eq L L'.
Proof.
  intros. general induction H0; eauto using PIR2.
Qed.

Lemma spill_sound_ext2
      (k : nat)
      (ZL : list params) s
      (Λ Λ2 : list (⦃var⦄ * ⦃var⦄))
      (R R2 M M2 : ⦃var⦄)
      (sl sl2 : spilling)
  :
    PIR2 _eq Λ Λ2
    -> R [=] R2
    -> M [=] M2
    -> sl === sl2
    -> spill_sound k ZL Λ (R,M) s sl -> spill_sound k ZL Λ2 (R2,M2) s sl2
.
Proof.
  intros Λeq Req Meq sleq H.
  general induction H; simpl; eauto.
    destruct sl2; isabsurd;
      destruct a as [[Sp' L'] rm'].
  - destruct rm'; [|clear - sleq; invc sleq; invc H2; isabsurd].
    eapply SpillLet with (K:=K) (Kx:=Kx); simpl; eauto; invc sleq; invc H9; invc H10.
    + rewrite <-Req, <-H9. assumption.
    + rewrite <-Meq, <-H14, <-H9. assumption.
    + eapply IHspill_sound; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite H9, Meq; clear; cset_tac.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
  - invc sleq. invc H4.
    inv H8. inv H6. econstructor; eauto.
    rewrite <- H5. rewrite <- Req. eauto.
    rewrite <- H5, <- H9. rewrite <- Meq. eauto.
    rewrite <- H9. rewrite <- Req. eauto.
    rewrite <- Req, <- H9. eauto.
  - inv sleq. inv H8. inv H7; invc H12.
    eapply SpillIf with (K:=K).
    + rewrite <-H9, <-Req. assumption.
    + rewrite <-Meq, <-H9, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + rewrite <-Req, <-H14; assumption.
    + eapply IHspill_sound1; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite Meq, H9; clear; cset_tac.
    + eapply IHspill_sound2; eauto.
      * rewrite Req, H14; clear; cset_tac.
      * rewrite Meq, H9; clear; cset_tac.
  - PIR2_inv.
    invc sleq. invc H11. invc H17. invc H18.
    invc H15. invc H13.
    eapply SpillApp with (K:=K); eauto.
    + rewrite <- H16, <- Req; eauto.
    + rewrite <- H16, <- H18, <- Meq; eauto.
    + rewrite <- H18, <- Req; eauto.
    + rewrite <- H12, <- Req, <- H18; eauto.
    + rewrite <- H16, <- Meq, <-H14; eauto.
    + rewrite <- H19, <- H15; eauto.
    + rewrite <- H18, <- Req, <- H15; eauto.
    + rewrite <- H19, <- Meq, <- H16; eauto.
  - invc sleq. invc H11. invc H10.
    eapply SpillFun with (K:=K); eauto.
    + rewrite <- H11, <- Req; eauto.
    + rewrite <- H11, <- H17, <- Meq; eauto.
    + rewrite <- H17, <- Req. eauto.
    + eauto with len.
    + hnf in H16. eapply list_eq_length in H16. eauto with len.
    + intros. symmetry in H16.
      edestruct @list_eq_get; try eapply H16; eauto; dcr.
      exploit H4; eauto. rewrite H13. eauto.
    + intros. inv_get.
      exploit H14; eauto.
      edestruct @list_eq_get; try eapply H16; eauto; dcr.
      inv_get. invc H22.
      eapply H6; eauto.
      * eapply PIR2_app; eauto using list_eq_PIR2.
      * eapply H20.
      * eapply H21.
    + eapply IHspill_sound; eauto.
      * eapply PIR2_app; eauto using list_eq_PIR2.
      * rewrite <- Req, <- H17. eauto.
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
    + rewrite H9. set_simpl. cset_tac.
    + eauto.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H11. clear; cset_tac.
    + rewrite H15. clear; cset_tac.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + set_simpl. instantiate (1:=K ∪ Kx).
      rewrite <- minus_union. eauto.
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
