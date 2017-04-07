Require Import List Map Env AllInRel Exp.
Require Import IL Annotation AnnP InRel.
Require Import LabelsDefined SpillSound SpillUtil.

Lemma list_eq_PIR2 X `{OrderedType X} (L L':list X)
  : L === L'
    -> PIR2 _eq L L'.
Proof.
  intros. general induction H0; eauto using PIR2.
Qed.

Lemma spill_sound_ext
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
    invc sleq. invc H10. invc H16. invc H17.
    invc H14. invc H12.
    eapply SpillApp with (K:=K); eauto.
    + rewrite <- H15, <- Req; eauto.
    + rewrite <- H15, <- H17, <- Meq; eauto.
    + rewrite <- H17, <- Req; eauto.
    + rewrite <- H11, <- Req, <- H17; eauto.
    + rewrite <- H13, <- Meq, <- H15; eauto.
    + rewrite <- H18, <- Req, <- H17; eauto.
    + rewrite <- H18, <- Meq, <- H15; eauto.
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
  - eapply spill_sound_ext; eauto; try reflexivity.
    eapply H2. eapply H3.
  - eapply spill_sound_ext; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_implX k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_flip_implX k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> flip impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morphX' k ZL Λ
  : Proper (@pe _ _ ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound_ext; eauto; try reflexivity.
  - eapply spill_sound_ext; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.


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
      (R M Sp L Kx : ⦃var⦄)
      (x : var)
      (e : exp)
      (s : stmt)
      (sl : spilling)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (spill_sub : spill_sound k ZL Λ ({x;R\Kx},M) s sl)
      (kgt0: k > 0)
      (card : cardinal {x; R \ Kx } <= k)
      (inR : Exp.freeVars e ⊆ R)
      : spill_sound k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,nil) sl)
  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L : ⦃var⦄)
      (e : op)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (inVar : Op.freeVars e ⊆ R)
      : spill_sound k ZL Λ (R,M) (stmtReturn e) (ann0 (Sp,L,nil))
  | SpillIf
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L : ⦃var⦄)
      (e : op)
      (s t : stmt)
      (sl_s sl_t : spilling)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (inVar : Op.freeVars e ⊆ R)
      (spill_s : spill_sound k ZL Λ (R,M) s sl_s)
      (spill_t : spill_sound k ZL Λ (R,M) t sl_t)
    : spill_sound k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,nil) sl_s sl_t)
  | SpillApp
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L R_f M_f R' M' : ⦃var⦄)
      (f : lab)
      (Z : params)
      (Y : args)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (getZ : get ZL (counted f) Z)
      (getΛ : get Λ (counted f) (R_f,M_f))
      (Rf_sub : R_f \ of_list Z ⊆ R)
      (Mf_sub : M_f \ of_list Z ⊆ M)
      (inVar : list_union (Op.freeVars ⊝ Y) ⊆ R ∪ M')
      (M_sub : M' ⊆ M)
      : spill_sound k ZL Λ (R,M) (stmtApp f Y)
                     (ann0 (Sp,L, (R', M')::nil))
  | SpillFun
      (ZL : list params)
      (Λ rms : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L : ⦃var⦄)
      (F : list (params * stmt))
      (t : stmt)
      (sl_F : list spilling)
      (sl_t : spilling)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (len_Fsl : length F = length sl_F)
      (len_Frms : length F = length rms)
      (card : (forall n Rf Mf, get rms n (Rf,Mf) -> cardinal Rf <= k))
      (spill_F : (forall n Zs Rf Mf sl_s, get rms n (Rf,Mf)
                         -> get F n Zs
                         -> get sl_F n sl_s
                         -> spill_sound k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) (Rf,Mf) (snd Zs) sl_s
        ))
      (spill_t : spill_sound k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R,M) t sl_t)
      : spill_sound k ZL Λ (R,M) (stmtFun F t)
                    (annF (Sp,L,rms) sl_F sl_t)
  | SpillLoad
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M K : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (Sp_empty : getSp sl [=] ∅)
      (L_sub : getL sl ⊆ M)
      (card :  cardinal (R \ K ∪ getL sl) <= k)
      (spill_s : spill_sound k ZL Λ (R \ K ∪ getL sl, M) s (clear_L sl))
    : spill_sound k ZL Λ (R,M) s sl
  | SpillSpill
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M: ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (Sp_sub : getSp sl ⊆ R)
      (spill_s : spill_sound k ZL Λ (R, getSp sl ∪ M) s (clear_Sp sl))
    : spill_sound k ZL Λ (R,M) s sl
.


Smpl Add
     match goal with
     | [ H : @equiv (@ann _) _ _ ?A ?B |- _ ] => inv_if_one_ctor H A B
     end : inv_trivial.


Instance clear_Sp_morph
  : Proper (@equiv _ (ann_R _eq) _ ==> equiv) clear_Sp.
Proof.
  unfold Proper, respectful; intros.
  destruct x; clear_trivial_eqs; simpl; econstructor; eauto.
  * econstructor; eauto;
      rewrite H1; reflexivity.
  * econstructor; eauto;
      rewrite H2; reflexivity.
  * econstructor; eauto;
      rewrite H3; reflexivity.
  * econstructor; eauto;
      rewrite H3; reflexivity.
Qed.

Instance clear_L_morph
  : Proper (@equiv _ (ann_R _eq) _ ==> equiv) clear_L.
Proof.
  unfold Proper, respectful; intros.
  destruct x; clear_trivial_eqs; simpl; econstructor; eauto.
  * econstructor; eauto;
      rewrite H1; reflexivity.
  * econstructor; eauto;
      rewrite H2; reflexivity.
  * econstructor; eauto;
      rewrite H3; reflexivity.
  * econstructor; eauto;
      rewrite H3; reflexivity.
Qed.


Lemma spill_sound_ext'
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
  general induction H; simpl; eauto; clear_trivial_eqs.
  - eapply SpillLet with (Kx:=Kx); simpl; eauto.
    + rewrite <-H2. assumption.
    + rewrite <-H7. assumption.
    + eapply IHspill_sound; eauto.
      rewrite Req. reflexivity.
    + rewrite <- Req. eauto.
    + rewrite <- Req. eauto.
  - econstructor; eauto;
      try rewrite <- H1; try rewrite <- H5; try rewrite <- Req; eauto.
  - eapply SpillIf; try eapply IHspill_sound1; try eapply IHspill_sound2; eauto;
      try rewrite <- H4; try rewrite <- H9; try rewrite <- Req; eauto.
  - PIR2_inv.
    eapply SpillApp; eauto;
      (try rewrite <- H1); (try rewrite <- H5); (try rewrite <- H3);
        (try rewrite <- H4); (try rewrite <- H8); (try rewrite <- Req);
          try rewrite <- Req0; try rewrite <- H7;
          (try rewrite <- Meq); eauto.
  - eapply SpillFun; eauto.
    + rewrite <- H4; eauto.
    + rewrite <- H10; eauto.
    + eauto with len.
    + eapply list_eq_length in H9. eauto with len.
    + intros. symmetry in H9.
      edestruct @list_eq_get; try eapply H9; eauto; dcr. inv H6.
      exploit card; eauto. rewrite H12; eauto.
    + intros. inv_get.
      exploit H7; eauto.
      edestruct @list_eq_get; try eapply H9; eauto; dcr.
      inv_get.
      eapply H; eauto.
      * eapply PIR2_app; eauto using list_eq_PIR2.
      * assumption.
      * assumption.
    + eapply IHspill_sound; eauto.
      * eapply PIR2_app; eauto using list_eq_PIR2.
  - eapply SpillLoad; eauto.
    + rewrite <- sleq; eauto.
    + rewrite <- sleq, <- Meq; eauto.
    + rewrite <- Req, <- sleq; eauto.
    + eapply IHspill_sound; eauto.
      * rewrite Req, sleq. reflexivity.
      * rewrite sleq. reflexivity.
  - eapply SpillSpill; eauto.
    + rewrite <- sleq, <- Req; eauto.
    + eapply IHspill_sound; eauto.
      * rewrite Meq, sleq. eauto.
      * rewrite sleq. reflexivity.
Qed.


Instance spill_sound_morph k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound_ext'; eauto; try reflexivity.
    eapply H2. eapply H3.
  - eapply spill_sound_ext'; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_impl k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext'; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph_flip_impl k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> flip impl) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst; intros; inv H.
  - eapply spill_sound_ext'; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound_morph' k ZL Λ
  : Proper (@pe _ _ ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound_ext'; eauto; try reflexivity.
  - eapply spill_sound_ext'; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.


Lemma spill_sound_spill_ext k ZL Λ (R0 M0:set var) s sl
  (SPS: SpillSound.spill_sound k ZL Λ (R0, getSp sl ∪ M0) s (clear_Sp sl))
  (Sp_sub : getSp sl [<=] R0)
  (Rsmall : cardinal R0 <= k)
  : SpillSound.spill_sound k ZL Λ (R0, M0) s sl.
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
  (SPS:SpillSound.spill_sound k ZL Λ (R,M) s sl)
  (Incl: R ⊆ R')
  (Card:cardinal R' <= k)
  : SpillSound.spill_sound k ZL Λ (R',M) s sl.
Proof.
  destruct sl; invc SPS; simpl in *.
  - eapply SpillSound.SpillReturn with (K:=K ∪ R' \ R); eauto with cset.
    + rewrite H7.
      revert Incl; clear_all; cset_tac.
    + rewrite <- H8. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
  - eapply SpillSound.SpillApp with (K:=K ∪ R' \ R); eauto.
    + eauto with cset.
    + rewrite <- H4. eapply subset_cardinal.
      revert Incl; clear_all; cset_tac.
    + rewrite H7.
      revert Incl; clear_all; cset_tac.
    + rewrite H12.
      revert Incl; clear_all; cset_tac.
  - eapply SpillSound.SpillLet with (K:=K ∪ R' \ R); eauto.
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
    eapply SpillSound.SpillIf with (K:=K ∪ R' \ R); eauto;
                                try rewrite EQ; eauto with cset.
  - assert (EQ:R' \ (K ∪ R' \ R) ∪ L
              [=] R \ K ∪ L). {
      revert Incl; clear_all; cset_tac.
    }
    eapply SpillSound.SpillFun with (K:=K ∪ R' \ R); eauto;
                                try rewrite EQ; eauto.
    + eauto with cset.
Qed.

Lemma spill_sound_load_ext k ZL Λ (R0 M0:set var) Ka s sl
      (card:cardinal R0 <= k)
      (card2: cardinal (R0 \ Ka ∪ getL sl) <= k)
      (SPS: SpillSound.spill_sound k ZL Λ (R0 \ Ka ∪ getL sl, M0) s (clear_L sl))
      (L_sub : getL sl [<=] M0)
      (SpE:getSp sl [=] ∅)
  : SpillSound.spill_sound k ZL Λ (R0, M0) s sl.
Proof.
  destruct sl; inv SPS; simpl in *; clear_trivial_eqs;
    try destruct p as [Sp L]; simpl in *.
  - eapply SpillSound.SpillReturn with (K:=Ka).
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H9. set_simpl. cset_tac.
    + eauto.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + rewrite H12. clear; cset_tac.
    + rewrite H14. clear; cset_tac.
  - econstructor; eauto.
    + rewrite SpE. eauto with cset.
    + rewrite L_sub. eauto with cset.
    + set_simpl. instantiate (1:=K ∪ Kx).
      rewrite <- minus_union. eauto.
    + rewrite H11. clear; cset_tac.
    + rewrite <- H14.
      eapply subset_cardinal.
      clear_all. cset_tac'.
  - eapply SpillSound.SpillIf with (K:=K ∪ Ka).
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

Lemma spill_sound_spill_sound3
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M  : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (Rsmall: cardinal R <= k)
  : spill_sound k ZL Λ (R,M) s sl
    -> SpillSound.spill_sound k ZL Λ (R, M) s sl.
Proof.
  intros SPS.
  general induction SPS.
  - eapply SpillSound.SpillLet with (Kx:=Kx);
      set_simpl; eauto with cset.
    + set_simpl. eauto.
    + set_simpl. eauto.
    + set_simpl; eauto.
  - eapply SpillSound.SpillReturn;
      set_simpl; eauto with cset.
    + set_simpl. eauto.
  - eapply SpillSound.SpillIf;
      set_simpl; eauto with cset.
    + set_simpl; eauto.
    + set_simpl; eauto.
    + set_simpl; eauto.
  - eapply SpillSound.SpillApp;
      set_simpl; eauto with cset.
    + set_simpl; eauto.
    + set_simpl; eauto.
  - eapply SpillSound.SpillFun;
      set_simpl; eauto with cset.
    + instantiate (1:={}). set_simpl. eauto.
    + intros. destruct rm. exploit card; eauto.
    + intros. destruct rm. eapply H; try reflexivity; eauto.
    + set_simpl. eauto.
  - eapply spill_sound_load_ext; eauto.
  - eapply spill_sound_spill_ext; eauto.
Qed.
