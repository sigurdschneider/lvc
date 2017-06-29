Require Import List Map Env AllInRel Exp.
Require Import IL Annotation AnnP InRel.
Require Import LabelsDefined SpillSound SpillUtil.


(** * Correctness Predicate with 7 inference rules *)


Inductive spill_sound7 (k:nat) :
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
      (spill_sub : spill_sound7 k ZL Λ ({x;R\Kx},M) s sl)
      (kgt0: k > 0)
      (card : cardinal {x; R \ Kx } <= k)
      (inR : Exp.freeVars e ⊆ R)
      : spill_sound7 k ZL Λ (R,M) (stmtLet x e s) (ann1 (Sp,L,nil) sl)
  | SpillReturn
      (ZL : list (params))
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M Sp L : ⦃var⦄)
      (e : op)
      (Sp_empty : Sp [=] ∅)
      (L_empty : L [=] ∅)
      (inVar : Op.freeVars e ⊆ R)
      : spill_sound7 k ZL Λ (R,M) (stmtReturn e) (ann0 (Sp,L,nil))
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
      (spill_s : spill_sound7 k ZL Λ (R,M) s sl_s)
      (spill_t : spill_sound7 k ZL Λ (R,M) t sl_t)
    : spill_sound7 k ZL Λ (R,M) (stmtIf e s t) (ann2 (Sp,L,nil) sl_s sl_t)
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
      (inVar : list_union (Op.freeVars ⊝ Y) ⊆ R' ∪ M')
      (R_sub : R' ⊆ R)
      (M_sub : M' ⊆ M)
      : spill_sound7 k ZL Λ (R,M) (stmtApp f Y)
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
                         -> spill_sound7 k ((fst ⊝ F) ++ ZL)
                                       (rms ++ Λ) (Rf,Mf) (snd Zs) sl_s
        ))
      (spill_t : spill_sound7 k ((fst ⊝ F) ++ ZL) (rms ++ Λ) (R,M) t sl_t)
      : spill_sound7 k ZL Λ (R,M) (stmtFun F t)
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
      (spill_s : spill_sound7 k ZL Λ (R \ K ∪ getL sl, M) s (clear_L sl))
    : spill_sound7 k ZL Λ (R,M) s sl
  | SpillSpill
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M: ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (Sp_sub : getSp sl ⊆ R)
      (spill_s : spill_sound7 k ZL Λ (R, getSp sl ∪ M) s (clear_Sp sl))
    : spill_sound7 k ZL Λ (R,M) s sl
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

Lemma spill_sound7_ext'
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
    -> spill_sound7 k ZL Λ (R,M) s sl -> spill_sound7 k ZL Λ2 (R2,M2) s sl2
.
Proof.
  intros Λeq Req Meq sleq H.
  general induction H; simpl; eauto; clear_trivial_eqs.
  - eapply SpillLet with (Kx:=Kx); simpl; eauto.
    + rewrite <-H2. assumption.
    + rewrite <-H7. assumption.
    + eapply IHspill_sound7; eauto.
      rewrite Req. reflexivity.
    + rewrite <- Req. eauto.
    + rewrite <- Req. eauto.
  - econstructor; eauto;
      try rewrite <- H1; try rewrite <- H5; try rewrite <- Req; eauto.
  - eapply SpillIf; try eapply IHspill_sound71; try eapply IHspill_sound72; eauto;
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
    + eapply IHspill_sound7; eauto.
      * eapply PIR2_app; eauto using list_eq_PIR2.
  - eapply SpillLoad; eauto.
    + rewrite <- sleq; eauto.
    + rewrite <- sleq, <- Meq; eauto.
    + rewrite <- Req, <- sleq; eauto.
    + eapply IHspill_sound7; eauto.
      * rewrite Req, sleq. reflexivity.
      * rewrite sleq. reflexivity.
  - eapply SpillSpill; eauto.
    + rewrite <- sleq, <- Req; eauto.
    + eapply IHspill_sound7; eauto.
      * rewrite Meq, sleq. eauto.
      * rewrite sleq. reflexivity.
Qed.


Instance spill_sound7_morph k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound7 k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound7_ext'; eauto; try reflexivity.
    eapply H2. eapply H3.
  - eapply spill_sound7_ext'; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound7_morph_impl k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> impl) (spill_sound7 k ZL Λ).
Proof.
  unfold Proper, respectful, impl; intros; subst; intros; inv H.
  - eapply spill_sound7_ext'; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound7_morph_flip_impl k ZL Λ
  : Proper (_eq ==> eq ==> @equiv _ _ _ ==> flip impl) (spill_sound7 k ZL Λ).
Proof.
  unfold Proper, respectful, flip, impl; intros; subst; intros; inv H.
  - eapply spill_sound7_ext'; try eapply H2; try reflexivity.
    rewrite H0; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Instance spill_sound7_morph' k ZL Λ
  : Proper (@pe _ _ ==> eq ==> @equiv _ _ _ ==> iff) (spill_sound7 k ZL Λ).
Proof.
  unfold Proper, respectful; intros; subst; split; intros; inv H.
  - eapply spill_sound7_ext'; eauto; try reflexivity.
  - eapply spill_sound7_ext'; try eapply H0; try reflexivity.
    rewrite H2; eauto. rewrite H3; eauto. symmetry; eauto.
Qed.

Lemma spill_sound7_spill_sound
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M  : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
      (Rsmall: cardinal R <= k)
  : spill_sound7 k ZL Λ (R,M) s sl
    -> spill_sound k ZL Λ (R, M) s sl.
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
  - eapply SpillSound.SpillFun;
      set_simpl; eauto with cset.
    + instantiate (1:={}). set_simpl. eauto.
    + intros. destruct rm. exploit card; eauto.
    + intros. destruct rm. eapply H; try reflexivity; eauto.
    + set_simpl. eauto.
  - eapply spill_sound_load_ext; eauto.
  - eapply spill_sound_spill_ext; eauto.
Qed.


Lemma spill_sound_spill_sound7
      (k : nat)
      (ZL : list params)
      (Λ : list (⦃var⦄ * ⦃var⦄))
      (R M  : ⦃var⦄)
      (s : stmt)
      (sl : spilling)
  : spill_sound k ZL Λ (R,M) s sl
    -> spill_sound7 k ZL Λ (R, M) s sl.
Proof.
  intros spillSnd.
  general induction spillSnd; eapply SpillSpill; eauto; eapply SpillLoad; eauto;
    econstructor; eauto.
  intros. exploit H4; eauto.
Qed.
