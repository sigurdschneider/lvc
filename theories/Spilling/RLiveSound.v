Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound SpillUtil.


Inductive rlive_sound
  : list params -> list (set var) -> stmt -> spilling -> ann (set var) -> Prop :=
| RLiveLet ZL Lv x e s Sp L sl lv (al:ann (set var))
  :  Sp ⊆ lv
     -> rlive_sound ZL Lv s sl al
     -> live_exp_sound e (lv ∪ L)
     -> (getAnn al \ singleton x) ⊆ lv ∪ L
     -> x ∈ getAnn al
     -> rlive_sound ZL Lv (stmtLet x e s) (ann1 (Sp,L,nil) sl) (ann1 lv al)
| RLiveIf Lv ZL e s1 s2 Sp L sl1 sl2 lv al1 al2
  :  Sp ⊆ lv
     -> rlive_sound ZL Lv s1 sl1 al1
     -> rlive_sound ZL Lv s2 sl2 al2
     -> live_op_sound e (lv ∪ L)
     -> getAnn al1 ⊆ lv ∪ L
     -> getAnn al2 ⊆ lv ∪ L
     -> rlive_sound ZL Lv (stmtIf e s1 s2) (ann2 (Sp,L,nil) sl1 sl2) (ann2 lv al1 al2)
| RLiveApp ZL Lv l Y Sp L R' M' lv blv Z
  : Sp ⊆ lv
    -> get ZL (counted l) Z
    -> get Lv (counted l) blv
    -> (blv \ of_list Z) ⊆ lv ∪ L
    -> (forall n y, get Y n y -> live_op_sound y (lv ∪ M' ∪ L))
    -> rlive_sound ZL Lv (stmtApp l Y) (ann0 (Sp,L,(R',M')::nil)) (ann0 lv)
| RLiveReturn ZL Lv e Sp L lv
  : Sp ⊆ lv
    -> live_op_sound e (lv ∪ L)
    -> rlive_sound ZL Lv (stmtReturn e) (ann0 (Sp,L,nil)) (ann0 lv)
| RLiveFun ZL Lv F t lv Sp L rms sl_F sl_t als alb
  : Sp ⊆ lv
    -> rlive_sound (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) t sl_t alb
    -> length F = length als
    -> (forall n Zs a sl_s, get F n Zs ->
                 get als n a ->
                 get sl_F n sl_s ->
                 rlive_sound (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) sl_s a)
    -> (forall n Zs a rm, get F n Zs ->
                    get als n a ->
                    get rms n rm ->
                    (fst rm) ⊆ getAnn a) (* don't add L here *)
    -> getAnn alb ⊆ lv ∪ L
    -> rlive_sound ZL Lv (stmtFun F t) (annF (Sp,L,rms) sl_F sl_t) (annF lv als alb)
.



Lemma rlive_sound_monotone
  : forall (ZL : 〔params〕) (LV LV' : 〔⦃var⦄〕) (s : stmt) (sl : spilling) (rlv : ann ⦃var⦄),
    rlive_sound ZL LV s sl rlv -> PIR2 Subset LV' LV -> rlive_sound ZL LV' s sl rlv.
Proof.
  intros ? ? ? ? ? ? rlvSnd pir2.
  general induction rlvSnd.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply PIR2_nth_2 in pir2 as [lv' [get_lv' lv'_sub]]; eauto.
    econstructor; eauto. rewrite lv'_sub. eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    + eapply IHrlvSnd. apply PIR2_app; [apply PIR2_refl|]; eauto.
    + intros; inv_get. eapply H2; eauto. apply PIR2_app; [apply PIR2_refl|]; eauto.
Qed.
