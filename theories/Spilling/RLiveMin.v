Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound SpillUtil.



Set Implicit Arguments.



Definition is_rlive_min k ZL Λ s sl Rlv
  := forall R M, spill_sound k ZL Λ (R,M) s sl
                 -> Rlv ⊆ R
.


Inductive rlive_min (k:nat)
  : list params -> list (⦃var⦄ * ⦃var⦄) -> ⦃var⦄ -> stmt -> spilling -> ann ⦃var⦄ -> Prop :=
| RMinLet ZL Λ x e s an sl Rlv rlv G
  : rlive_min k ZL Λ (singleton x) s sl rlv
    -> is_rlive_min k ZL Λ (stmtLet x e s) (ann1 an sl) (Rlv \ G)
    -> rlive_min k ZL Λ G (stmtLet x e s) (ann1 an sl) (ann1 Rlv rlv)
| RMinIf ZL Λ e s1 s2 an sl1 sl2 Rlv rlv1 rlv2 G
  : rlive_min k ZL Λ ∅ s1 sl1 rlv1
    -> rlive_min k ZL Λ ∅ s2 sl2 rlv2
    -> is_rlive_min k ZL Λ (stmtIf e s1 s2) (ann2 an sl1 sl2) (Rlv \ G)
    -> rlive_min k ZL Λ G (stmtIf e s1 s2) (ann2 an sl1 sl2) (ann2 Rlv rlv1 rlv2)
| RMinReturn ZL Λ e an Rlv G
  : is_rlive_min k ZL Λ (stmtReturn e) (ann0 an) (Rlv \ G)
    -> rlive_min k ZL Λ G (stmtReturn e) (ann0 an) (ann0 Rlv)
| RMinApp ZL Λ f Y an Rlv G
  : is_rlive_min k ZL Λ (stmtApp f Y) (ann0 an) (Rlv \ G)
    -> rlive_min k ZL Λ G (stmtApp f Y) (ann0 an) (ann0 Rlv)
| RSpillFun ZL Λ G F t spl rms sl_F sl_t Rlv rlv_F rlv_t
  : (forall n Zs sl_s rlv_s rm,
        get F n Zs
        -> get sl_F n sl_s
        -> get rlv_F n rlv_s
        -> get rms n rm
        -> rlive_min k (fst ⊝ F ++ ZL) (rms ++ Λ) (fst rm) (snd Zs) sl_s rlv_s)
    -> rlive_min k (fst ⊝ F ++ ZL) (rms ++ Λ) ∅ t sl_t rlv_t
    -> is_rlive_min k ZL Λ (stmtFun F t) (annF (spl, rms) sl_F sl_t) (Rlv \ G)
    -> rlive_min k ZL Λ G (stmtFun F t) (annF (spl, rms) sl_F sl_t) (annF Rlv rlv_F rlv_t)
.

Lemma rlive_min_G_anti k ZL Λ G G' s sl rlv
  : rlive_min k ZL Λ G s sl rlv
    -> G ⊆ G'
    -> rlive_min k ZL Λ G' s sl rlv.
Proof.
  intros RLM Incl.
  general induction RLM; econstructor; intros; eauto;
    hnf; intros; rewrite <- Incl; eauto.
Qed.




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


Lemma rlive_min_ext k ZL Λ Λ' s sl rlv G :
  Λ === Λ'
  -> rlive_min k ZL Λ  G s sl rlv
  -> rlive_min k ZL Λ' G s sl rlv
.
Proof.
  intros Λeq rlvMin. general induction rlvMin.
  - econstructor; eauto. unfold is_rlive_min.
    intros. admit.
Admitted.

  