Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import ExpVarsBounded SpillSound SpillUtil.



Set Implicit Arguments.



Definition is_live_min k ZL Λ s sl LV
  := forall R M, spill_sound k ZL Λ (R,M) s sl
                 -> LV ⊆ R ∪ M
.


Inductive live_min (k:nat)
  : list params -> list (⦃var⦄ * ⦃var⦄) -> ⦃var⦄ -> stmt -> spilling -> ann ⦃var⦄ -> Prop :=
| RMinLet ZL Λ x e s an sl LV lv G
  : live_min k ZL Λ (singleton x) s sl lv
    -> is_live_min k ZL Λ (stmtLet x e s) (ann1 an sl) (LV \ G)
    -> live_min k ZL Λ G (stmtLet x e s) (ann1 an sl) (ann1 LV lv)
| RMinIf ZL Λ e s1 s2 an sl1 sl2 LV lv1 lv2 G
  : live_min k ZL Λ ∅ s1 sl1 lv1
    -> live_min k ZL Λ ∅ s2 sl2 lv2
    -> is_live_min k ZL Λ (stmtIf e s1 s2) (ann2 an sl1 sl2) (LV \ G)
    -> live_min k ZL Λ G (stmtIf e s1 s2) (ann2 an sl1 sl2) (ann2 LV lv1 lv2)
| RMinReturn ZL Λ e an LV G
  : is_live_min k ZL Λ (stmtReturn e) (ann0 an) (LV \ G)
    -> live_min k ZL Λ G (stmtReturn e) (ann0 an) (ann0 LV)
| RMinApp ZL Λ f Y an LV G
  : is_live_min k ZL Λ (stmtApp f Y) (ann0 an) (LV \ G)
    -> live_min k ZL Λ G (stmtApp f Y) (ann0 an) (ann0 LV)
| RSpillFun ZL Λ G F t spl rms sl_F sl_t LV lv_F lv_t
  : (forall n Zs sl_s lv_s rm,
        get F n Zs
        -> get sl_F n sl_s
        -> get lv_F n lv_s
        -> get rms n rm
        -> live_min k (fst ⊝ F ++ ZL) (rms ++ Λ) (fst rm) (snd Zs) sl_s lv_s)
    -> live_min k (fst ⊝ F ++ ZL) (rms ++ Λ) ∅ t sl_t lv_t
    -> is_live_min k ZL Λ (stmtFun F t) (annF (spl, rms) sl_F sl_t) (LV \ G)
    -> live_min k ZL Λ G (stmtFun F t) (annF (spl, rms) sl_F sl_t) (annF LV lv_F lv_t)
.

Lemma live_min_G_anti k ZL Λ G G' s sl lv
  : live_min k ZL Λ G s sl lv
    -> G ⊆ G'
    -> live_min k ZL Λ G' s sl lv.
Proof.
  intros RLM Incl.
  general induction RLM; econstructor; intros; eauto;
    hnf; intros; rewrite <- Incl; eauto.
Qed.




Lemma live_min_getAnn k ZL Λ s sl lv R M :
  live_min k ZL Λ ∅ s sl lv
  -> spill_sound k ZL Λ (R,M) s sl
  -> getAnn lv ⊆ R ∪ M
.
Proof.
  intros rliveMin spillSnd. general induction rliveMin; cbn; unfold is_live_min in H;
                              rewrite <-minus_empty; try eapply H; eauto.
Qed.

Lemma live_min_getAnn_G k ZL Λ G s sl lv :
  live_min k ZL Λ G s sl lv
  -> (forall R M, spill_sound k ZL Λ (R,M) s sl -> getAnn lv ⊆ R ∪ M)
  -> live_min k ZL Λ ∅ s sl lv
.
Proof.
  intros rliveMin isMin.
  general induction rliveMin; econstructor; cbn in *; eauto;
    unfold is_live_min; intros; rewrite minus_empty; eapply isMin; eauto.
Qed.

Lemma live_min_incl_R k ZL Λ s sl lv R M G :
  G ⊆ R ∪ M
  -> spill_sound k ZL Λ (R, M) s sl
  -> live_min k ZL Λ G s sl lv
  -> getAnn lv ⊆ R ∪ M
.
Proof.
  intros Geq spillSnd rlive.
  general induction rlive; cbn;
    unfold is_live_min in *; rewrite <-union_subset_equal with (s':=R ∪ M); eauto;
      apply incl_minus_incl_union; [| | | |eapply H1;eauto]; eapply H; eauto.
Qed.

Lemma live_min_monotone k ZL Λ s sl G G' lv :
  G ⊆ G'
  -> live_min k ZL Λ G  s sl lv
  -> live_min k ZL Λ G' s sl lv
.
Proof.
  intros Geq rliveMin.
  general induction rliveMin; econstructor; eauto; unfold is_live_min in *; intros; rewrite <-Geq;
    eauto.
Qed.
