Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound SpillUtil.



Set Implicit Arguments.

(** * Register Liveness *)

Fixpoint reg_live
         (ZL : list params)
         (Lv : list ⦃var⦄)
         (G : ⦃var⦄)
         (s : stmt)
         (sl : spilling)
         {struct s}
  : ann ⦃var⦄
  :=
    match s, sl with
    | stmtLet x e s, ann1 (Sp, L, _) sl'
                          (* maybe we have to add Exp.freeVars e and etc.
                             getAnn al [<=] {x; R
*)
      => let lv_s := reg_live ZL Lv (singleton x) s sl' in
        ann1 (G ∪ Sp ∪ (((getAnn lv_s) \ singleton x ∪ Exp.freeVars e) \ L)) lv_s

    | stmtReturn e, ann0 (Sp, L, _)
      => ann0 (G ∪ Sp ∪ (Op.freeVars e \ L))

    | stmtIf e s1 s2, ann2 (Sp, L, _) sl1 sl2
      => let lv1 := reg_live ZL Lv ∅ s1 sl1 in
        let lv2 := reg_live ZL Lv ∅ s2 sl2 in
        ann2 (G ∪ Sp ∪ ((getAnn lv1 ∪ getAnn lv2 ∪ Op.freeVars e) \ L)) lv1 lv2

    | stmtApp f Y, ann0 (Sp, L, (_,Sl)::nil)
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (G ∪ Sp ∪ (((list_union (Op.freeVars ⊝ Y) \ Sl) ∪ blv \ of_list Z) \ L))

    | stmtFun F t, annF (Sp, L, rms) sl_F sl_t
      => let lv_t := reg_live (fst ⊝ F ++ ZL) (fst ⊝ rms ++ Lv) ∅ t sl_t in
        let lv_F := (fun ps (rmsl : spilling * ⦃var⦄)
                     => let (sl_s, Rf) := rmsl in
                       reg_live (fst ⊝ F   ++ ZL)
                                (fst ⊝ rms ++ Lv)
                                (Rf)
                                (snd ps)
                                 sl_s
                    ) ⊜ F (pair ⊜ sl_F (fst ⊝ rms)) in
        annF (G ∪ Sp ∪ ((getAnn lv_t ∪ G) \ L)) lv_F lv_t

    | _,_ => ann0 G
    end
.


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

Lemma reg_live_G_eq
      (G : ⦃var⦄)
      (Lv : list ⦃var⦄)
      (ZL : list params)
      (s : stmt)
      (sl : spilling)
  :
    getAnn (reg_live ZL Lv G s sl)
           [=]
           getAnn (reg_live ZL Lv ∅ s sl) ∪ G
.
Proof.
  general induction s;
    destruct sl;
    try destruct a;
    try destruct p;
    simpl; eauto; try cset_tac.
  induction l0; simpl; eauto.
  - cset_tac.
  - destruct a. destruct l0; simpl; cset_tac.
Qed.


Lemma reg_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (G : set var)
      (s : stmt)
      (sl : spilling)
  :
    G ⊆ getAnn (reg_live ZL Lv G s sl)
.
Proof.
  induction s,sl; destruct a,p;
    simpl; eauto with cset.
  - simpl. induction l0; simpl; eauto with cset.
    destruct a,l0; simpl; cset_tac.
Qed.

(*
Definition rlive_min
  := ann_P (fun (Rlv: ⦃var⦄)
            => forall k ZL Λ RM  s sl,
                spill_sound k ZL Λ RM s sl
                -> Rlv ⊆ fst RM)
.
*)

(*Definition rlive_min k ZL Λ RM  s sl rlv
  :=
    spill_sound k ZL Λ RM s sl
    -> getAnn rlv ⊆ fst RM
.*)


Lemma reg_live_R k ZL Λ RM  s sl rLv :
    spill_sound k ZL Λ RM s sl
    -> PIR2 Subset rLv (fst ⊝ Λ)
    -> getAnn (reg_live ZL rLv (∅:⦃var⦄) s sl) ⊆ fst RM
.
Proof.
  intros spillSnd pir2. general induction spillSnd; simpl.
  - rewrite reg_live_G_eq. rewrite IHspillSnd; simpl; eauto.
    rewrite H1, H. clear; cset_tac.
  - rewrite H1, H. clear; cset_tac.
  - rewrite H, H1, IHspillSnd1, IHspillSnd2; simpl; eauto. clear; cset_tac.
  - eapply PIR2_nth_2 in pir2 as [Rl [get_Rl Rl_sub]].
    + erewrite !get_nth; eauto. simpl. rewrite Rl_sub, H, H4, H6. clear; cset_tac.
    + eapply map_get_eq; eauto.
  - rewrite reg_live_G_eq. rewrite H, IHspillSnd; eauto.
    + simpl; clear; cset_tac.
    + rewrite List.map_app. apply PIR2_app; eauto.
Qed.


Lemma reg_live_rlive_min k G ZL Λ RM s sl rLv :
  let rlv := reg_live ZL rLv G s sl in
  spill_sound k ZL Λ RM s sl
  -> PIR2 Subset rLv (fst ⊝ Λ)
  -> annotation s rlv
  -> rlive_min k ZL Λ G s sl rlv
.
Proof.
  intros rlv spillSnd pir2 anno. subst rlv. general induction spillSnd; invc anno; cbn.
  - econstructor; eauto.
    unfold is_rlive_min in *. intros. rewrite reg_live_G_eq. clear spillSnd.
    invc H5. rewrite reg_live_R; eauto. cbn. clear - H17 H20; cset_tac.
  - econstructor; eauto.
    unfold is_rlive_min. intros. invc H3. clear - H13 H11. cset_tac.
  - econstructor; eauto. clear spillSnd1 spillSnd2. unfold is_rlive_min. intros.
    invc H3. rewrite !reg_live_R; eauto. cbn. clear - H19 H16. cset_tac.
  - eapply PIR2_nth_2 with (blk:=R_f) in pir2 as [Rl [get_Rl Rl_sub]]; [|eapply map_get_eq;eauto].
    erewrite !get_nth; eauto.
    econstructor; eauto. unfold is_rlive_min.
    intros. rewrite Rl_sub. invc H8. eapply get_get_eq with (x:=Z) in H22;eauto. subst Z0.
    eapply get_get_eq with (x':=(R_f,M_f)) in H23; eauto. invc H23.
    rewrite H17, H24, H26. clear; cset_tac.
  - econstructor; eauto.
    + intros. inv_get.
      eapply rlive_min_G_anti.
      eapply H6; eauto.
      * rewrite List.map_app. eapply PIR2_app; eauto.
      * eapply H13; eauto.
        eapply zip_get_eq; eauto using zip_get.
      * reflexivity.
    + eapply IHspillSnd; eauto.
      rewrite List.map_app. eapply PIR2_app; eauto.
    + unfold is_rlive_min. intros. clear H6 IHspillSnd spillSnd H13 H11 H5. invc H7.
      rewrite reg_live_R; eauto; cbn; [clear - H18; cset_tac|].
      rewrite List.map_app. eapply PIR2_app; eauto.
Qed.


(*
Proof.
  intros spillSnd pir2. general induction spillSnd; simpl.
  - rewrite IHspillSnd; simpl; eauto.
    rewrite H1, H. clear; cset_tac.
  - rewrite H1, H. clear; cset_tac.
  - rewrite H, H1, IHspillSnd1, IHspillSnd2; simpl; eauto. clear; cset_tac.
  - eapply PIR2_nth_2 in pir2 as [Rl [get_Rl Rl_sub]].
    + erewrite !get_nth; eauto. simpl. rewrite Rl_sub, H, H4, H6. clear; cset_tac.
    + eapply map_get_eq; eauto.
  - rewrite H, IHspillSnd; eauto.
    + simpl; clear; cset_tac.
    + rewrite List.map_app. apply PIR2_app; eauto.
Qed.
*)



Lemma rlive_sound_monotone
  : forall (ZL : 〔params〕) (LV LV' : 〔⦃nat⦄〕) (s : stmt) (sl : spilling) (rlv : ann ⦃nat⦄),
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




Lemma reg_live_sound k ZL Λ rlv (R M : ⦃var⦄) G s sl
  : spill_sound k ZL Λ (R,M) s sl
    -> PIR2 Subset rlv (fst ⊝ Λ)
    -> rlive_sound ZL rlv s sl (reg_live ZL rlv G s sl)
.
Proof.
  intros spillSnd pir2.
  general induction spillSnd.
  - econstructor.
    + apply union_incl_left; clear;cset_tac.
    + eapply IHspillSnd; eauto.
    + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
      * apply live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear;cset_tac.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + apply reg_live_G. clear; cset_tac.
  - econstructor.
    + clear; cset_tac.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * clear; cset_tac.
  - econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
     + eapply IHspillSnd1; eauto.
    + eapply IHspillSnd2; eauto.
    + apply live_op_sound_incl with (lv':=Op.freeVars e).
      * apply Op.live_freeVars.
      * setoid_rewrite <-incl_right at 4. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
    + setoid_rewrite <-incl_right at 2. clear; cset_tac.
  - assert (pir2' := pir2). eapply PIR2_flip in pir2'. eapply PIR2_nth in pir2'.
    destruct pir2', H8.
    econstructor; eauto.
    + clear; cset_tac.
    + simpl. erewrite !get_nth; eauto. clear; cset_tac.
    + intros. inv_get.
      apply live_op_sound_incl with (lv':=Op.freeVars y).
      * apply Op.live_freeVars.
      * erewrite !get_nth; eauto.
        erewrite <-incl_list_union with (s:=Op.freeVars y); eauto; clear; cset_tac.
    + eauto.
  - simpl.
    econstructor.
    + setoid_rewrite <-incl_right at 3. clear; cset_tac.
    + set (fix1 := fun (ps : params * stmt) (rmsl : spilling * ⦃var⦄) => _ ).
      eapply rlive_sound_monotone with (LV := fst ⊝ rms ++ rlv).
      eapply IHspillSnd; eauto.
     * rewrite List.map_app. apply PIR2_app; [apply PIR2_refl|]; eauto.
     * apply PIR2_app; [|apply PIR2_refl;eauto].
       apply PIR2_get. intros; inv_get.
       -- subst fix1. simpl. rewrite reg_live_G_eq. rewrite reg_live_R.
          ++ instantiate (1:=x0). clear; cset_tac.
          ++ eauto.
          ++ rewrite List.map_app. apply PIR2_app; eauto.
       -- eauto with len.
    + eauto with len.
    + intros; inv_get. eapply rlive_sound_monotone. eapply H6; eauto.
      * apply pair_eta.
      * rewrite List.map_app. apply PIR2_app; eauto.
      * apply PIR2_app; [|apply PIR2_refl;eauto].
        apply PIR2_get. intros; inv_get.
        -- rewrite reg_live_G_eq, reg_live_R; eauto.
           ++ clear; cset_tac.
           ++ rewrite List.map_app. apply PIR2_app; [apply PIR2_refl|]; eauto.
        -- eauto with len.
    + intros; inv_get. rewrite <-reg_live_G. clear; cset_tac.
    + clear; cset_tac.
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
