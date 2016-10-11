Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling SpillUtil.

Set Implicit Arguments.



Fixpoint reconstr_live
         (Lv : list (set var))
         (ZL : list (params))
         (G : set var)
         (s : stmt)
         (rm : ann (option (list (set var))))
         {struct s}
  : ann (set var)
  :=
    match s, rm with
    | stmtLet x e t, ann1 _ rm
      => let lv_t := reconstr_live Lv ZL (singleton x) t rm in
        ann1 ((getAnn lv_t) \ singleton x ∪ Exp.freeVars e ∪ G) lv_t

    | stmtReturn e, ann0 _
      => ann0 (Op.freeVars e ∪ G)

    | stmtIf e t v, ann2 _ rm_t rm_v
      => let lv_t := reconstr_live Lv ZL ∅ t rm_t in
        let lv_v := reconstr_live Lv ZL ∅ v rm_v in
        ann2 (getAnn lv_t ∪ getAnn lv_v ∪ Op.freeVars e ∪ G) lv_t lv_v

    | stmtApp f Y, ann0 _
      => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (list_union (Op.freeVars ⊝ Y) ∪ blv \ of_list Z ∪ G)

    | stmtFun F t, annF (Some rms) rm_F rm_t
      => let lv_t := reconstr_live (rms ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s => reconstr_live (rms ++ Lv)
                                               (fst ⊝ F ++ ZL)
                                               (of_list (fst ps))
                                               (snd ps)
                                               rm_s
                    ) ⊜ F rm_F in
        annF (getAnn lv_t ∪ G) lv_F lv_t

    | _,_ => ann0 G

    end.






Lemma live_sound_ann_ext ZL Lv s lv lv'
  :
    ann_R Equal lv lv'
    -> live_sound Imperative ZL Lv s lv
    -> live_sound Imperative ZL Lv s lv'
.
Proof.
  intros annR lvSnd.
  general induction lvSnd; inversion_clear annR.
  - econstructor; eauto; apply ann_R_get in H3.
    + apply live_exp_sound_incl with (lv':=lv); eauto.
      rewrite H2. reflexivity.
    + rewrite <- H3. rewrite <- H2. eauto.
    + rewrite <- H3. eauto.
  - econstructor; eauto;
      apply ann_R_get in H3;
      apply ann_R_get in H4;
      try rewrite <- H2;
      try rewrite <- H3;
      try rewrite <- H4;
      eauto.
  - econstructor; simpl; intros; eauto;
      try rewrite <- H4; eauto.
  - econstructor; simpl; intros; eauto;
      try rewrite <- H0; eauto.
  - apply ann_R_get in H7 as H7'.
    assert (PIR2 Subset (getAnn ⊝ bns ++ Lv) (getAnn ⊝ als ++ Lv))
      as pir2_als_bns.
    { apply PIR2_app.
      - apply PIR2_get; eauto with len.
        intros; inv_get.
        exploit H6 as EQ; eauto.
        eapply ann_R_get in EQ. rewrite EQ. reflexivity.
      - apply PIR2_refl; eauto.
    }
    econstructor; simpl; eauto;
      try rewrite <- H0; eauto.
    + apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + rewrite <- H5. eauto.
    + intros. inv_get.
      apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + intros. simpl in H2. inv_get.
      exploit H6 as EQ; eauto.
      apply ann_R_get in EQ.
      rewrite <- EQ.
      apply H2 with (n:=n); eauto.
    + rewrite <- H4. rewrite <- H7'. eauto.
Qed.



Lemma reconstr_live_subset Lv Lv' ZL G s sl
  :
    PIR2 Subset Lv Lv'
    -> ann_R Subset
            (reconstr_live Lv  ZL G s sl)
            (reconstr_live Lv' ZL G s sl).
Proof.
  intros H.
  revert Lv Lv' H ZL G sl.
  sind s; intros; destruct s, sl; simpl; try econstructor; eauto;
    try eapply IH; eauto.
  - exploit (IH s); eauto.
    rewrite (ann_R_get H0); eauto.
  - exploit (IH s1); eauto.
    exploit (IH s2); eauto.
    rewrite (ann_R_get H0); eauto.
    rewrite (ann_R_get H1); eauto.
  - enough (nth (labN l) Lv ∅ ⊆ nth (labN l) Lv' ∅)
      as HH by (rewrite HH; clear; cset_tac).
    apply PIR2_length in H as Lv_len.
    decide (labN l < length Lv).
    + assert ({x : ⦃var⦄ & get Lv (labN l) x}) as [x get_x]
          by (apply get_in_range; eauto).
      rewrite Lv_len in l0.
      assert ({y : ⦃var⦄ & get Lv' (labN l) y}) as [y get_y]
          by (apply get_in_range; eauto).
      erewrite get_nth; eauto.
      erewrite get_nth; eauto.
      eapply get_PIR2; eauto.
    + apply not_le in n.
      rewrite nth_overflow; eauto with cset.
      omega.
  - destruct a; simpl; econstructor.
    exploit (IH s). eauto. Focus 2.
    rewrite (ann_R_get H0); eauto. reflexivity.
    eapply PIR2_app; eauto with len.
    repeat rewrite zip_length; eauto.
    intros; inv_get.
    eapply IH; eauto.
    eapply PIR2_app; eauto with len.
    eapply IH; eauto.
    eapply PIR2_app; eauto with len.
    reflexivity.
Qed.

Lemma reconstr_live_equal Lv Lv' ZL G s sl
  : PIR2 Equal Lv Lv'
    -> ann_R Equal
            (reconstr_live Lv  ZL G s sl)
            (reconstr_live Lv' ZL G s sl).
Proof.
  intros H.
  revert Lv Lv' H ZL G sl.
  sind s; intros; destruct s, sl; simpl; try econstructor; eauto;
    try eapply IH; eauto.
  - exploit (IH s); eauto.
    rewrite (ann_R_get H0); eauto.
  - exploit (IH s1); eauto.
    exploit (IH s2); eauto.
    rewrite (ann_R_get H0); eauto.
    rewrite (ann_R_get H1); eauto.
  - enough (nth (labN l) Lv ∅ [=] nth (labN l) Lv' ∅)
      as HH by (rewrite HH; clear; cset_tac).
    apply PIR2_length in H as Lv_len.
    decide (labN l < length Lv).
    + assert ({x : ⦃var⦄ & get Lv (labN l) x}) as [x get_x]
          by (apply get_in_range; eauto).
      rewrite Lv_len in l0.
      assert ({y : ⦃var⦄ & get Lv' (labN l) y}) as [y get_y]
          by (apply get_in_range; eauto).
      erewrite get_nth; eauto.
      erewrite get_nth; eauto.
      eapply get_PIR2; eauto.
    + apply not_le in n.
      rewrite nth_overflow; eauto with cset;
        [ | omega].
      rewrite Lv_len in n.
      rewrite nth_overflow; eauto with cset.
      omega.
  - destruct a; simpl; econstructor.
    exploit (IH s). eauto. Focus 2.
    rewrite (ann_R_get H0); eauto. reflexivity.
    eapply PIR2_app; eauto with len.
    repeat rewrite zip_length; eauto.
    intros; inv_get.
    eapply IH; eauto.
    eapply PIR2_app; eauto with len.
    eapply IH; eauto.
    eapply PIR2_app; eauto with len.
    reflexivity.
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
    : merge rms = getAnn ⊝ lv_F
      -> spill_live VD sl_t lv_t
      -> (forall n rm,
            get rms n rm
            -> fst rm ⊆ VD /\ snd rm ⊆ VD)
      -> (forall n sl_s lv_s,
            get sl_F n sl_s
            -> get lv_F n lv_s
            -> spill_live VD sl_s lv_s
        )
      -> spill_live VD (annF (a,⎣ inl rms ⎦) sl_F sl_t)
                              (annF b lv_F lv_t)
.


Lemma injective_map_minus
      (X Y : Type)
      `{OrderedType X}
      `{OrderedType Y}
      (f : X -> Y)
      (s t D : ⦃X⦄)
  :
    Proper (_eq ==> _eq) f
    -> s ⊆ D
    -> t ⊆ D
    -> injective_on D f
    -> map f (s \ t) [=] map f s \ map f t
.
Proof.
  intros H1 sD tD inj.
  apply lookup_set_minus_eq; eauto.
  apply injective_on_incl with (D:=D); eauto.
  cset_tac.
Qed.
