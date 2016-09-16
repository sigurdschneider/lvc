Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill DoSpillRm DiscardMergeSl SpillUtil.

Set Implicit Arguments.




Fixpoint spill_live
(Lv : list (set var))
(ZL : list (params))
(G : set var)
(s : stmt)
(rm : ann (option (list (set var))))
{struct s}
: ann (set var)
:=
match s, rm with
| stmtLet x e t, ann1 _ rm  (* checked *)
     => let lv_t := spill_live Lv ZL (singleton x) t rm in
        ann1 ((getAnn lv_t) \ singleton x ∪ Exp.freeVars e ∪ G) lv_t

| stmtReturn e, ann0 _ (* checked *)
     => ann0 (Op.freeVars e ∪ G)

| stmtIf e t v, ann2 _ rm_t rm_v (* checked *)
     => let lv_t := spill_live Lv ZL ∅ t rm_t in
        let lv_v := spill_live Lv ZL ∅ v rm_v in
        ann2 (getAnn lv_t ∪ getAnn lv_v ∪ Op.freeVars e ∪ G) lv_t lv_v

| stmtApp f Y, ann0 _ (* checked *)
     => let blv := nth (counted f) Lv ∅ in
        let Z   := nth (counted f) ZL nil in
        ann0 (list_union (Op.freeVars ⊝ Y) ∪ blv \ of_list Z ∪ G)

| stmtFun F t, annF (Some rms) rm_F rm_t (* checked *)
     => let lv_t := spill_live (rms ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s => spill_live (rms ++ Lv)
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



Lemma spill_live_subset Lv Lv' ZL G s sl
  :
    PIR2 Subset Lv Lv'
    -> ann_R Subset
            (spill_live Lv  ZL G s sl)
            (spill_live Lv' ZL G s sl).
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
  - destruct (get_dec Lv l) as [[? ?]|].
    + PIR2_inv.
      rewrite (get_nth _ g); eauto.
      rewrite (get_nth _ H1); eauto.
      rewrite H0. reflexivity.
    + PIR2_inv.
      rewrite not_get_nth_default; eauto.
      rewrite (not_get_nth_default _ H0); eauto.
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

Lemma spill_live_equal Lv Lv' ZL G s sl
  : PIR2 Equal Lv Lv'
    -> ann_R Equal
            (spill_live Lv  ZL G s sl)
            (spill_live Lv' ZL G s sl).
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
  - destruct (get_dec Lv l) as [[? ?]|].
    + PIR2_inv.
      rewrite (get_nth _ g); eauto.
      rewrite (get_nth _ H1); eauto.
      rewrite H0. reflexivity.
    + PIR2_inv.
      rewrite not_get_nth_default; eauto.
      rewrite (not_get_nth_default _ H0); eauto.
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


Lemma spill_live_G
      (Lv : list (set var))
      (ZL : list (params))
      (x : var)
      (s : stmt)
      (a : ann (option (list (set var))))
  :
    x ∈ getAnn (spill_live Lv ZL (singleton x) s a).
Proof.
  induction s,a ; simpl; eauto with cset.
  - destruct a; simpl; eauto.
    cset_tac.
Qed.


Lemma spill_live_G_set
      (Lv : list (set var))
      (ZL : list (params))
      (G : set var)
      (s : stmt)
      (a : ann (option (list (set var))))
  :
    G ⊆ getAnn (spill_live Lv ZL G s a)
.
Proof.
  induction s,a; simpl; eauto with cset.
  - destruct a; simpl; eauto.
Qed.




Inductive some_spill_live
  :
    ann (set var * set var * option (list (set var * set var))) -> ann (set var) -> Prop
  :=
  | SomeSpLv0 a b
    : some_spill_live (ann0 a) (ann0 b)
  | SomeSpLv1 a b sl lv
    : some_spill_live sl lv
      -> some_spill_live (ann1 a sl) (ann1 b lv)
  | SomeSpLv2 a b sl1 sl2 lv1 lv2
    : some_spill_live sl1 lv1
      -> some_spill_live sl2 lv2
      -> some_spill_live (ann2 a sl1 sl2) (ann2 b lv1 lv2)
  | SomeSpLvF a b sl_F sl_t lv_F lv_t rms
    : merge rms = getAnn ⊝ lv_F
      -> some_spill_live sl_t lv_t
      -> (forall n sl_s lv_s,
            get sl_F n sl_s
            -> get lv_F n lv_s
            -> some_spill_live sl_s lv_s
        )
      -> some_spill_live (annF (a,⎣ rms ⎦) sl_F sl_t)
                              (annF b lv_F lv_t)
.


(* TODO: I need some assumptions on slot
   this doesn't hold in general *)
Lemma map_slot_minus
      (slot : var -> var)
      (s t : ⦃var⦄)
  :
    map slot (s \ t) [=] map slot s \ map slot t
.
Admitted.


Lemma map_slot_cut
      (slot : var -> var)
      (s t : ⦃var⦄)
  :
    map slot (s ∩ t) [=] map slot s ∩ map slot t
.
Admitted.


Lemma map_slot_incl
      (slot : var -> var)
      (s t : ⦃var⦄)
  :
    s ⊆ t <-> map slot s ⊆ map slot t
.
Admitted.




Lemma fst_F
      F sl_F slot rms
  :
    length F = length sl_F
    -> length F = length rms
    -> fst
        ⊝ (fun (Zs : params * stmt)
             (sls_rm : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕) * (⦃var⦄ * ⦃var⦄)) =>
             let (sl_s, rm) := sls_rm in
             (slot_lift_params slot (fst Zs) rm, do_spill slot (snd Zs) sl_s)) ⊜ F
        ((fun (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) (rm : ⦃var⦄ * ⦃var⦄) => (sl_s, rm))
           ⊜ sl_F rms)
        = (slot_lift_params slot ⊜ (fst ⊝ F) rms)
.
Proof.
  intros len.

  general induction F;
    simpl in *; eauto.
  destruct sl_F,rms; simpl in *; eauto.
  + isabsurd.
  + f_equal. apply IHF; eauto.
Qed.
