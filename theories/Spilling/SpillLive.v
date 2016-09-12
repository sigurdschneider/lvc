Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SimI Spilling DoSpill DoSpillRm DiscardMergeSl SpillUtil.

Set Implicit Arguments.



(*
Lemma spill_fun_is_live
      (k : nat)
      (slot : var -> var)
      (ZL : list (params))
      (Λ rms : list (set var * set var))
      (R M Sp L : set var)
      (s t : stmt)
      (sl_F : list (ann (set var * set var * option (list (set var * set var)))))
      (sl_t : ann (set var * set var * option (list (set var * set var))))
      (F : list (params * stmt))
       lv_t lv_F lv
  :
    spill_sound k ZL Λ (R,M) (stmtFun F t)
                (annF (Sp,L,Some rms) sl_F sl_t)
    -> live_sound Imperative ZL (slot_merge slot Λ)
                                (stmtFun F t)
                                (annF lv lv_F lv_t)
    -> getAnn ⊝ lv_F = (fun rm => fst rm ∪ map slot (snd rm)) ⊝ rms

.
Proof.
  intros spillSound lvSound.
  induction lvSound; inversion_clear spillSound.
Admitted.
*)

Fixpoint list_union'
         (X : Type) `{OrderedType X}
         (L : list (set X))
  : set X
  :=
    match L with
    | nil => ∅
    | s::xl => s ∪ list_union' xl
    end
.


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
     => let Lv'  := (fun rm ps => rm ∪ of_list (fst ps)) ⊜ rms F in
        let lv_t := spill_live (Lv' ++ Lv) (fst ⊝ F ++ ZL) ∅ t rm_t in
        let lv_F := (fun ps rm_s => spill_live (Lv' ++ Lv)
                                             (fst ⊝ F ++ ZL)
                                             (of_list (fst ps))
                                             (snd ps)
                                              rm_s
                    ) ⊜ F rm_F in
        annF (getAnn lv_t ∪ G) lv_F lv_t

| _,_ => ann0 G

end.


Lemma simpl_als
      F
      als
  :
    length F = length als
    -> (forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs -> get als n a -> of_list (fst Zs) ⊆ getAnn a /\ True)
    ->                (fun (rm : ⦃var⦄) (ps : params * stmt)
                      => rm ∪ of_list (fst ps)) ⊜ (getAnn ⊝ als) F
                                               === getAnn ⊝ als
.
Proof.
  intros H H2.
  revert dependent F; induction als;
    intros F H H2; simpl; eauto.
  destruct F ; simpl; eauto.
  + isabsurd.
  + econstructor.
    * assert (get (p::F) 0 p) as get_p.
      { econstructor. }
      assert (get (a::als) 0 a) as get_a.
      { econstructor. }
      specialize (H2 0 p a get_p get_a).
      destruct H2.
      change (Equal_pw ⦃var⦄ var In (getAnn a ∪ of_list (fst p)) (getAnn a))
      with (getAnn a ∪ of_list (fst p) === getAnn a).
      apply set_incl.
      -- cset_tac.
      -- cset_tac.
    * apply IHals; eauto.
      intros.
      apply H2 with (n:= S(n)); econstructor; eauto.
Qed.




Lemma live_sound_monotone3 ZL Lv s lv lv'
  :
    ann_R (Equal_pw ⦃var⦄ var In) lv lv'
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
      - apply PIR2_get.
        Focus 2. do 2 rewrite map_length. eauto.
        intros n x x' get_x get_x'.
        apply map_get_4 in get_x.
        destruct get_x as [y [get_y xeq]].
        apply map_get_4 in get_x'.
        destruct get_x' as [y' [get_y' yeq]].
        apply H6 with (b:=y) in get_y' as H6'; eauto.
        apply ann_R_get in H6'.
        subst.
        rewrite H6'.
        reflexivity.
      - apply PIR2_refl.
        unfold Reflexive.
        apply subset_refl.
    }
    econstructor; simpl; eauto;
      try rewrite <- H0; eauto.
    + apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + rewrite <- H5. eauto.
    + intros.
      assert (exists a', get als n a') as [a' get_a'].
      { apply get_length_eq with (L:=bns) (x:=a); eauto. }
      apply live_sound_monotone with (LV:=getAnn ⊝ als ++ Lv); eauto.
    + intros. simpl in H2.
      assert (exists a', get als n a') as [a' get_a'].
      { apply get_length_eq with (L:=bns) (x:=a); eauto. }
      apply H6 with (b:=a) in get_a' as H6'; eauto.
      apply ann_R_get in H6'.
      rewrite <- H6'.
      apply H2 with (n:=n); eauto.
    + rewrite <- H4. rewrite <- H7'. eauto.
Qed.



Lemma get_get_eq
      (X : Type)
      (L : list X)
      (n : nat)
      (x x' : X)
  :
    get L n x -> get L n x' -> x = x'
.
Proof.
  intros get_x get_x'.
  induction get_x; inversion get_x'.
  - reflexivity.
  - apply IHget_x. assumption.
Qed.

Lemma spill_live_setequal Lv Lv' ZL G s sl
  :
    PIR2 (Equal_pw ⦃var⦄ var In) Lv Lv'
    -> ann_R (Equal_pw ⦃var⦄ var In)
             (spill_live Lv  ZL G s sl)
             (spill_live Lv' ZL G s sl)
.
Proof.
  intros pir2.
  apply PIR2_length in pir2 as pir2_len; eauto.
  general induction s;
    general induction sl;
    unfold spill_live; simpl; eauto.
  - econstructor; eauto.
    specialize (IHs Lv Lv' ZL (singleton x) sl pir2).
    apply ann_R_get in IHs; eauto.
    rewrite IHs.
    reflexivity.
  - econstructor; eauto.
    specialize (IHs1 Lv Lv' ZL ∅ sl1 pir2).
    apply ann_R_get in IHs1; eauto.
    rewrite IHs1.
    specialize (IHs2 Lv Lv' ZL ∅ sl2 pir2).
    apply ann_R_get in IHs2; eauto.
    rewrite IHs2.
    reflexivity.
  - econstructor; simpl; eauto.
    enough (nth l Lv ∅ [=] nth l Lv' ∅) as nth_eq.
    + rewrite nth_eq.
      reflexivity.
    + decide (l >= length Lv).
      * rewrite nth_overflow; eauto.
        rewrite nth_overflow; eauto.
        rewrite <- pir2_len. eauto.
      * apply not_ge in n.
        apply get_in_range in n as range.
        rewrite pir2_len in n.
        apply get_in_range in n as range'.
        destruct range as [x get_x].
        destruct range' as [x' get_x'].
        apply PIR2_nth with (l:=l) (blk:=x)
          in pir2 as [blk [get_blk blk_eq]]; eauto.
        apply get_get_eq with (x':=x') in get_blk; eauto.
        subst.
        rewrite get_nth with (m:=x); eauto.
        rewrite blk_eq.
        symmetry.
        rewrite get_nth with (m:=x'); eauto.
  - destruct a; econstructor; eauto.
    + specialize (IHs ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv)
                      ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv')
                      (fst ⊝ F ++ ZL) ∅ sl).
      apply ann_R_get in IHs; eauto.
      * rewrite IHs.
        reflexivity.
      * apply PIR2_app; eauto.
      * do 2 rewrite app_length.
        rewrite pir2_len.
        reflexivity.
    + do 2 rewrite zip_length.
      reflexivity.
    + intros.
      apply get_zip in H.
      destruct H as [x [y [get_x [get_y eq_a]]]].
      apply get_zip in H0.
      destruct H0 as [x' [y' [get_x' [get_y' eq_b]]]].
      apply get_get_eq with (L:=F) (n:=n) (x':=x) in get_x'; eauto.
      apply get_get_eq with (L:=sa)(n:=n) (x':=y) in get_y'; eauto.
      admit.
    + specialize (IHs ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv)
                      ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv')
                      (fst ⊝ F ++ ZL) ∅ sl).
      apply IHs.
      * apply PIR2_app; eauto.
      * do 2 rewrite app_length.
        rewrite pir2_len.
        reflexivity.
    + reflexivity.
Admitted.

Lemma spill_live_subset Lv Lv' ZL G s sl
  :
    PIR2 Subset Lv Lv'
    -> ann_R  Subset
             (spill_live Lv  ZL G s sl)
             (spill_live Lv' ZL G s sl)
.
    intros pir2.
  apply PIR2_length in pir2 as pir2_len; eauto.
  general induction s;
    general induction sl;
    unfold spill_live; simpl; eauto.
  - econstructor; eauto.
    specialize (IHs Lv Lv' ZL (singleton x) sl pir2).
    apply ann_R_get in IHs; eauto.
    rewrite IHs.
    reflexivity.
  - econstructor; eauto.
    specialize (IHs1 Lv Lv' ZL ∅ sl1 pir2).
    apply ann_R_get in IHs1; eauto.
    rewrite IHs1.
    specialize (IHs2 Lv Lv' ZL ∅ sl2 pir2).
    apply ann_R_get in IHs2; eauto.
    rewrite IHs2.
    reflexivity.
  - econstructor; simpl; eauto.
    enough (nth l Lv ∅ ⊆ nth l Lv' ∅) as nth_eq.
    + rewrite nth_eq.
      reflexivity.
    + decide (l >= length Lv).
      * rewrite nth_overflow; eauto.
        rewrite nth_overflow; eauto.
        rewrite <- pir2_len. eauto.
      * apply not_ge in n.
        apply get_in_range in n as range.
        rewrite pir2_len in n.
        apply get_in_range in n as range'.
        destruct range as [x get_x].
        destruct range' as [x' get_x'].
        apply PIR2_nth with (l:=l) (blk:=x)
          in pir2 as [blk [get_blk blk_eq]]; eauto.
        apply get_get_eq with (x':=x') in get_blk; eauto.
        subst.
        rewrite get_nth with (m:=x); eauto.
        rewrite blk_eq.
        rewrite get_nth with (m:=x'); eauto.
  - destruct a; econstructor; eauto.
    + specialize (IHs ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv)
                      ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv')
                      (fst ⊝ F ++ ZL) ∅ sl).
      apply ann_R_get in IHs; eauto.
      * rewrite IHs.
        reflexivity.
      * apply PIR2_app; eauto.
      * do 2 rewrite app_length.
        rewrite pir2_len.
        reflexivity.
    + do 2 rewrite zip_length.
      reflexivity.
    + intros.
      apply get_zip in H.
      destruct H as [x [y [get_x [get_y eq_a]]]].
      apply get_zip in H0.
      destruct H0 as [x' [y' [get_x' [get_y' eq_b]]]].
      apply get_get_eq with (L:=F) (n:=n) (x':=x) in get_x'; eauto.
      apply get_get_eq with (L:=sa)(n:=n) (x':=y) in get_y'; eauto.
      admit.
    + specialize (IHs ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv)
                      ((fun (rm : ⦃var⦄) (ps : params * stmt)
                        => rm ∪ of_list (fst ps)) ⊜ l F ++ Lv')
                      (fst ⊝ F ++ ZL) ∅ sl).
      apply IHs.
      * apply PIR2_app; eauto.
      * do 2 rewrite app_length.
        rewrite pir2_len.
        reflexivity.
Admitted.


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


Lemma spill_live_sound_s
      (slot : var -> var)
      (n : nat)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (Lv : list (set var))
      (s : stmt)
      (sl sl': ann (set var * set var * option (list (set var * set var))))
  :
    sub_spill sl' sl
    -> n = count sl'
    -> let sl0 := setTopAnn sl (∅,∅,snd (getAnn sl)) in
   (forall G', live_sound Imperative ZL Lv
              (do_spill slot s sl0)
              (spill_live (slot_merge slot Λ) ZL G'
                          (do_spill slot s sl0)
                          (discard_merge_sl slot (do_spill_rm' slot 0 sl))))
-> live_sound Imperative ZL Lv
              (do_spill slot s sl')
              (spill_live (slot_merge slot Λ) ZL G
                          (do_spill slot s sl')
                          (discard_merge_sl slot (do_spill_rm' slot n sl))).
Proof.

set (Sp' := fst (fst (getAnn sl'))).
set (L'  := snd (fst (getAnn sl'))).
set (rm' := snd (getAnn sl')).
intros sub_sl n_count sl0 strong_sls.

remember (cardinal Sp') as n_Sp'.
symmetry in Heqn_Sp'.
rename Heqn_Sp' into card_Sp'.
revert dependent sl'.
revert G.
revert n.
induction n_Sp';
  intros n G sl' Sp' L' rm' sub_sl n_count card_Sp'.

- remember (cardinal L') as n_L'.
  symmetry in Heqn_L'.
  rename Heqn_L' into card_L'.
  revert dependent sl'.
  revert G.
  revert n.
  induction n_L';
    intros n G sl' Sp' L' rm' sub_sl n_count card_Sp' card_L'.

  {
    assert (count sl' = 0) as count_sl'.
    { unfold count. subst Sp'. subst L'.
      rewrite card_Sp'. rewrite card_L'. omega. }
    rewrite do_spill_empty_invariant
    with (Sp':=∅) (L':=∅) (rm:=rm') (sl':=sl0);
      simpl; eauto; try apply empty_1;
      try apply cardinal_Empty; eauto.

    + rewrite n_count.
      rewrite count_sl'.
      rewrite do_spill_rm_zero.
      destruct sl; destruct a; destruct p; apply strong_sls.
    + subst sl0.
      unfold sub_spill in sub_sl.
      destruct  sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite <- eq_rm.
      rewrite top_sl'.
      rewrite setTopAnn_setTopAnn.
      rewrite getAnn_setTopAnn.
      subst rm'.
      reflexivity.
  }


  rewrite do_spill_L.
  Focus 2. rewrite cardinal_Empty. subst Sp'. assumption.
  Focus 2. clear - card_L'. intro N.
           apply cardinal_Empty in N. subst L'. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  subst L'.
  rewrite card_L'.
  rewrite card_Sp'.
  simpl.

  rewrite do_spill_rm_s.

  rewrite discard_merge_sl_step.

  constructor; fold spill_live.

  * apply IHn_L'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.

    -- rewrite count_reduce_L with (n:=n_L') (m:=n_L'); eauto.
       unfold count. rewrite card_Sp'. rewrite card_L'. eauto.
    -- rewrite getAnn_setTopAnn.
       simpl.
       assumption.
    -- rewrite getAnn_setTopAnn.
       simpl. erewrite cardinal_set_tl. eauto.
       rewrite of_list_elements. rewrite card_L'. eauto.
    * apply live_exp_sound_incl
        with (lv':=Exp.freeVars (Operation (Var (slot
                         (hd 0 (elements (snd (fst (getAnn sl'))))))))).
      -- apply live_freeVars.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.

- rewrite do_spill_Sp.
  Focus 2. subst Sp'. clear - card_Sp'. intro N.
           apply cardinal_Empty in N. omega.

  rewrite n_count.
  unfold count.
  subst Sp'.
  rewrite card_Sp'.
  simpl.


  rewrite do_spill_rm_s with (n:=n_Sp' + cardinal L').

  econstructor; fold spill_live.
  * apply IHn_Sp'.
    -- unfold sub_spill.
       unfold sub_spill in sub_sl.
       destruct sub_sl as [top_sl' [sub_Sp [sub_L eq_rm]]].
       repeat split; rewrite getAnn_setTopAnn; simpl; eauto.
       ++ rewrite top_sl'. rewrite setTopAnn_setTopAnn.
          rewrite getAnn_setTopAnn. reflexivity.
       ++ rewrite tl_set_incl. assumption.
    -- rewrite count_reduce_Sp with (n:=n_Sp' + cardinal L') (m:=n_Sp'); eauto.
       unfold count. rewrite card_Sp'. subst L'. omega.
    -- rewrite getAnn_setTopAnn.
       simpl.
       erewrite cardinal_set_tl; eauto.
       rewrite of_list_elements.
       rewrite card_Sp'.
       omega.
     * apply live_exp_sound_incl
        with (lv':= singleton (hd 0 (elements (fst (fst (getAnn sl')))))).
      -- econstructor. econstructor. eauto with cset.
      -- clear. cset_tac.
    * clear. cset_tac.
    * apply spill_live_G.
Qed.


Lemma sub_spill_refl sl
  :
    sub_spill sl sl
.
Proof.
  unfold sub_spill.
  repeat split.
    simpl; eauto.
  - unfold setTopAnn.
    destruct sl; destruct a; destruct p;
      simpl; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.



Inductive some_spill_live
          (slot : var -> var)
  :
    ann (set var * set var * option (list (set var * set var))) -> ann (set var) -> Prop
  :=
  | SomeSpLv0 a b
    : some_spill_live slot (ann0 a) (ann0 b)
  | SomeSpLv1 a b sl lv
    : some_spill_live slot sl lv
      -> some_spill_live slot (ann1 a sl) (ann1 b lv)
  | SomeSpLv2 a b sl1 sl2 lv1 lv2
    : some_spill_live slot sl1 lv1
      -> some_spill_live slot sl2 lv2
      -> some_spill_live slot (ann2 a sl1 sl2) (ann2 b lv1 lv2)
  | SomeSpLvF a b sl_F sl_t lv_F lv_t rms
    : slot_merge slot rms = getAnn ⊝ lv_F
      -> some_spill_live slot sl_t lv_t
      -> (forall n sl_s lv_s,
            get sl_F n sl_s
            -> get lv_F n lv_s
            -> some_spill_live slot sl_s lv_s
        )
      -> some_spill_live slot (annF (a,⎣ rms ⎦) sl_F sl_t)
                              (annF b lv_F lv_t)
.

(* This lemma seems to be wrong *)
Lemma spill_live_small
      ZL Λ s lv k R M sl G slot Lv
  :
    Lv = (slot_merge slot Λ)
    -> live_sound Imperative ZL Lv s lv
    -> spill_sound k ZL Λ (R,M) s sl
    -> some_spill_live slot sl lv
    -> getAnn (spill_live Lv ZL G (do_spill slot s sl)
                                  (discard_merge_sl slot (do_spill_rm slot sl)))
      ⊆ getAnn lv ∪ G
.
Proof.
  intros Lv_Λ lvSnd spSnd ssl.
  general induction lvSnd;
    inversion spSnd;
    inversion ssl;
    simpl; eauto.

Admitted.



Lemma injective_ann
      (X : Type)
      (a b : ann X)
  :
    a = b
    -> match a,b with
      | ann0 an, ann0 bn => an = bn
      | ann1 an a', ann1 bn b' => an = bn /\ a' = b'
      | ann2 an a1 a2, ann2 bn b1 b2 => an = bn /\ a1 = b1 /\ a2 = b2
      | annF an aF a', annF bn bF b' => an = bn /\ aF = bF /\ a' = b'
      | _,_ => True
      end
.
Proof.
  revert b;
    induction a;
    intros b eq_ab;
    induction b;
    eauto;
    try split;
    inversion eq_ab;
    eauto.
Qed.

Lemma spill_live_sound
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (R M : set var)
      (Lv : list (set var))
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
      (alv : ann (set var))
  :  app_expfree s
   -> spill_sound k ZL Λ (R,M) s sl
   -> some_spill_live slot sl alv
   -> live_sound Imperative ZL (slot_merge slot Λ) s alv
   -> live_sound Imperative ZL (slot_merge slot Λ)
                (do_spill slot s sl)
                (spill_live (slot_merge slot Λ) ZL G
                            (do_spill slot s sl)
                            (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound sSpillLv lvSound.

general induction lvSound;
  inversion_clear aeFree;
  inversion sSpillLv;
  inversion spillSound;
  subst sl;
  apply spill_live_sound_s;
  try apply sub_spill_refl; eauto.

- (* tidy up the inversion mess *)
  apply injective_ann in H15.
  destruct H15.
  subst.
  rename sl0 into sl.

  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step. simpl.

  econstructor.
  + eapply IHlvSound; eauto.
  + apply live_exp_sound_incl with (lv':=Exp.freeVars e).
    * apply Exp.live_freeVars.
    * clear. cset_tac.
  +  clear. cset_tac.
  + apply spill_live_G.

- apply injective_ann in H18.
  repeat destruct H18.
  subst.
  rename sl_s into sl1.

  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + eapply IHlvSound1; eauto.
  + eapply IHlvSound2; eauto.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.
  + clear. cset_tac.
  + clear. cset_tac.

- apply injective_ann in H16.
  subst.

  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  intro G'.
  rewrite get_nth with (m:=Z0).
  assert (Z = Z0) as eq_Z.
  { apply get_get_eq with (L:=ZL) (n:=counted l); eauto. }
  assert (blv = R_f ∪ map slot M_f) as eq_blv.
  {
    clear - H0 H15.
    unfold slot_merge in H0.
    change (R_f ∪ map slot M_f)
           with ((fun rm => fst rm ∪ map slot (snd rm)) (R_f,M_f)).
    eapply map_get; eauto.
  }
  econstructor; simpl in *; eauto; rewrite <- eq_Z; eauto.
  + rewrite get_nth with (m:=blv).
    * cset_tac.
    * assumption.
  + subst Z0.
    rewrite get_nth with (m:=blv); eauto.
    intros n y get_y.
    apply live_op_sound_incl with (lv':=Op.freeVars y).
    * apply Op.live_freeVars.
    * repeat apply incl_union_left.
      eapply get_list_union_map; eauto.
  + eauto.

- apply injective_ann in H8.
  subst.

  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.

- apply injective_ann in H23.
  repeat destruct H23.
  inversion H9.
  clear H9.
  subst.
  rename sl_F0 into sl_F.

  specialize (IHlvSound k slot).
  change (snd (getAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t)))
    with (⎣ rms ⎦).
  change (setTopAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t) (∅, ∅, ⎣ rms ⎦))
    with (annF (∅,∅,⎣ rms ⎦) sl_F sl_t).
  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  intros G'.

  assert (forall F sl_F, length F = length sl_F -> fst
      ⊝ (fun (Zs : params * stmt) (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) =>
           (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F
      = fst ⊝ F) as fst_F.
  {
    clear.
    intros F sl_F eq_len.
    assert (length F = length (
                           (fun (Zs : params * stmt)
                              (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕))
                            => (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
           ) as F_len.
    { symmetry. apply zip_length2. assumption. }
    revert dependent sl_F.
    induction F; intros sl_F eq_F eq_zip.
    - eauto.
    - simpl. destruct sl_F.
      + isabsurd.
      + simpl. f_equal.
        apply IHF; simpl in *; omega.
  }

  assert ((fun (rm : ⦃var⦄) (ps : params * stmt) => rm ∪ of_list (fst ps)) ⊜
         (slot_merge slot rms)
         ((fun (Zs : params * stmt) (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) =>
             (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F)
          = (fun (rm : ⦃var⦄) (ps : params * stmt) => rm ∪ of_list (fst ps))
              ⊜ (slot_merge slot rms) F) as dscrd_sl_F.
  {
    clear - H18.
    apply zip_ext_get2; eauto.
    - apply zip_length2. eauto.
    - intros.
      rewrite get_get_eq with (L:=slot_merge slot rms)
                                (n:=n)
                                (x:=x1)
                                (x':=x2); eauto.
      apply get_zip in H0.
      destruct H0 as [x [y [get_x [ get_y y1_eq]]]].
      rewrite <- y1_eq.
      simpl.
      rewrite get_get_eq with (L:=F)
                              (n:=n)
                              (x:=y2)
                              (x':=x); eauto.
  }

  let elim_gets := ( rewrite fst_F;
                     eauto;
                     intros n Zs a get_Zs_sls get_ps_rms;
                     apply get_zip in get_Zs_sls;
                     destruct get_Zs_sls as [Zs' [sl_s [get_Zs' [get_sls Zs_eq]]]];
                     apply get_zip in get_ps_rms;
                     destruct get_ps_rms as [ps [rm_s [get_ps [get_rms splv]]]];
                     apply get_zip in get_ps;
                     destruct get_ps as [ps' [rm_s' [get_ps' [get_rms' ps_eq]]]]
                   ) in

  econstructor;  simpl in *; eauto; [ | | elim_gets | elim_gets ].
  + rewrite fst_F; eauto. rewrite dscrd_sl_F.
    rewrite H10.
    apply live_sound_monotone with (LV:= getAnn ⊝ als ++ slot_merge slot Λ).
    * apply live_sound_monotone3 with (lv:= spill_live
        (getAnn ⊝ als ++ slot_merge slot Λ)
        (fst ⊝ F ++ ZL) ∅ (do_spill slot t sl_t)
        (discard_merge_sl slot (do_spill_rm slot sl_t))).
      -- apply spill_live_setequal.
         apply PIR2_app.
         ++ apply PIR2_get.
            ** intros n x x' get_x get_x'.
               apply map_get_4 in get_x.
               destruct get_x as [y [get_y x_eq]].
               apply get_zip in get_x'.
               destruct get_x' as [al [ps [get_al [get_ps x'_eq]]]].
               apply map_get_4 in get_al.
               destruct get_al as [a [get_a al_eq]].
               apply get_get_eq with (x:=y) in get_a; eauto.
               subst.
               specialize (H2 n ps a get_ps get_y).
               clear - H2. destruct H2.
               change (Equal_pw ⦃var⦄ var In (getAnn a) (getAnn a ∪ of_list (fst ps)))
               with (getAnn a [=] getAnn a ∪ of_list (fst ps)).
               cset_tac.
            ** rewrite zip_length2; eauto.
               rewrite Coqlib.list_length_map.
               eauto.
         ++ apply PIR2_refl.
            unfold Reflexive.
            intros.
            change (Equal_pw ⦃var⦄ var In x x)
            with (x [=] x).
            eauto with cset.
      -- eapply IHlvSound; eauto.
         rewrite <- H10.
         unfold slot_merge.
         symmetry.
         apply Coqlib.list_append_map.
    * apply PIR2_app with (L2:=slot_merge slot Λ).
      -- apply PIR2_get.
         ++ intros n x x' get_x get_x'.
            apply map_get_4 in get_x.
            destruct get_x as [a [get_a eq_a]].
            apply map_get_4 in get_x'.
            destruct get_x' as [al [get_al eq_al]].
            apply get_zip in get_a.
            destruct get_a as [ps [rm_s [get_ps [get_rm_s eq_a']]]].
            apply get_zip in get_ps.
            destruct get_ps as [ps' [ sl' [get_ps' [get_sl' eq_ps]]]].
            apply map_get_4 in get_rm_s.
            destruct get_rm_s as [sl'' [ get_sl'' eq_rm_s]].
            apply map_get_4 in get_sl''.
            destruct get_sl'' as [sl''' [get_sl''' eq_sl'']].
            subst.
            simpl.
            apply get_get_eq with (x':=sl') in get_sl'''; eauto.
            subst.

            (* the following conjecture might be unprovable/wrong *)
            assert (getAnn (spill_live (getAnn ⊝ als ++ slot_merge slot Λ)
                                       (fst ⊝ F ++ ZL)
                                       (of_list (fst ps'))
                                       (do_spill slot (snd ps') sl')
                                       (discard_merge_sl slot (do_spill_rm slot sl')))
                           ⊆ getAnn al) as splvsmall.
            {
              specialize (H2 n ps' al get_ps' get_al).
              assert (exists rm, get rms n rm) as [rm get_rm].
              {
                apply get_length_eq with (L:=F) (x:=ps'); eauto.
              }
              erewrite spill_live_small with (lv:=al)
                                             ( Λ:=rms ++ Λ )
                                             ( k:=k )
                                             ( R:=fst rm )
                                             ( M:=snd rm );
              eauto with cset.
              ** unfold slot_merge.
                 rewrite Coqlib.list_append_map.
                 rewrite <- H10.
                 unfold slot_merge.
                 reflexivity.
              ** apply H24 with (n:=n); eauto.
                 replace (fst rm, snd rm) with rm; eauto.
                 apply injective_projections; simpl; eauto.
            }
            rewrite <- splvsmall.
            apply ann_R_get.
            apply spill_live_subset.
            apply PIR2_app.
            Focus 2. apply PIR2_refl. unfold Reflexive. apply subset_refl.
            apply PIR2_get.
            intros n0 a b get_a get_b.
            apply get_zip in get_a.
            destruct get_a as [x [y [get_x [get_y eq_a]]]].
            apply map_get_4 in get_x.
            destruct get_x as [x' [get_x' eq_x]].
            apply map_get_4 in get_b.
            destruct get_b as [y' [get_y' eq_b]].
            apply get_get_eq with (x':=x') in get_y'; eauto.
            ** subst.
               specialize (H2 n0 y x' get_y get_x').
               clear - H2. cset_tac.
            ** rewrite zip_length2; eauto.
               rewrite Coqlib.list_length_map; eauto.
         ++ do 2 rewrite Coqlib.list_length_map; eauto.
            do 2 rewrite zip_length2; eauto.
            do 2 rewrite Coqlib.list_length_map; eauto.
      -- apply PIR2_refl.
         unfold Reflexive.
         apply subset_refl.
  + set (A := (fun (Zs : params * stmt) (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) =>
                 (fst Zs, do_spill slot (snd Zs) sl_s)) ⊜ F sl_F).
    symmetry. apply zip_length2.
    repeat rewrite Coqlib.list_length_map.
    subst A.
    rewrite zip_length2; eauto.
  + assert (fst Zs = fst Zs') as fst_ZsZs'.
    { rewrite <- Zs_eq. simpl. reflexivity. }
    admit.
  + assert (fst Zs = fst Zs') as fst_ZsZs'.
    { rewrite <- Zs_eq. simpl. reflexivity. }
    rewrite fst_ZsZs'.
    rewrite <- splv.
    rewrite <- ps_eq.
    simpl.
    rewrite get_get_eq with (L:=F) (n:=n) (x:=ps') (x':=Zs'); eauto.
    split; [ | auto].
    apply spill_live_G_set.