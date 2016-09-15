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
      exploit H2; eauto.
      change (Equal_pw ⦃var⦄ var In (getAnn a ∪ of_list (fst p)) (getAnn a))
      with (getAnn a ∪ of_list (fst p) [=] getAnn a).
      cset_tac.
    * apply IHals; eauto.
      intros.
      apply H2 with (n:= S(n)); econstructor; eauto.
Qed.




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
    with (Sp':=∅) (L':=∅) (sl':=sl0);
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


Definition merge := List.map (fun (RM : set var * set var)
                                  => fst RM ∪ snd RM).


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


Lemma spill_live_remove_G
      Lv ZL G s sl G'
  :
    getAnn (spill_live Lv ZL G s sl) \ G
           ⊆ getAnn (spill_live Lv ZL G' s sl)
.
Proof.
  destruct s, sl, a; simpl; cset_tac.
Qed.


Lemma of_list_tl_hd
      (L : list var)
  :
    L <> nil
    ->  of_list L [=] of_list (tl L) ∪ singleton (hd 0 L)
.
Proof.
  intro N.
  induction L; simpl; eauto.
  - isabsurd.
  - cset_tac.
Qed.


Lemma tl_hd_set_incl
      (s t : ⦃var⦄)
  :
    s \ of_list (tl (elements t)) ⊆ s \ t ∪ singleton (hd 0 (elements t))
.
Proof.
  hnf.
  intros a H.
  apply diff_iff in H.
  destruct H as [in_s not_in_tl_t].
  apply union_iff.
  decide (a ∈ t).
  - right.
    rewrite <- of_list_elements in i.
    rewrite of_list_tl_hd in i.
    + apply union_iff in i.
      destruct i.
      * contradiction.
      * eauto.
    + intro N.
      apply elements_nil_eset in N.
      rewrite of_list_elements in i.
      rewrite N in i.
      isabsurd.
  - left.
    cset_tac.
Qed.

Lemma map_singleton
      (f : var -> var)
      (x : var)
  :
    map f (singleton x) [=] singleton (f x)
.
Proof.
  apply set_incl.
  - hnf.
    intros a a_in_f.
    rewrite singleton_iff in a_in_f.
    rewrite <- a_in_f.
    apply map_1; eauto.
  - hnf.
    intros a a_in_map.
    apply map_2 in a_in_map; eauto.
    destruct a_in_map as [a' [in_x a_eq]].
    rewrite singleton_iff in in_x.
    rewrite <- in_x in a_eq.
    rewrite a_eq.
    cset_tac.
Qed.


Lemma spill_live_small_s
      (sl sl' : ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄))))
      ZL G
      slot s Λ R M
  :
    let Sp := fst (fst (getAnn sl )) in
    let L  := snd (fst (getAnn sl )) in
    let Sp':= fst (fst (getAnn sl')) in
    let L' := snd (fst (getAnn sl')) in
    sub_spill sl' sl
    -> Sp ⊆ R
    -> L  ⊆ Sp ∪ M
    -> (forall G', getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G'
           (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))))
           (discard_merge_sl slot (do_spill_rm' slot 0 sl)))
        ⊆ (R ∪ L) ∪ map slot (Sp ∪ M) ∪ G')
    -> getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl')
           (discard_merge_sl slot (do_spill_rm' slot (count sl') sl)))
        ⊆ (R ∪ L \ L') ∪ map slot (Sp \ Sp' ∪ M) ∪ G
.
Proof.
  intros Sp L Sp' L' sub spr lspm sls.

  remember (cardinal Sp') as card_Sp'.
  general induction card_Sp'.
  - remember (cardinal L') as card_L'.
    general induction card_L'.
    + assert (((R ∪ L ∪ map slot (Sp ∪ M) ∪ G) \ (L ∩ L')) \ (map slot (Sp ∩ Sp'))
                                                       ∪ R ∪ map slot M ∪ G
          ⊆ R ∪ L \ L' ∪ map slot (Sp \ Sp' ∪ M) ∪ G) as set_EQ.
      {
        repeat rewrite SetOperations.map_app; eauto.
        rewrite map_slot_cut; eauto.
        rewrite map_slot_minus; eauto.
        clear. cset_tac.
      }
      rewrite <- set_EQ.
      rewrite <- sls.
      assert (count sl' = 0) as count_zero.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite count_zero.
      enough (do_spill slot s sl'
              = do_spill slot s (setTopAnn sl (∅,∅, snd (getAnn sl))))
        as do_spill_eq.
      {
        rewrite do_spill_eq.
        symmetry in Heqcard_Sp'.
        apply cardinal_Empty in Heqcard_Sp'.
        apply empty_inter_2 with (s0:=Sp) in Heqcard_Sp'.
        apply empty_is_empty_1 in Heqcard_Sp'.
        rewrite Heqcard_Sp'.
        symmetry in Heqcard_L'.
        apply cardinal_Empty in Heqcard_L'.
        apply empty_is_empty_1 in Heqcard_L'.
        rewrite Heqcard_L'.
        rewrite SetOperations.map_empty; eauto.
        clear. cset_tac.
      }
      erewrite do_spill_empty_invariant
      with (Sp':=∅) (L':=∅) ;
        try apply cardinal_Empty;
        try apply empty_1;
        eauto.
      unfold sub_spill in sub.
      destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
      rewrite top_sl'.
      rewrite getAnn_setTopAnn.
      rewrite setTopAnn_setTopAnn.
      rewrite eq_rm.
      reflexivity.
    + assert (count sl' = S card_L') as count_sl'.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite do_spill_L;
        [ | apply cardinal_Empty;
            subst Sp'
          | intro N ;
            apply cardinal_Empty in N ;
            subst L';
            omega ];
        eauto.
      rewrite count_sl'.
      rewrite do_spill_rm_s.
      rewrite discard_merge_sl_step.
      simpl.
      assert (count (setTopAnn sl'
                               (fst (fst (getAnn sl')),
                                of_list (tl (elements (snd (fst (getAnn sl'))))),
               snd (getAnn sl'))) = card_L') as count_L'.
      { eapply count_reduce_L; eauto. }
      rewrite <- count_L'.
      assert (Sp' [=] ∅) as Sp'_empty.
      {
        clear - Heqcard_Sp'.
        apply empty_is_empty_1.
        apply cardinal_Empty.
        eauto.
      }
      apply union_incl_split; [ apply union_incl_split | ].
      * assert (forall s t u : set var, s ⊆ t ∪ u -> s \ u ⊆ t) as set_eq.
        { clear. cset_tac.
          hnf in H.
          exploit H; eauto.
          apply union_iff in H0.
          destruct H0; eauto. contradiction.
        }
        assert (forall s t : set var, s \ t [=] s \ t \ t) as set_eq2.
        { clear. cset_tac. }
        rewrite set_eq2.
        apply set_eq.
        rewrite spill_live_remove_G with (G':=G).
        set (sl'' := setTopAnn _ _).
        let reset :=
            (subst L; subst L'; subst Sp; subst Sp';
             set (Sp := fst (fst (getAnn sl))) in *;
             set (L := snd (fst (getAnn sl))) in *;
             set (Sp' := fst (fst (getAnn sl'))) in *;
             set (L' := snd (fst (getAnn sl'))) in *) in
                 rewrite IHcard_L';
             simpl; eauto; reset.
        -- enough (L \ snd (fst (getAnn sl''))
                          ⊆ L \ L' ∪ singleton (hd 0 (elements L'))) as enog.
           {
            rewrite enog.
            subst sl''.
            rewrite getAnn_setTopAnn.
            simpl.
            clear.
            cset_tac.
          }
          subst sl''.
          rewrite getAnn_setTopAnn.
          simpl.
          rewrite tl_hd_set_incl.
          reflexivity.
        -- subst sl''.
           unfold sub_spill in *.
           destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
           repeat split.
           ** rewrite top_sl'.
              repeat rewrite getAnn_setTopAnn.
              rewrite setTopAnn_setTopAnn.
              reflexivity.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst Sp'.
              apply sub_Sp.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst L'.
              rewrite tl_set_incl.
              apply sub_L.
           ** rewrite getAnn_setTopAnn.
              simpl.
              apply eq_rm.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           eauto.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           symmetry.
           apply cardinal_set_tl.
           rewrite of_list_elements.
           eauto.
      * assert (hd 0 (elements (snd (fst (getAnn sl'))))
                    ∈ (snd (fst (getAnn sl')))) as hd_in.
        {
          apply hd_in_elements.
          intro N.
          subst L'.
          rewrite N in Heqcard_L'.
          rewrite empty_cardinal in Heqcard_L'.
          clear - Heqcard_L'. isabsurd.
        }
        apply incl_singleton in hd_in.
        rewrite map_slot_incl with (slot:=slot) in hd_in.
        assert (singleton (slot (hd 0 (elements (snd (fst (getAnn sl'))))))
                          ⊆ map slot (snd (fst (getAnn sl')))) as hd_in_set.
        { rewrite <- hd_in. clear. cset_tac. }
        rewrite hd_in_set.
        rewrite Sp'_empty.
        enough (map slot (snd (fst (getAnn sl'))) ⊆ map slot (Sp ∪ M)) as enog.
        { revert enog. clear.
          repeat rewrite SetOperations.map_app; eauto.
          rewrite map_slot_minus.
          intros.
          rewrite H.
          rewrite SetOperations.map_empty; eauto.
          apply union_incl_split; cset_tac.
        }
        apply map_slot_incl.
        unfold sub_spill in sub.
        destruct sub as [_ [_ [sub_L _]]].
        rewrite sub_L.
        subst L.
        eauto.
      * clear. cset_tac.
  - assert (count sl' = S card_Sp' + cardinal L') as count_sl'.
      { unfold count.
        subst Sp'.
        subst L'.
        rewrite <- Heqcard_Sp'.
        omega.
      }
      rewrite do_spill_Sp;
        [ | intro N ;
            apply cardinal_Empty in N ;
            subst Sp';
            omega ];
        eauto.
      rewrite count_sl'.
      simpl.
      rewrite do_spill_rm_s.
      rewrite discard_merge_sl_step.
      simpl.
      assert (count (setTopAnn sl'
                               (of_list (tl (elements (fst (fst (getAnn sl'))))),
                                snd (fst (getAnn sl')),
               snd (getAnn sl'))) = card_Sp' + cardinal L') as count_Sp'.
      { eapply count_reduce_Sp; eauto. }
      rewrite <- count_Sp'.
      apply union_incl_split; [ apply union_incl_split | ].
      * assert (forall s t u : set var, s ⊆ t ∪ u -> s \ u ⊆ t) as set_eq.
        { clear. cset_tac.
          hnf in H.
          exploit H; eauto.
          apply union_iff in H0.
          destruct H0; eauto. contradiction.
        }
        assert (forall s t : set var, s \ t [=] s \ t \ t) as set_eq2.
        { clear. cset_tac. }
        rewrite set_eq2.
        apply set_eq.
        rewrite spill_live_remove_G with (G':=G).
        set (sl'' := setTopAnn _ _).
        let reset :=
            (subst L; subst L'; subst Sp; subst Sp';
             set (Sp := fst (fst (getAnn sl))) in *;
             set (L := snd (fst (getAnn sl))) in *;
             set (Sp' := fst (fst (getAnn sl'))) in *;
             set (L' := snd (fst (getAnn sl'))) in *) in
                 rewrite IHcard_Sp';
             simpl; eauto; reset.
        -- enough (Sp \ fst (fst (getAnn sl''))
                          ⊆ Sp \ Sp' ∪ singleton ((hd 0 (elements Sp')))) as enog.
           {
            rewrite enog.
            subst sl''.
            rewrite getAnn_setTopAnn.
            simpl.
            clear.
            repeat rewrite SetOperations.map_app; eauto.
            rewrite map_singleton.
            cset_tac.
          }
          subst sl''.
          rewrite getAnn_setTopAnn.
          simpl.
          rewrite tl_hd_set_incl.
          reflexivity.
        -- subst sl''.
           unfold sub_spill in *.
           destruct sub as [top_sl' [sub_Sp [sub_L eq_rm]]].
           repeat split.
           ** rewrite top_sl'.
              repeat rewrite getAnn_setTopAnn.
              rewrite setTopAnn_setTopAnn.
              reflexivity.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst Sp'.
              rewrite tl_set_incl.
              apply sub_Sp.
           ** rewrite getAnn_setTopAnn.
              simpl.
              subst L'.
              apply sub_L.
           ** rewrite getAnn_setTopAnn.
              simpl.
              apply eq_rm.
        -- subst sl''.
           rewrite getAnn_setTopAnn.
           simpl.
           symmetry.
           apply cardinal_set_tl.
           rewrite of_list_elements.
           eauto.
      * assert (hd 0 (elements (fst (fst (getAnn sl'))))
                    ∈ (fst (fst (getAnn sl')))) as hd_in.
        {
          apply hd_in_elements.
          intro N.
          subst Sp'.
          rewrite N in Heqcard_Sp'.
          rewrite empty_cardinal in Heqcard_Sp'.
          clear - Heqcard_Sp'. isabsurd.
        }
        apply incl_singleton in hd_in.
        subst Sp Sp' L L'.
        rewrite <- spr.
        unfold sub_spill in sub.
        destruct sub as [_ [sub_Sp' _]].
        rewrite <- sub_Sp'.
        rewrite hd_in.
        clear.
        cset_tac.
      * clear. cset_tac.
Qed.



Corollary spill_live_small_s'
      (sl : ann (⦃var⦄ * ⦃var⦄ * option (list (⦃var⦄ * ⦃var⦄))))
      ZL G
      slot s Λ R M
  :
    let Sp := fst (fst (getAnn sl )) in
    let L  := snd (fst (getAnn sl )) in
    Sp ⊆ R
    -> L ⊆ Sp ∪ M
    -> (forall G', getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G'
           (do_spill slot s (setTopAnn sl (∅,∅,snd (getAnn sl))))
           (discard_merge_sl slot (do_spill_rm' slot 0 sl)))
        ⊆ (R ∪ L) ∪ map slot (Sp ∪ M) ∪ G')
    -> getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl)
           (discard_merge_sl slot (do_spill_rm' slot (count sl) sl)))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros Sp L sp_sub l_sub.
  assert (R [=] R ∪ L \ L).
  { clear. cset_tac. }
  assert (M [=] Sp \ Sp ∪ M).
  { clear. cset_tac. }
  rewrite H.
  rewrite H0.
  apply spill_live_small_s;
    subst Sp; subst L;
      [ apply sub_spill_refl | | ];
      eauto.
Qed.


Lemma spill_live_small
      ZL Λ Lv s G k R M sl slot al (F : list(params * stmt))
  :
    PIR2 Equal Lv (merge Λ)
    -> live_sound Imperative ZL Lv s al
    -> spill_sound k ZL Λ (R,M) s sl
    -> some_spill_live sl al
    -> getAnn
        (spill_live
           (slot_merge slot Λ)
           (slot_lift_params slot ⊜ ZL Λ)
            G
           (do_spill slot s sl)
           (discard_merge_sl slot (do_spill_rm slot sl)))
        ⊆ R ∪ map slot M ∪ G
.
Proof.
  intros pir2 lvSnd spSnd ssl.
  general induction lvSnd;
    invc spSnd;
    invc ssl;
    apply spill_live_small_s';
    try apply sub_spill_refl;
    simpl in *; eauto; intros G';
      rewrite empty_cardinal;
      simpl.
  - rewrite IHlvSnd with (R:={x; (R \ K ∪ L) \ Kx})
                         (M:=Sp ∪ M); eauto.
    rewrite H13.
    rewrite SetOperations.map_app; eauto.
    clear.
    cset_tac.
  - rewrite IHlvSnd1 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M); eauto.
    rewrite IHlvSnd2 with (R:=R \ K ∪ L)
                          (M:=Sp ∪ M); eauto.
    rewrite H11.
    rewrite SetOperations.map_app; eauto.
    clear.
    cset_tac.
  - repeat apply union_incl_split.
    + admit.
    + eapply get_nth in H14.
      assert (nth l (slot_merge slot Λ) ∅ [=] R_f ∪ map slot M_f).
      {
        admit.
      }
      rewrite H4.
      assert (of_list (nth l (slot_lift_params slot ⊜ ZL Λ) nil) === of_list Z0).
      {
        admit.
      }
      rewrite H5.
      rewrite SetOperations.map_app; eauto.
      clear - H16 H17.
      apply map_slot_incl with (slot:=slot) in H17.
      rewrite map_slot_minus in H17.
      admit.
    + clear. cset_tac.
  - rewrite H7.
    cset_tac.
  - rewrite IHlvSnd.
Admitted.
(*

proof.
  intros lv_λ lvsnd spsnd ssl get_rms get_f.
  general induction lvsnd;
    invt spill_sound;
    invt some_spill_live;
(*    apply spill_live_small_s;*)

    simpl; eauto.
  - rewrite empty_cardinal. simpl.
    rewrite ihlvsnd.
    assert (sp ⊆ r) as spr. { admit. }
    assert (l  ⊆ m) as lm.  { admit. }
    assert (lv [=] r ∪ m) as lvrm. { admit. }
    rewrite lvrm.
    rewrite h11.

Admitted.
*)


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


Lemma dscrd_sl_F
      rms F sl_F slot
  :
    length F = length sl_F
    -> length F = length rms
    -> (fun (rm : ⦃var⦄) (ps0 : params * stmt) => rm ∪ of_list (fst ps0))
            ⊜ (slot_merge slot rms)
            ((fun (Zs : params * stmt)
                (sls_rm : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕) * (⦃var⦄ * ⦃var⦄)) =>
              let (sl_s, rm) := sls_rm in
              (slot_lift_params slot (fst Zs) rm, do_spill slot (snd Zs) sl_s)) ⊜ F
             ((fun (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) (rm : ⦃var⦄ * ⦃var⦄) =>
                 (sl_s, rm)) ⊜ sl_F rms))
    = (fun (rm : ⦃var⦄) (ps : params * stmt) => rm ∪ of_list (fst ps))
        ⊜ (slot_merge slot rms) ((fun Zs rm => (slot_lift_params slot (fst Zs) rm,snd Zs))
                                   ⊜ F rms)
.
Proof.
  intros len_slF len_rms.
  general induction rms;
    simpl in *; eauto.
  destruct F;
    simpl in *; eauto.
  destruct sl_F;
    simpl in *; eauto.
  - isabsurd.
  - f_equal. apply IHrms; eauto.
Qed.

(*

Lemma dscrd_sl_F'
      rms F sl_F slot
  :
    length F = length sl_F
    -> length F = length rms
    -> (fun (rm : ⦃var⦄) (ps0 : params * stmt) => rm ∪ of_list (fst ps0))
            ⊜ (slot_merge slot rms)
            ((fun (Zs : params * stmt)
                (sls_rm : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕) * (⦃var⦄ * ⦃var⦄)) =>
              let (sl_s, rm) := sls_rm in
              (slot_lift_params slot (fst Zs) rm, do_spill slot (snd Zs) sl_s)) ⊜ F
             ((fun (sl_s : ann (⦃var⦄ * ⦃var⦄ * ؟ 〔⦃var⦄ * ⦃var⦄〕)) (rm : ⦃var⦄ * ⦃var⦄) =>
                 (sl_s, rm)) ⊜ sl_F rms))
    = (fun (rm : ⦃var⦄) (ps : params * stmt) => rm ∪ of_list (fst ps))
        ⊜ (slot_merge slot rms) ((fun Zs rm => (slot_lift_params slot (fst Zs) rm,snd Zs))
                                   ⊜ F rms)
.
Proof.
  intros len_slF len_rms.
  general induction rms;
    simpl in *; eauto.
  destruct F;
    simpl in *; eauto.
  destruct sl_F;
    simpl in *; eauto.
  - isabsurd.
  - f_equal. apply IHrms; eauto.
Qed.

 *)


Lemma slot_lift_params_app
      L1 L2 L1' L2' slot
  :
    length L1 = length L1'
    -> slot_lift_params slot ⊜ L1 L1' ++ slot_lift_params slot ⊜ L2 L2'
      = slot_lift_params slot ⊜ (L1 ++ L2) (L1' ++ L2')
.
Proof.
  intros.
  rewrite zip_app; eauto with len.
Qed.


Lemma slot_merge_app
      (L1 L2: list (set var * set var))
      (slot : var -> var)
  :
    slot_merge slot L1 ++ slot_merge slot L2
      = slot_merge slot (L1 ++ L2)
.
Proof.
  intros.
  unfold slot_merge.
  rewrite map_app; eauto.
Qed.


Lemma spill_live_sound
      (k : nat)
      (slot : var -> var)
      (ZL : list params)
      (G : set var)
      (Λ : list (set var * set var))
      (R M : set var)
      (s : stmt)
      (Lv : list (set var))
      (sl : ann (set var * set var * option (list (set var * set var))))
      (alv : ann (set var))
  :  app_expfree s
   -> spill_sound k ZL Λ (R,M) s sl
   -> some_spill_live sl alv
   -> PIR2 Equal (merge Λ) Lv
   -> live_sound Imperative ZL (merge Λ) s alv
   -> live_sound Imperative
                (slot_lift_params slot ⊜ ZL Λ)
                (slot_merge slot Λ)
                (do_spill slot s sl)
                (spill_live (slot_merge slot Λ)
                            (slot_lift_params slot ⊜ ZL Λ)
                             G
                            (do_spill slot s sl)
                            (discard_merge_sl slot (do_spill_rm slot sl))).

Proof.
intros aeFree spillSound sSpillLv PEQ lvSound.

general induction lvSound;
  invc aeFree;
  inv sSpillLv;
  inv spillSound;
  apply spill_live_sound_s;
  try apply sub_spill_refl; eauto.

- rename sl0 into sl.

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

- rewrite do_spill_empty;
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

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  intro G'.

  assert (get (slot_lift_params slot ⊜ ZL Λ) l (slot_lift_params slot Z0 (R_f,M_f)))
    as get_slp.
  { apply zip_get; eauto. }
  rewrite get_nth with (m:=slot_lift_params slot Z0 (R_f,M_f)); eauto.
  assert (Z = Z0) as eq_Z.
  { apply get_get_eq with (L:=ZL) (n:=counted l); eauto. }
  subst Z0.
  assert (get (slot_merge slot Λ) l (R_f ∪ map slot M_f)) as get_rfmf.
  { apply map_get_eq with (x:=(R_f,M_f)); simpl; eauto. }

  econstructor; simpl in *; eauto;
    [ erewrite get_nth
    | unfold slot_lift_params; eauto with len
    | erewrite get_nth ]
    ; eauto.
  + clear. cset_tac.
  + admit. (* We need some new assumptions to prove this *)
  + intros n y get_y.
    apply live_op_sound_incl with (lv':=Op.freeVars y).
    * apply Op.live_freeVars.
    * repeat apply incl_union_left.
      eapply get_list_union_map; eauto.

- rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.

  econstructor.
  + apply live_op_sound_incl with (lv':=Op.freeVars e).
    * apply Op.live_freeVars.
    * clear. cset_tac.




- specialize (IHlvSound k slot).
  change (snd (getAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t)))
    with (⎣ rms ⎦).
  change (setTopAnn (annF (Sp, L, ⎣ rms ⎦) sl_F sl_t) (∅, ∅, ⎣ rms ⎦))
    with (annF (∅,∅,⎣ rms ⎦) sl_F sl_t).
  rewrite do_spill_empty;
    [ | simpl; apply empty_1 | simpl; apply empty_1].
  rewrite do_spill_rm_zero.
  rewrite discard_merge_sl_step; simpl.
  intros G'.

  econstructor;  simpl in *; eauto.
  + rewrite fst_F; eauto.
    apply live_sound_monotone with (LV:= slot_merge slot rms ++ slot_merge slot Λ).
    * apply live_sound_ann_ext with (lv:= spill_live
        (slot_merge slot rms ++ slot_merge slot Λ)
        (slot_lift_params slot ⊜ (fst ⊝ F) rms ++ slot_lift_params slot ⊜ ZL Λ)
         ∅
        (do_spill slot t sl_t)
        (discard_merge_sl slot (do_spill_rm slot sl_t))).
      -- apply spill_live_equal.
         apply PIR2_app.
         ++ apply PIR2_get.
            ** intros.
               erewrite get_get_eq with (x:=x)
                                        (x':=x')
                                        (L:=slot_merge slot rms)
                                        (n:=n); eauto.
           ** reflexivity.
         ++ apply PIR2_refl; eauto.
      --
         rewrite slot_lift_params_app; eauto with len.
         rewrite slot_merge_app.
         eapply IHlvSound; eauto.
         ** unfold merge.
            rewrite map_app.
            rewrite <- H10.
            reflexivity.
         ** apply PIR2_app; eauto.
            apply PIR2_refl; eauto.
    * apply PIR2_app with (L2:=slot_merge slot Λ).
      -- apply PIR2_get.
         ++ intros.
            unfold slot_merge in H5.
            inv_get; simpl.
            rewrite slot_merge_app.
            rewrite slot_lift_params_app; eauto with len.
            erewrite spill_live_small with (R:=fst x0) (M:=snd x0); eauto.
            ** exploit H2 as H2'; eauto.
               destruct H2' as [H2' _].
               unfold slot_lift_params.
               rewrite of_list_elements.
               rewrite H2'.
               assert (forall s t, map slot (s ∩ t) [=] map slot s ∩ map slot t) as map_slot_cut.
               { admit. } (* we need assumptions for this *)
               rewrite map_slot_cut.
               cset_tac.
            ** unfold merge. rewrite map_app.
               unfold merge in H10.
               rewrite H10.
               eapply H0; eauto.
            ** eapply H23; eauto. admit. (* easy *)
            ** admit. (* easy *)
         ++ unfold slot_merge.
            do 2 rewrite Coqlib.list_length_map; eauto.
            do 2 rewrite zip_length2; eauto with len.
      -- apply PIR2_refl; eauto.
  + symmetry. apply zip_length2.
    repeat rewrite Coqlib.list_length_map.
    rewrite zip_length2; eauto with len.
  + intros.
    inv_get.
    simpl.
    rewrite fst_F; eauto.
    rewrite slot_merge_app.
    rewrite slot_lift_params_app.
    apply live_sound_monotone with (LV:=slot_merge slot rms ++ slot_merge slot Λ).
     * apply live_sound_ann_ext with (lv:= spill_live
        (slot_merge slot rms ++ slot_merge slot Λ)
        (slot_lift_params slot ⊜ ((fst ⊝ F) ++ ZL) (rms ++ Λ))
        (of_list (slot_lift_params slot (fst x) x3))
        (do_spill slot (snd x) x2)
        (discard_merge_sl slot (do_spill_rm slot x2))).
       -- apply spill_live_equal.
          rewrite <- slot_merge_app.
          apply PIR2_app.
          ++ apply PIR2_get.
             ** intros.
                erewrite get_get_eq with (x:=x1)
                                           (x':=x')
                                           (L:=slot_merge slot rms)
                                           (n:=n0); eauto.
           ** reflexivity.
         ++ apply PIR2_refl; eauto.
      -- rewrite slot_merge_app.
         eapply H1 with (R:=fst x3) (M:=snd x3); eauto.
         ** eapply H23 ; eauto.
            rewrite injective_projections with (p2:=x3); eauto.
         ** unfold merge.
            rewrite map_app.
            rewrite <- H10.
            reflexivity.
         ** apply PIR2_app; eauto.
            apply PIR2_refl; eauto.
    * apply PIR2_app with (L2:=slot_merge slot Λ).
      -- apply PIR2_get.
         ++ intros.
            unfold slot_merge in H14.
            inv_get; simpl.
            erewrite spill_live_small with (R:=fst x4) (M:=snd x4); eauto.
            ** exploit H2 as H2'; eauto.
               destruct H2' as [H2' _].
               unfold slot_lift_params.
               rewrite of_list_elements.
               rewrite H2'.
               assert (forall s t, map slot (s ∩ t) [=] map slot s ∩ map slot t) as map_slot_cut.
               { admit. } (* we need assumptions for this *)
               rewrite map_slot_cut.
               cset_tac.
            ** unfold merge. rewrite map_app.
               unfold merge in H10.
               rewrite H10.
               eapply H0; eauto.
            ** eapply H23; eauto. admit. (* easy *)
            ** admit. (* easy *)
         ++ unfold slot_merge.
            do 2 rewrite Coqlib.list_length_map; eauto.
            do 2 rewrite zip_length2; eauto with len.
      -- apply PIR2_refl; eauto.
    * eauto with len.
  + intros.
    inv_get.
    simpl.
    split; [ | auto].
    apply spill_live_G_set.