Require Import Util IL RenamedApart LabelsDefined OptionR.
Require Import Annotation Exp SetOperations Liveness.Liveness Restrict.

Set Implicit Arguments.

Lemma plus_minus_eq n m
  : n + m - n = m.
Proof.
  omega.
Qed.

Ltac inv_get_step_some_minus :=
  match goal with
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) ?k _,
          H' : get ?A ?k _ |- _ ] =>
    eapply get_app_lt_1 in H; [| eauto 20 with len]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) ?k _,
          H' : get ?B ?k _ |- _ ] =>
    eapply get_app_lt_1 in H; [| eauto 20 with len]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) (❬?B❭ + ?n) _ |- _ ] =>
    let LENEQ := fresh "LenEq" in
    assert (LENEQ:❬f ⊝ (g1 ⊝ A) \\ (g2 ⊝ B)❭ = ❬B❭) by eauto with len;
    rewrite get_app_ge in H;
    [ rewrite LENEQ in H; rewrite plus_minus_eq in H
    | rewrite LENEQ; omega]
  | [ H : get (?f ⊝ (?g1 ⊝ ?A) \\ (?g2 ⊝ ?B) ++ ?C) (❬?A❭ + ?n) _ |- _ ] =>
    let LENEQ := fresh "LenEq" in
    assert (LENEQ:❬f ⊝ (g1 ⊝ A) \\ (g2 ⊝ B)❭ = ❬A❭) by eauto with len;
    rewrite get_app_ge in H;
    [ rewrite LENEQ in H; rewrite plus_minus_eq in H
    | rewrite LENEQ; omega]
  end.

Smpl Add inv_get_step_some_minus : inv_get.

(** * Definition of Coherence: [srd] *)

Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
| srdExp DL x e s lv al
  : srd (restr (lv \ singleton x) ⊝ DL) s al
    -> srd DL (stmtLet x e s) (ann1 lv al)
| srdIf DL e s t lv als alt
  : srd DL s als
    -> srd DL t alt
    -> srd DL (stmtIf e s t) (ann2 lv als alt)
| srdRet e DL lv
  : srd DL (stmtReturn e) (ann0 lv)
| srdGoto DL lv G' f Y
  : get DL (counted f) (Some G')
    -> srd DL (stmtApp f Y) (ann0 lv)
| srdLet DL F t lv als alt
  : length F = length als
    -> (forall n Zs a, get F n Zs -> get als n a ->
                 srd (restr (getAnn a \ of_list (fst Zs)) ⊝
                            (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) (snd Zs) a)
    -> srd (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL) t alt
    -> srd DL (stmtFun F t) (annF lv als alt).


(** ** Some monotonicity properties *)

Lemma srd_monotone (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR Equal) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite List.map_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.

Lemma srd_monotone2 (DL DL' : list (option (set var))) s a
 : srd DL s a
   -> PIR2 (fstNoneOrR (flip Subset)) DL DL'
   -> srd DL' s a.
Proof.
  intros. general induction H; eauto using srd.
  - econstructor.
    eapply IHsrd; eauto. eapply restrict_subset2; eauto.
  - destruct (PIR2_nth H0 H); eauto; dcr. inv H3.
    econstructor; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite List.map_app.
      eapply PIR2_app; eauto.
      eapply restrict_subset2; eauto.
    + eapply IHsrd. eapply PIR2_app; eauto.
Qed.

(** *** Every renamed apart program is coherent *)
(** Note that this lemma also builds the liveness annotation:
    It exploits that we can always claim more variables live *)

Hint Extern 20 =>
match goal with
  | [ H: length ?L = length ?L' |- length ?L = length (List.map ?f ?L')] => rewrite map_length; eauto
end.

Lemma renamedApart_coherent s ang DL
  : renamedApart s ang
    -> labelsDefined s (length DL)
    -> bounded (List.map Some DL) (fst (getAnn ang))
    -> srd (List.map Some DL) s (mapAnn fst ang).
Proof.
  intros. general induction H; invt labelsDefined; simpl in * |- *; pe_rewrite.
  - econstructor; eauto.
    eapply srd_monotone.
    eapply IHrenamedApart; eauto with cset.
    erewrite bounded_restrict_eq; simpl; eauto. eauto with cset.
  - econstructor; eauto.
  - econstructor.
  - edestruct get_in_range as [a ?]; eauto using map_get_1, srd.
  - econstructor; eauto.
    + intros. inv_map H10.
      exploit (H1 _ _ _ H9 H12 ((getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL)); eauto.
      * rewrite app_length. rewrite zip_length2; eauto with len.
        repeat rewrite map_length. rewrite <- H. eauto.
      * edestruct H2; eauto; dcr.
        rewrite List.map_app. eapply bounded_app; split; eauto.
        rewrite H14. eapply get_bounded.
        intros. inv_get. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H10.
        eapply incl_union_right.
        eauto with cset.
        rewrite H14. rewrite <- incl_right; eauto.
      * eapply srd_monotone. eapply H14.
        rewrite getAnn_mapAnn; simpl.
        repeat rewrite List.map_app.
        eapply PIR2_app.
        erewrite bounded_restrict_eq. reflexivity.
        reflexivity. inv_get. edestruct H2; eauto; dcr.
        eapply get_bounded.
        intros. inv_get.
        edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H10.
        decide (n=n0); subst. repeat get_functional.
        rewrite H10; reflexivity.
        exploit H3; eauto using zip_get.
        unfold defVars in H21.
        rewrite H17.
        revert H18 H24; clear_all; cset_tac; intuition; eauto.
        erewrite bounded_restrict_eq; simpl; eauto.
        edestruct H2; eauto; dcr.
        rewrite H15. revert H19; clear_all; cset_tac; intuition; eauto.
    + eapply srd_monotone.
      eapply (IHrenamedApart ((getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL)); eauto.
      * rewrite app_length, zip_length2, map_length, map_length, <- H; eauto with len.
      * pe_rewrite. rewrite List.map_app. rewrite bounded_app. split; eauto.
        eapply get_bounded.
        intros. inv_get.
        edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H10.
        clear_all; cset_tac; intuition.
      * rewrite List.map_app. reflexivity.
Qed.



(** *** In a coherent program, the globals of every function that can eventually be called are live *)

Lemma srd_globals_live_F (isCalled:stmt -> lab -> Prop)  ZL Lv F als f lv' Z' l DL
      (LEN1 : ❬F❭ = ❬als❭) (Len2:❬ZL❭=❬Lv❭) (Len3:❬ZL❭=❬DL❭)
      (IH : forall k Zs, get F k Zs ->
                    forall (ZL : 〔params〕) (Lv : 〔⦃var⦄〕) (DL : 〔؟ ⦃var⦄〕) (alv : ann ⦃var⦄) (f : lab),
                      live_sound Imperative ZL Lv (snd Zs) alv ->
                      srd DL (snd Zs) alv ->
                      PIR2 (ifFstR Equal) DL (Lv \\ ZL) ->
                      isCalled (snd Zs) f ->
                      ❬ZL❭ = ❬Lv❭ ->
                      ❬ZL❭ = ❬DL❭ ->
                      exists (lv : ⦃var⦄) (Z : params), get ZL f Z /\ get DL f ⎣ lv ⎦ /\ lv ⊆ getAnn alv)
      (LS: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (SRD: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          srd (restr (getAnn a \ of_list (fst Zs)) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL))
              (snd Zs) a)
      (PE:PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
               ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL)))
      (CC:callChain isCalled F l f)
      (GetZL : get (fst ⊝ F ++ ZL) l Z')
      (GetLv : get (getAnn ⊝ als ++ Lv) l lv')
      dv (GetDL : get (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL) l ⎣ dv ⎦)
      (dvEq:dv [=] lv' \ of_list Z')
  : exists (lv : ⦃var⦄) (Z : params) dv,
    get (fst ⊝ F ++ ZL) (labN f) Z
    /\ get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ get (restr (lv \ of_list Z) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) (labN f) (Some dv)
    /\ dv [=] (lv \ of_list Z) /\ lv \ of_list Z ⊆ lv' \ of_list Z'.
Proof.
  general induction CC.
  - do 2 eexists; eexists (dv); split; [| split; [|split]]; eauto.
    eapply map_get_eq; eauto using zip_get, map_get_1.
    simpl; cases; eauto. eauto. exfalso. apply NOTCOND; rewrite dvEq; eauto.
  - inv_get.
    assert (Incl:(of_list (fst Zs)) ⊆ (list_union ((fun Zs : params * stmt => of_list (fst Zs) ∪ definedVars (snd Zs)) ⊝ F))). {
      eapply incl_list_union; eauto using map_get_1.
    }
    exploit (IH k Zs); eauto using restrict_ifFstR; [ eauto with len | eauto with len |].
    dcr.
    edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
    eauto with len. inv_get.
    PIR2_inv; inv_get.
    exploit IHCC; try eapply H4; eauto.
    eapply get_app_cases in H3. destruct H3; dcr; inv_get.
    + do 3 eexists; split; [| split; [|split] ]; eauto.
      eapply map_get_eq. eauto. simpl. cases; eauto.
      split; eauto.
      rewrite <- H5. rewrite <- H14. eauto.
    + do 2 eexists; eexists x5; split; [| split ]; eauto.
      assert (Len4:❬Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F)❭ = ❬F❭) by eauto with len.
      rewrite get_app_ge in H1; eauto with len.
      rewrite get_app_ge in H4. len_simpl. inv_get.
      split.
      * eapply map_get_eq; eauto. simpl; cases; eauto.
      * split; eauto.
        rewrite <- H5, H9. eauto.
      * len_simpl. omega.
      * len_simpl. omega.
Qed.

Lemma srd_globals_live b s ZL Lv DL alv f
  (LS:live_sound Imperative ZL Lv s alv)
  (SRD:srd DL s alv)
  (PE:PIR2 (ifFstR Equal) DL (Lv \\ ZL))
  (IC:isCalled b s f)
  (Len1:❬ZL❭=❬Lv❭) (Len2:❬ZL❭=❬DL❭)
  : exists lv Z, get ZL (counted f) Z
            /\ get DL (counted f) (Some lv)
            /\ lv ⊆ getAnn alv.
Proof.
  revert_except s.
  sind s.
  intros.
  invt live_sound; invt srd; invt isCalled; simpl in * |- *.
  - edestruct (IH s0) as [lv' [Z' ?]]; eauto using restrict_ifFstR; dcr.
    inv_get.
    do 2 eexists; split; [| split]. eauto. eauto.
    idtac "improve". rewrite H3. eauto with cset.
  - edestruct (IH s1); eauto; dcr; inv_get. eauto with cset.
  - edestruct (IH s2); eauto; dcr; inv_get. eauto with cset.
  - PIR2_inv. inv_get.
    do 2 eexists; split; [| split]; eauto with cset.
    idtac "improve"; rewrite H7; eauto.
  - assert (PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                 ((getAnn ⊝ als) \\ (fst ⊝ F) ++ Lv \\ ZL)). {
      eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
    }
    edestruct (IH t); eauto with len. rewrite zip_app; eauto with len.
    destruct l'; simpl in *; dcr; inv_get.
    edestruct PIR2_nth; eauto; dcr. invc H13.
    edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
    eauto with len.
    rewrite <- zip_app in H9; eauto with len. inv_get.
    exploit srd_globals_live_F; eauto using restrict_ifFstR.
    intros; eapply (IH (snd Zs)); eauto.
    rewrite zip_app; eauto with len.
    dcr; destruct f; simpl in *; inv_get.
    do 2 eexists; split; [|split]; eauto.
    rewrite <- H3, <- H14, H15, H18. eauto.
Qed.


Lemma srd_globals_live_From b ZL Lv DL s F als f alv
      (ICF:isCalledFrom (isCalled b) F s f)
      (LS:live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) s alv)
      (SRD:srd ((Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)) s alv)
      (Len1 : ❬F❭ = ❬als❭)
      (Len2 : ❬ZL❭ = ❬Lv❭)
      (Len3 : ❬ZL❭ = ❬DL❭)
      (LSF: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          live_sound Imperative (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv) (snd Zs) a)
      (SRDF: forall (n : nat) (Zs : params * stmt) (a : ann ⦃var⦄),
          get F n Zs ->
          get als n a ->
          srd (restr (getAnn a \ of_list (fst Zs)) ⊝ (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL))
              (snd Zs) a)
      (PE:PIR2 (ifFstR Equal) DL (Lv \\ ZL))

  : exists (lv : ⦃var⦄) (Z : params),
    get (fst ⊝ F ++ ZL) (labN f) Z /\
    get (getAnn ⊝ als ++ Lv) (labN f) lv
    /\ (lv \ of_list Z) ⊆ getAnn alv.
Proof.
  destruct ICF as [? [IC CC]]; dcr.
  assert (PE':PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))). {
    rewrite zip_app; eauto with len.
    eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
  }
  exploit srd_globals_live; eauto using restrict_ifFstR with len.
  dcr.
  setoid_rewrite <- H3. inv_get.
  simpl in *.
  edestruct (@get_length_eq _ _ (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ Lv)); eauto.
  eauto with len.
  PIR2_inv; inv_get.
  exploit srd_globals_live_F; eauto using get_app_right, srd_globals_live.
  dcr. do 2 eexists; split; [|split]; eauto.
  rewrite H10, H5; eauto.
Qed.

(** *** On a coherent program a liveness analysis which is sound imperatively is also sound functionally. *)

Local Hint Extern 1 =>
match goal with
| [ |- context [ (?A ++ ?B) \\ (?C ++ ?D) ] ] =>
  rewrite (zip_app _ A C B D);
    [| eauto with len]
| [ |- context [ restr ?G ⊝ (?A ++ ?B) ] ] =>
  rewrite (@List.map_app _ _ (restr G) A B)
end.

Lemma srd_live_functional b s ZL Lv DL alv  (Len2 : ❬ZL❭ = ❬Lv❭) (Len3 : ❬ZL❭ = ❬DL❭)
: live_sound Imperative ZL Lv s alv
  -> srd DL s alv
  -> PIR2 (ifFstR Equal) DL (Lv \\ ZL)
  -> noUnreachableCode (isCalled b) s
  -> live_sound FunctionalAndImperative ZL Lv s alv.
Proof.
  intros LS SRD PE NUC.
  general induction SRD;
    invt live_sound; invt noUnreachableCode; simpl in * |- *;
      eauto using live_sound, restrict_ifFstR.
  - assert(PIR2 (ifFstR Equal) (Some ⊝ (getAnn ⊝ als) \\ (fst ⊝ F) ++ DL)
                ((getAnn ⊝ als ++ Lv) \\ (fst ⊝ F ++ ZL))). {
      eauto using PIR2_app, PIR2_ifFstR_refl.
    }
    econstructor; eauto.
    + eapply IHSRD; eauto with len.
    + intros.
      eapply H1; eauto 10 using restrict_ifFstR with len.
    + intros. exploit H12; eauto; dcr.
      simpl; split; eauto.
      exploit H6; eauto using get_range.
      len_simpl.
      edestruct srd_globals_live_From as [lv' [Z' ?]]; eauto; dcr.
      inv_get.
      rewrite <- H13, <- H20. eauto.
Qed.
