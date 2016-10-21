Require Import Util IL InRel RenamedApart LabelsDefined OptionR.
Require Import Annotation Exp SetOperations Liveness Restrict.

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


(*
(** *** In a coherent program, the globals of every function that can eventually be called are live *)

Lemma srd_globals_live s ZL Lv DL alv f
: live_sound Imperative ZL Lv s alv
  -> srd DL s alv
  -> PIR2 (ifFstR Equal) DL (Lv \\ ZL)
  -> isCalled s f
  -> exists lv Z, get ZL (counted f) Z
            /\ get DL (counted f) (Some lv)
            /\ lv ⊆ getAnn alv.
Proof.
  intros LS SRD PE IC.
  general induction IC; try invt live_sound; try invt srd; simpl in * |- *.
  - edestruct IHIC as [lv' [Z' ?]]; eauto using restrict_ifFstR; dcr.
    inv_get.
    do 2 eexists; split; [| split]. eauto. eauto.

    idtac "improve". rewrite H. eauto with cset.
  - edestruct IHIC; eauto; dcr; inv_get. eauto with cset.
  - edestruct IHIC; eauto; dcr; inv_get. eauto with cset.
  - PIR2_inv. inv_get.
    do 2 eexists; split; [| split]; eauto with cset.
    idtac "improve"; rewrite H5; eauto.
  - edestruct IHIC; eauto using restrict_ifFstR; dcr; inv_get.
    do 2 eexists; split; [| split]; eauto.
    rewrite H. eauto with cset.
  - inv_get.
    edestruct IHIC2; eauto.
    rewrite zip_app; eauto with len.
    eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
    dcr; inv_get.
    edestruct IHIC1; eauto. econstructor. eauto. eauto. eauto.
    eauto. reflexivity.
    econstructor. eauto. eauto. exploit H12; eauto. eapply srd_monotone. eapply H1.
    (*todo*). simpl in *. dcr.
    do 2 eexists; split; [|split]; eauto.
    PIR2_inv. inv_get. exploit H7; eauto; dcr.
    (*todo*).
  - edestruct IHIC; eauto. rewrite zip_app; eauto with len.
    eapply PIR2_app; eauto using restrict_ifFstR, PIR2_ifFstR_refl.
    destruct l; simpl in *; dcr; inv_get.
    eauto with cset.
(*todo*).


(** *** On a coherent program a liveness analysis which is sound imperatively is also sound functionally. *)

Local Hint Extern 1 =>
match goal with
| [ |- context [ (?A ++ ?B) \\ (?C ++ ?D) ] ] =>
  rewrite (zip_app _ A C B D);
    [| eauto with len]
| [ |- context [ restr ?G ⊝ (?A ++ ?B) ] ] =>
  rewrite (@List.map_app _ _ (restr G) A B)
end.

Lemma srd_live_functional s ZL Lv DL alv
: live_sound Imperative ZL Lv s alv
  -> srd DL s alv
  -> PIR2 (ifFstR Equal) DL (Lv \\ ZL)
  -> noUnreachableCode s
  -> live_sound FunctionalAndImperative ZL Lv s alv.
Proof.
  intros LS SRD PE NUC.
  general induction SRD;
    invt live_sound; invt noUnreachableCode; simpl in * |- *;
      eauto using live_sound, restrict_ifFstR.
  - econstructor; eauto.
    + eapply IHSRD; eauto using PIR2_app, restrict_ifFstR, PIR2_ifFstR_refl.
    + intros.
      eapply H1; eauto 10 using PIR2_app, restrict_ifFstR, PIR2_ifFstR_refl.
    + intros. exploit H12; eauto; dcr.
      simpl; split; eauto.
      edestruct srd_globals_live as [lv' [Z' ?]];
        eauto using PIR2_app, restrict_eqReq, PIR2_ifFstR_refl with len.
      dcr. simpl in *. inv_get.
      unfold lminus in H17. rewrite H17; eauto.
Qed.
*)