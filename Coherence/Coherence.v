Require Import Util IL InRel RenamedApart LabelsDefined.
Require Import Annotation Liveness Restrict MoreExp SetOperations.
Require Import Bisim BisimTactics.

Set Implicit Arguments.

(** * Definition of Coherence: [srd] *)

Notation "'oglobals' F alF" := (List.map Some ((getAnn ⊝ alF) \\ (fst ⊝ F))) (at level 50, F, alF at level 0).

Inductive srd : list (option (set var)) -> stmt -> ann (set var) -> Prop :=
| srdExp DL x e s lv al
  : srd (restrict DL (lv \ singleton x)) s al
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
| srdExtern DL x f Y s lv al
  : srd (restrict DL (lv \ singleton x)) s al
    -> srd DL (stmtExtern x f Y s) (ann1 lv al)
| srdLet DL F t lv als alt
  : length F = length als
    -> (forall n Zs a, get F n Zs -> get als n a ->
                 srd (restrict (oglobals F als ++ DL)
                               (getAnn a \ of_list (fst Zs))) (snd Zs) a)
    -> srd (oglobals F als ++ DL) t alt
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
  - econstructor. eapply IHsrd; eauto.
    eapply restrict_subset; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite restrict_app.
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
  - econstructor. eapply IHsrd, restrict_subset2; eauto.
  - econstructor; eauto.
    + intros. eapply H1; eauto.
      repeat rewrite restrict_app.
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

Lemma inv_oglobals (F:〔params*stmt〕) als k lv
: length F = length als
  -> get (oglobals F als) k ⎣lv⎦
  -> exists Zs a, get F k Zs /\ get als k a /\ lv = getAnn a \ of_list (fst Zs).
Proof.
  intros. length_equify.
  general induction H; isabsurd.
  - inv H0.
    + eexists; eauto using get.
    + edestruct IHlength_eq as [? []]; eauto; dcr; subst.
      do 2 eexists; eauto using get.
Qed.

Lemma inv_globals (F:〔params*stmt〕) als k lv
: length F = length als
  -> get ((getAnn ⊝ als) \\ (fst ⊝ F)) k lv
  -> exists Zs a, get F k Zs /\ get als k a /\ lv = getAnn a \ of_list (fst Zs).
Proof.
  intros. length_equify.
  general induction H; isabsurd.
  - inv H0.
    + eexists; eauto using get.
    + edestruct IHlength_eq as [? []]; eauto; dcr; subst.
      do 2 eexists; eauto using get.
Qed.

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
    eapply srd_monotone.
    eapply IHrenamedApart; eauto with cset.
    erewrite bounded_restrict_eq; simpl; eauto. eauto with cset.
  - econstructor; eauto.
    + intros. inv_map H10.
      exploit H1; eauto.
      * instantiate (1:=(getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL).
        rewrite app_length. rewrite zip_length2; eauto with len.
        repeat rewrite map_length. rewrite <- H. eauto.
      * edestruct H2; eauto; dcr.
        rewrite List.map_app. eapply bounded_app; split; eauto.
        rewrite H14. eapply get_bounded.
        intros. inv_map H15. eapply inv_globals in H17.
        destruct H17; dcr; subst.
        inv_map H20. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H22.
        revert H26; clear_all; cset_tac; intuition.
        eauto with len.
        rewrite H14. rewrite <- incl_right; eauto.
      * eapply srd_monotone. eapply H14.
        rewrite getAnn_mapAnn; simpl.
        repeat rewrite restrict_app. rewrite List.map_app.
        eapply PIR2_app.
        erewrite bounded_restrict_eq. reflexivity.
        reflexivity.
        eapply get_bounded.
        intros. eapply inv_oglobals in H15.
        destruct H15; dcr; subst.
        inv_map H16. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H18.
        decide (n=n0); subst. repeat get_functional.
        rewrite H18. clear_all; cset_tac; intuition.
        exploit H3; eauto. eapply zip_get; eauto. eapply zip_get; eauto.
        unfold defVars in H19. simpl in *.
        edestruct H2; try eapply H12; eauto. dcr. rewrite H21.
        revert H22 H27; clear_all; cset_tac; intuition; eauto.
        eauto with len.
        erewrite bounded_restrict_eq; simpl; eauto.
        edestruct H2; eauto; dcr.
        rewrite H15. revert H19; clear_all; cset_tac; intuition; eauto.
    + eapply srd_monotone.
      eapply (IHrenamedApart ((getAnn ⊝ (mapAnn fst ⊝ ans)) \\ (fst ⊝ F) ++ DL)); eauto.
      * rewrite app_length, zip_length2, map_length, map_length, <- H; eauto with len.
      * pe_rewrite. rewrite List.map_app. rewrite bounded_app. split; eauto.
        eapply get_bounded.
        intros. inv_map H9. eapply inv_globals in H10.
        destruct H10; dcr; subst.
        inv_map H12. edestruct H2; eauto; dcr.
        rewrite getAnn_mapAnn. rewrite H15.
        clear_all; cset_tac; intuition. eauto with len.
      * rewrite List.map_app. reflexivity.
Qed.

(** *** In a coherent program, the globals of every function that can eventually be called are live *)

Lemma eqReq_oglobals_liveGlobals (F:〔params*stmt〕) als
: length F = length als
  -> PIR2 eqReq (oglobals F als) (zip pair (getAnn ⊝ als) (fst ⊝ F)).
Proof.
  intros. length_equify. general induction H; simpl; eauto using PIR2.
  - econstructor; eauto.
    econstructor; reflexivity.
Qed.


Lemma srd_globals_live s DL AL alv f
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> isCalled s f
  -> exists lv, get DL (counted f) (Some lv) /\ lv ⊆ getAnn alv.
Proof.
  intros. general induction H0; invt live_sound; invt isCalled; simpl in * |- *.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct IHsrd1; eauto. dcr.
    eexists; split; eauto. rewrite <- H12; eauto.
  - edestruct IHsrd2; eauto. dcr.
    eexists; split; eauto. rewrite <- H13; eauto.
  - eexists; split; eauto.
    edestruct PIR2_nth; eauto; dcr. get_functional; subst.
    inv H5; simpl in *. rewrite H4; eauto.
  - edestruct IHsrd; eauto using restrict_eqReq.
    dcr. edestruct restrict_get; eauto.
    eexists; split; eauto. revert H6; clear_all; cset_tac; intuition; eauto.
    specialize (H6 a); cset_tac; intuition.
  - edestruct get_length_eq; eauto.
    edestruct H1; eauto.
    rewrite restrict_app. eapply PIR2_app; eauto using restrict_eqReq.
    eapply restrict_eqReq; eauto using eqReq_oglobals_liveGlobals.
    dcr. destruct f; simpl in *.
    edestruct IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    simpl in *; dcr.
    rewrite restrict_app in H11.
    assert (length F = length (restrict (oglobals F als) (getAnn x \ of_list (fst Zs)))).
    rewrite restrict_length. eauto with len.
    rewrite H7 in H11. eapply shift_get in H11.
    eapply restrict_get in H11; dcr.
    eexists; split; eauto.
    eapply get_app_lt_1 in H19.
    eapply inv_oglobals in H19. destruct H19; dcr. repeat get_functional; subst.
    rewrite H22, H20; eauto. eauto.
    rewrite map_length, zip_length2, map_length, <- H; eauto with len.
  - edestruct IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    destruct f; simpl in *.
    dcr.
    assert (LEN: length F = length (oglobals F als)) by eauto with len.
    erewrite LEN in H7. eapply shift_get in H7.
    eexists; split; eauto. rewrite H8; eauto.
Qed.

(** *** On a coherent program a liveness analysis which is sound imperatively is also sound functionally. *)

Lemma srd_live_functional s DL AL alv
: live_sound Imperative AL s alv
  -> srd DL s alv
  -> PIR2 eqReq DL AL
  -> noUnreachableCode s
  -> live_sound FunctionalAndImperative AL s alv.
Proof.
  intros. general induction H0; invt live_sound; invt noUnreachableCode; simpl in * |- *;
          eauto using live_sound, restrict_eqReq.
  - econstructor; eauto.
    + eapply IHsrd; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    + intros. eapply H1; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
    + intros. exploit H15; eauto; dcr.
      edestruct srd_globals_live; eauto using PIR2_app, restrict_eqReq, eqReq_oglobals_liveGlobals.
      eapply H10; eauto. eapply get_length; eauto. dcr.
      simpl; split; eauto.
      eapply get_app_lt_1 in H18; simpl.
      eapply inv_oglobals in H18. destruct H18; dcr. simpl in *. repeat get_functional; subst.
      rewrite H19; eauto. eauto.
      rewrite map_length, zip_length2, map_length, <- H; eauto using get_range with len.
Qed.
