Require Import Util IL RenamedApart LabelsDefined OptionR.
Require Import Annotation Exp SetOperations Liveness.Liveness Restrict Coherence.

Set Implicit Arguments.

(** *** Every renamed apart program is coherent *)
(** Note that this lemma also builds the liveness annotation:
    It exploits that we can always claim more variables live *)

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
    erewrite bounded_restrict_eq; simpl; eauto.
    rewrite getAnn_mapAnn. pe_rewrite. clear - H; cset_tac.
  - econstructor; eauto.
  - econstructor.
  - edestruct get_in_range as [a ?]; eauto using map_get_1, srd.
  - econstructor; eauto with len.
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
