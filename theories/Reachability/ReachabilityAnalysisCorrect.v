Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR.
Require Import Val Var Env IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForward FiniteFixpointIteration.
Require Import Reachability ReachabilityAnalysis Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} ftransform ZL st ST d a.

(* Coq can't figure out the instantiation (fun _ => bool) via unification,
   so we have to add this specialized lemma *)
Lemma forward_length_ass_UC
      (sT : stmt)
      (f : forall sT0 : stmt,
          〔params〕 ->
          forall s : stmt, subTerm s sT0 -> bool -> anni bool)
      (s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
      k d (a : ann bool)
  : ❬ZL❭ = k -> ❬snd (forward f ZL s ST d a)❭ = k.
  eapply (@forward_length_ass _ (fun _ => bool)).
Qed.

Hint Resolve forward_length_ass_UC.

Opaque poLe.



Definition reachability_sound sT ZL BL s d a (ST:subTerm s sT)
  : poEq (fst (forward reachability_transform ZL s ST d a)) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length BL)
    -> poLe (snd (@forward sT _ _ _ reachability_transform ZL s ST d a)) BL
    -> reachability Sound BL s a.
Proof.
  intros EQ Ann DefZL DefBL.
  general induction Ann; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - inv EQ.
    pose proof (ann_R_get H7); simpl in *.
    econstructor; eauto.
    simpl_forward_setTopAnn; eauto.
  - assert (forall d d', ❬snd (forward reachability_transform ZL s (subTerm_EQ_If1 eq_refl ST) d sa)❭ =
            ❬snd (forward reachability_transform ZL t (subTerm_EQ_If2 eq_refl ST) d' ta)❭). {
      eauto with len.
    }
    repeat cases in EQ; simpl in *; try solve [congruence]; inv EQ;
    repeat simpl_forward_setTopAnn;
    econstructor; intros; try solve [congruence];
      eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right; simpl; eauto.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H3; eauto.
    Transparent poLe. hnf in H.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto. inv EQ. eauto.
  - econstructor.
  - invc EQ. simpl_forward_setTopAnn.
    revert H2 H16 H16 H15.
    set (FWt:=(forward reachability_transform (fst ⊝ s ++ ZL) t
                       (subTerm_EQ_Fun1 eq_refl ST) (getAnn ta) ta)).
    set (FWF:=forwardF (forward reachability_transform) (fst ⊝ s ++ ZL) s sa
                       (subTerm_EQ_Fun2 eq_refl ST)).
    intros.
    econstructor; eauto.
    + eapply IHAnn; eauto.
      erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
      * eapply PIR2_get. intros. inv_get.
        edestruct (get_forwardF (fun _ => bool) (forward reachability_transform)
                                (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H11 H8).
        edestruct (@get_union_union_b bool _ _).
        eapply H4.
        Focus 2. dcr.
        exploit H15. eapply zip_get. eapply map_get_1; eauto.
        eapply H12. eauto. eapply ann_R_get in H3. rewrite <- H3.
        rewrite getAnn_setTopAnn. eauto.
        intros. inv_get.
        edestruct (@forwardF_get _ _ _ _ _ _ _ _ _ _ _ H3). dcr. subst.
        eauto with len.
        rewrite Take.take_length_le. eauto with len.
        repeat rewrite (@forward_length sT (fun _ => bool)); eauto with len.
      * etransitivity; eauto. eapply PIR2_drop.
        eapply PIR2_fold_zip_join_inv. reflexivity.
        intros.
        inv_get.
        edestruct (@forwardF_get _ _ _ _ _ _ _ _ _ _ _ H4). dcr.
        subst; repeat rewrite (@forward_length sT (fun _ => bool)); eauto with len.
    + intros.
      assert (n < ❬snd FWt❭). {
        subst FWt.
        repeat rewrite (@forward_length sT (fun _ => bool)). rewrite app_length. rewrite map_length.
        eapply get_range in H8. omega.
      }
      edestruct get_in_range; eauto.
      edestruct (get_forwardF (fun _ => bool) (forward reachability_transform)
                              (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H4 H8).
      eapply H1 with (ST:=x0); eauto.
      eapply H15; eauto.
      *
        assert (n <
                ❬snd (
             forward reachability_transform (fst ⊝ s ++ ZL) (snd Zs) x0 (getAnn a) a)❭). {
          erewrite (@forward_length sT (fun _ => bool)). rewrite app_length,map_length.
          eapply get_range in H8. omega.
        }
        edestruct get_in_range; eauto.
        exploit (@get_union_union_A bool _ _).
        eapply map_get_1. apply g0. instantiate (3:=snd). eauto.
        Focus 2.
        destruct H12; dcr.
        eapply zip_get_eq. eapply map_get_1. eauto.  eauto.
        exploit H15.
        eapply zip_get.
        eapply map_get_1. eauto. eapply H13. eauto.
        exploit (setTopAnn_inv _ _ H12); eauto; subst.
        rewrite setTopAnn_eta; eauto.
        eapply (@forward_getAnn' sT (fun _ => bool)).

        clear_all. intros. inv_get.
        subst FWt.
        repeat erewrite (@forward_length sT (fun _ => bool)); eauto with len.
      * rewrite (take_eta ❬sa❭) at 1.
        eapply PIR2_app.
        protect g0.
        eapply PIR2_get; intros; inv_get.
        exploit (@get_union_union_A bool _ _).
        eapply map_get_1. apply g0. instantiate (3:=snd). eauto.
        Focus 2. dcr.
        edestruct (get_forwardF (fun _ => bool) (forward reachability_transform)
                                (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H17 H12).
        exploit H15; eauto.
        eapply zip_get. eapply map_get_1. subst FWF. eauto. eauto.
        eapply ann_R_get in H3. rewrite getAnn_setTopAnn in H3. rewrite <- H3.
        eauto.
        clear_all. intros. inv_get.
        subst FWt. eauto with len.
        rewrite Take.take_length_le; eauto with len.
        rewrite (@forward_length _ (fun _ => bool)). eauto with len.
        etransitivity; eauto.
        rewrite H. eapply PIR2_drop.
        subst FWF.
        pose proof (@PIR2_fold_zip_join_left bool _ _). eapply H11.
        eauto. reflexivity.
        clear_all. intros. inv_get.
        subst FWt. eauto with len.
    + simpl; eauto.
    + simpl; eauto.
Qed.

Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a b c
  : reachability Complete BL s a
    -> poLe (getAnn a) c
    -> get (snd (forward reachability_transform ZL s ST c a)) n b
    -> poLe b c.
Proof.
  revert ZL BL ST n a b c.
  sind s; intros; destruct s; destruct a; invt reachability;
    simpl in *; repeat let_case_eq; repeat simpl_pair_eqs; simpl in *;
      inv_get;
      try solve [ destruct a; simpl; eauto | destruct a1; simpl; eauto ].
  - eapply IH in H1; eauto.
  - cases in H6; cases in H1; try congruence.
    + specialize (H10 NOTCOND). specialize (H13 COND).
      eapply IH in H1; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H6; simpl in *; eauto.
      rewrite H13; eauto.
    + specialize (H9 NOTCOND). specialize (H14 COND).
      eapply IH in H6; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H1; simpl in *; eauto.
      rewrite H14; eauto.
    + specialize (H9 NOTCOND). specialize (H10 NOTCOND0).
      eapply IH in H1; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H6; simpl in *; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
      reflexivity.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get. destruct a; simpl; eauto.
  - destruct b; [| destruct c; simpl; eauto].
    eapply fold_left_zip_orb_inv in H1. destruct H1.
    + eapply IH in H1; eauto.
    + dcr. inv_get.
      eapply IH in H4; eauto.
      exploit H13; eauto. etransitivity; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Lemma reachability_analysis_complete_setTopAnn BL s a b
      (LE:poLe (getAnn a) b)
  : reachability Complete BL s a
    -> reachability Complete BL s (setTopAnn a b).
Proof.
  intros RCH; general induction RCH; simpl in *;
    eauto using reachability.
  - econstructor; intros; eauto.
    + specialize (H H3). eauto.
    + specialize (H0 H3). eauto.
  - econstructor; simpl; intros; eauto.
    exploit H4; eauto.
Qed.

Lemma fold_left_forward_mono sT F t ZL als als' alt alt' b b'
      (STF:forall n s, get F n s -> subTerm (snd s) sT)
      (ST:subTerm t sT)
  : length F = length als
    -> annotation t alt
    -> (forall n Zs a, get F n Zs -> get als n a -> annotation (snd Zs) a)
    -> poLe als als'
    -> poLe alt alt'
    -> poLe b b'
    -> poLe (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform)
                 (fst ⊝ F ++ ZL) F als STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST
                          b alt)))
         (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform)
                 (fst ⊝ F ++ ZL) F als' STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST
                          b' alt'))).
Proof.
  intros LEN Ant AnF LE1 LE2 LE3.
  eapply fold_left_mono.
  - eapply PIR2_get; intros; inv_get.
    + eapply (@forward_monotone sT (fun _ => bool) _ _ reachability_transform ); eauto.
      eapply reachability_transform_monotone; eauto.
      eapply ann_R_get.
      eapply get_PIR2; eauto.
      eapply get_PIR2; eauto.
    + rewrite !map_length.
      rewrite !(@forwardF_length _ (fun _ => bool)).
      rewrite (PIR2_length LE1). reflexivity.
  - exploit (@forward_monotone sT (fun _ => bool) _ _ reachability_transform );
      try eapply H; eauto.
    eapply reachability_transform_monotone.
Qed.


Local Hint Extern 0 =>
match goal with
| [ H : op2bool ?e <> Some ?t , H' : op2bool ?e <> Some ?t -> _ |- _ ] =>
  specialize (H' H); subst
| [ H : op2bool ?e = Some true , H' : op2bool ?e <> Some false -> _ |- _ ] =>
  let H'' := fresh "H" in
  assert (H'':op2bool e <> Some false) by congruence;
    specialize (H' H''); subst
end.

Lemma reachability_analysis_complete_isCalled sT ZL BL s a b
      (ST:subTerm s sT)
  : reachability Complete BL s a
    -> forall n, get (snd (forward reachability_transform ZL s ST b a)) n true
           -> poLe (getAnn a) b
           -> trueIsCalled s (LabI n).
Proof.
  intros.
  general induction H; simpl in *;
    repeat let_case_eq; repeat simpl_pair_eqs; subst;
      simpl in *; eauto using trueIsCalled.
  - inv_get.
    cases in H7; cases in H5; try congruence;
      destruct x,x0;
      try solve [
            inv EQ
          | eapply TrueIsCalledIf2;
            [ eapply IHreachability2; eauto
            | congruence ]
          | eapply TrueIsCalledIf1;
            [ eapply IHreachability1; eauto
            | congruence ]
          ].
    + eapply H3 in COND.
      eapply forward_snd_poLe in H7; eauto. inv H7.
      rewrite COND; eauto.
    + eapply H4 in COND.
      eapply forward_snd_poLe in H5; eauto. inv H5.
      rewrite COND; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
      destruct l; simpl. econstructor.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get.
  - exfalso. inv_get.
  - inv_get. rename H6 into Get.
    eapply fold_left_zip_orb_inv in Get.
    destruct Get as [Get|[? [? [GetFwd Get]]]]; dcr.
    + exploit forward_snd_poLe; try eapply Get; eauto.
      etransitivity; eauto.
      exploit IHreachability; eauto.
      eapply TrueIsCalledLet; eauto.
      econstructor 1.
    + inv_get.
      exploit H2; eauto.
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.

Lemma reachability_sTA_inv (BL : 〔bool〕)
         (s : stmt) (a : ann bool)
  : reachability Complete BL s (setTopAnn a (getAnn a)) ->
    reachability Complete BL s a.
Proof.
  intros. rewrite setTopAnn_eta in H; eauto.
Qed.

Lemma reachability_analysis_complete sT ZL BL BL' (Len:❬BL❭ = ❬BL'❭) s a (ST:subTerm s sT) b b' c
      (LDEF:labelsDefined s (length ZL))
      (EQ:(fst (forward reachability_transform ZL s ST b a)) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe (getAnn c) b')
  : reachability Complete BL s a
    -> reachability Complete BL' s (setTopAnn c b').
Proof.
  subst c.
  intros RCH.
  general induction RCH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; inv LE;
    eauto using reachability, subTerm, reachability_sTA_inv,
    ann_R_setTopAnn_left.
  - econstructor. eapply reachability_sTA_inv.
    eapply IHRCH; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)). eauto.
  - econstructor; intros; cases; simpl; eauto using reachability_sTA_inv, ann_R_setTopAnn_left.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
  - inv_get. econstructor; eauto.
  - econstructor; simpl; eauto using reachability_sTA_inv, ann_R_setTopAnn_left.
    + eapply reachability_sTA_inv. eapply IHRCH; eauto.
      rewrite !app_length, !map_length.
      rewrite H14. eauto.
      rewrite setTopAnn_eta; eauto.
    + eauto with len.
    + intros. inv_get.
      rewrite <- (setTopAnn_eta x4 eq_refl).
      edestruct (@get_forwardF sT (fun _ => bool)); eauto.
      exploit H15. eauto.
      eapply zip_get_eq. eauto. eauto. reflexivity.
      eapply H2. eauto. rewrite setTopAnn_eta. eauto.
      eauto.
      rewrite !app_length, !map_length.
      rewrite H14. eauto.
      eauto.
      etransitivity; eauto.
      rewrite (setTopAnn_eta _ eq_refl). eauto.
      pose proof (@poLe_setTopAnn bool _ x0 x0).
      eapply H10; eauto. assert (x = x6) by eapply subTerm_PI.
      subst. rewrite setTopAnn_eta. reflexivity. eauto.
      eapply ann_R_get in H8. rewrite getAnn_setTopAnn in H8.
      eauto.
    + intros. inv_get.
      rewrite getAnn_setTopAnn in H6.
      destruct x0; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply reachability_analysis_complete_isCalled in H5; eauto.
        econstructor; split; eauto. econstructor 1.
        eapply ann_R_get in H16.
        rewrite (@forward_getAnn' _ (fun _ => bool)) in H16. eauto.
      * dcr. inv_get.
        exploit forward_snd_poLe; try eapply H11; eauto.
        eapply reachability_analysis_complete_isCalled in H11; eauto.
        exploit H3; eauto.
        eapply isCalledFrom_extend; eauto.
    + intros. inv_get. rewrite getAnn_setTopAnn.
      exploit H4; eauto. destruct x0; simpl; eauto.
      destruct b0; eauto.
      destruct b'; invc LEb; eauto.
      destruct b; invc H12; eauto.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply forward_snd_poLe in H5; eauto.
      * dcr. inv_get.
        eapply forward_snd_poLe in H11; eauto.
        exploit H4; eauto. destruct (getAnn x8); isabsurd.
Qed.

Lemma reachability_complete_bottom BL s
  : labelsDefined s ❬BL❭
    -> reachability Complete BL s (setAnn bottom s).
Proof.
  revert BL.
  sind s; intros; destruct s; invt labelsDefined; simpl; eauto 10 using reachability.
  - econstructor; simpl; eauto.
  - edestruct get_in_range; eauto.
    econstructor; simpl; eauto.
  - econstructor; simpl; eauto with len.
    + intros; inv_get; eauto.
      eapply IH; eauto. rewrite app_length, !map_length. eauto.
    + intros; inv_get; eauto.
      unfold comp in H1. rewrite getAnn_setAnn in H1. intuition.
    + intros; inv_get; eauto.
      unfold comp. eauto.
Qed.

Lemma reachability_complete s
  : labelsDefined s ❬nil:list params❭
    -> reachability Complete nil s (reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - eapply reachability_complete_bottom; eauto.
  - intros.
    eapply reachability_sTA_inv.
    eapply (@reachability_analysis_complete s nil); eauto.
    reflexivity.
    erewrite (setTopAnn_eta _ eq_refl); eauto.
Qed.

Lemma correct s
  : labelsDefined s 0
    -> reachability SoundAndComplete nil s (reachabilityAnalysis s).
Proof.
  intros.
  eapply reachability_sound_and_complete.
  - eapply reachability_complete; eauto.
  - unfold reachabilityAnalysis.
    destr_sig. destr_sig. dcr.
    eapply (@reachability_sound s nil); simpl; eauto.
    + simpl in *. simpl_forward_setTopAnn.
    + assert (❬snd (forward reachability_transform nil s (subTerm_refl s) true x)❭ = 0).
      rewrite (@forward_length _ (fun _ => bool)); eauto.
      destruct (snd (forward reachability_transform nil s (subTerm_refl s) true x)); isabsurd.
      eauto using PIR2.
Qed.

Lemma reachabilityAnalysis_getAnn s
  : getAnn (ReachabilityAnalysis.reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis.
  destr_sig. destruct e as [n [H1 H2]]. subst x.
  simpl in *; simpl_forward_setTopAnn; destr_sig; simpl in *.
  rewrite H. eauto.
Qed.