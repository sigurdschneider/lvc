Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR.
Require Import Val Var Env IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForward FiniteFixpointIteration.
Require Import UnreachableCodeAnalysis UnreachableCode Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} ftransform ZL st ST a.

(* Coq can't figure out the instantiation (fun _ => bool) via unification,
   so we have to add this specialized lemma *)
Lemma forward_length_ass_UC
      (sT : stmt)
      (f : forall sT0 : stmt,
          〔params〕 ->
          forall s : stmt, subTerm s sT0 -> bool -> anni bool)
      (s : stmt) (ST : subTerm s sT) (ZL : 〔params〕)
      k (a : ann bool)
  : ❬ZL❭ = k -> ❬snd (forward f ZL s ST a)❭ = k.
  eapply (@forward_length_ass _ (fun _ => bool)).
Qed.

Hint Resolve forward_length_ass_UC.

Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : ann_R eq (fst (forward ?unreachable_code_transform ?ZL
                                       ?s ?ST (setTopAnn ?sa ?a))) ?sa |- _ ] =>
           let X := fresh "H" in
           match goal with
           | [ H' : getAnn sa = a |- _ ] => fail 1
           | _ => exploit (forward_getAnn _ _ _ _ _ H) as X
           end
         end; rewrite setTopAnn_eta in *; try eassumption.

Opaque poLe.

Definition ucc_sound sT ZL BL s a (ST:subTerm s sT)
  : poEq (fst (forward unreachable_code_transform ZL s ST a)) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length BL)
    -> paramsMatch s (length ⊝ ZL)
    -> poLe (snd (@forward sT _ _ _ unreachable_code_transform ZL s ST a)) BL
    -> unreachable_code Sound ZL BL s a.
Proof.
  intros EQ Ann DefZL DefBL PM.
  general induction Ann; simpl in *; inv DefZL; inv DefBL; inv PM;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *.
  - inv EQ.
    pose proof (ann_R_get H8); simpl in *.
    econstructor.
    eapply IHAnn; eauto;
      simpl_forward_setTopAnn.
    simpl_forward_setTopAnn.
  - assert (❬snd (forward unreachable_code_transform ZL s (subTerm_EQ_If1 eq_refl ST) sa)❭ =
            ❬snd (forward unreachable_code_transform ZL t (subTerm_EQ_If2 eq_refl ST) ta)❭). {
      eauto with len.
    }
    repeat cases in EQ; simpl in *; try solve [congruence]; inv EQ;
    repeat simpl_forward_setTopAnn;
    econstructor; intros; try solve [congruence];
      eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right.
  - inv_get. Transparent poLe. hnf in H.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; eauto.
  - econstructor.
  - inv EQ.
    pose proof (ann_R_get H8); simpl in *.
    econstructor.
    eapply IHAnn; eauto;
      simpl_forward_setTopAnn.
    simpl_forward_setTopAnn.
  - invc EQ. simpl_forward_setTopAnn.
    revert H2 H16 H17 H18.
    set (FWt:=(forward unreachable_code_transform (fst ⊝ s ++ ZL) t
                       (subTerm_EQ_Fun1 eq_refl ST) ta)).
    set (FWF:=forwardF (forward unreachable_code_transform) (fst ⊝ s ++ ZL) s sa
                       (subTerm_EQ_Fun2 eq_refl ST)).
    intros.
    econstructor; eauto.
    + eapply IHAnn; eauto.
      erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
      * eapply PIR2_get. intros. inv_get.
        edestruct (get_forwardF (fun _ => bool) (forward unreachable_code_transform)
                                (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H13 H10).
        edestruct (@get_union_union_b bool _ _).
        eapply H4.
        Focus 2. dcr.
        exploit H17. eapply zip_get. eapply map_get_1; eauto.
        eapply H14. eauto. eapply ann_R_get in H3. rewrite <- H3.
        rewrite getAnn_setTopAnn. eapply H15.
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
        eapply get_range in H4. omega.
      }
      edestruct get_in_range; eauto.
      edestruct (get_forwardF (fun _ => bool) (forward unreachable_code_transform)
                              (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H4 H10).
      eapply H1 with (ST:=x0); eauto.
      eapply H17; eauto.
      *
        assert (n <
                ❬snd (
             forward unreachable_code_transform (fst ⊝ s ++ ZL) (snd Zs) x0 a0)❭). {
          erewrite (@forward_length sT (fun _ => bool)). rewrite app_length,map_length.
          eapply get_range in H4. omega.
        }
        edestruct get_in_range; eauto.
        exploit (@get_union_union_A bool _ _).
        eapply map_get_1. apply g0. instantiate (3:=snd). eauto.
        Focus 2.
        destruct H15; dcr.
        eapply zip_get_eq. eapply map_get_1. eauto.  eauto.
        exploit H17.
        eapply zip_get.
        eapply map_get_1. eauto. eapply H19. eauto.
        exploit (setTopAnn_inv _ _ H15); eauto; subst.
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
        edestruct (get_forwardF (fun _ => bool) (forward unreachable_code_transform)
                                (fst ⊝ s ++ ZL) (subTerm_EQ_Fun2 eq_refl ST) H20 H15).
        exploit H17; eauto.
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
        pose proof (@PIR2_fold_zip_join_left bool _ _). eapply H13.
        eauto. reflexivity.
        clear_all. intros. inv_get.
        subst FWt. eauto with len.
    + simpl. eauto.
Qed.


Inductive unreachable_code_complete
  : list params -> list bool -> stmt -> ann bool -> Prop :=
| UCPOpr ZL BL x s b e al
  :  unreachable_code_complete ZL BL s al
     -> impb (getAnn al) b
     -> unreachable_code_complete ZL BL (stmtLet x e s) (ann1 b al)
| UCPIf ZL BL e b1 b2 b al1 al2
  :  unreachable_code_complete ZL BL b1 al1
     -> unreachable_code_complete ZL BL b2 al2
     -> impb (getAnn al1) b
     -> impb (getAnn al2) b
     -> (exp2bool e = ⎣ false ⎦ -> getAnn al1 = false)
     -> (exp2bool e = ⎣ true ⎦ -> getAnn al2 = false)
     -> unreachable_code_complete ZL BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto ZL BL l Y a
  : unreachable_code_complete ZL BL (stmtApp l Y) (ann0 a)
| UCReturn ZL BL e b
  : unreachable_code_complete ZL BL (stmtReturn e) (ann0 b)
| UCExtern ZL BL x s b Y al f
  : unreachable_code_complete ZL BL s al
    -> impb (getAnn al) b
    -> unreachable_code_complete ZL BL (stmtExtern x f Y s) (ann1 b al)
| UCLet ZL BL F t b als alt
  : unreachable_code_complete (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code_complete (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (forall n a,
          get als n a ->
          getAnn a ->
          isCalledFrom trueIsCalled F t (LabI n))
        -> (forall n a, get als n a -> impb (getAnn a) b )
    -> impb (getAnn alt) b
-> unreachable_code_complete ZL BL (stmtFun F t) (annF b als alt).

Lemma unreachable_code_complete_annotation ZL BL s a
  : unreachable_code_complete ZL BL s a
    -> annotation s a.
Proof.
  intros. general induction H; eauto using @annotation.
Qed.

Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a b c
  : unreachable_code_complete ZL BL s a
    -> poLe (getAnn a) c
    -> get (snd (forward unreachable_code_transform ZL s ST (setTopAnn a c))) n b
    -> poLe b c.
Proof.
  revert ZL BL ST n a b c.
  sind s; intros; destruct s; destruct a; invt unreachable_code_complete;
    simpl in *; repeat let_case_eq; repeat simpl_pair_eqs; simpl in *;
      inv_get;
      try solve [ destruct a; simpl; eauto | destruct a1; simpl; eauto ].
  - eapply IH in H1; eauto.
  - cases in H6; cases in H1; try congruence.
    + eapply IH in H1; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H6; simpl in *; eauto.
    + eapply IH in H6; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H1; simpl in *; eauto.
    + eapply IH in H1; eauto.
      destruct x, x0, c; simpl in *; eauto.
      eapply IH in H6; simpl in *; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
      reflexivity.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get. destruct a; simpl; eauto.
  - eapply IH in H1; eauto.
  - destruct b; [| destruct c; simpl; eauto].
    eapply fold_left_zip_orb_inv in H1. destruct H1.
    + eapply IH in H1; eauto.
    + dcr. inv_get.
      erewrite <- (@setTopAnn_eta _ x3 (getAnn x3)) in H4; eauto.
      eapply IH in H4; eauto.
      exploit H13; eauto. etransitivity; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Lemma unreachable_code_analysis_complete_setTopAnn ZL BL s a b
      (LE:poLe (getAnn a) b)
  : unreachable_code_complete ZL BL s a
    -> unreachable_code_complete ZL BL s (setTopAnn a b).
Proof.
  intros UCC; general induction UCC; simpl in *;
    eauto using unreachable_code_complete.
  - econstructor; eauto.
    intros; eauto.
    exploit H3; eauto.
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
            (snd ⊝ forwardF (forward unreachable_code_transform)
                 (fst ⊝ F ++ ZL) F als STF)
            (snd (forward unreachable_code_transform (fst ⊝ F ++ ZL)
                          t ST
                          (setTopAnn alt b))))
         (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward unreachable_code_transform)
                 (fst ⊝ F ++ ZL) F als' STF)
            (snd (forward unreachable_code_transform (fst ⊝ F ++ ZL)
                          t ST
                          (setTopAnn alt' b')))).
Proof.
  intros LEN Ant AnF LE1 LE2 LE3.
  eapply fold_left_mono.
  - eapply PIR2_get; intros; inv_get.
    + eapply (@forward_monotone sT (fun _ => bool) _ _ unreachable_code_transform ); eauto.
      eapply unreachable_code_transform_monotone; eauto.
      eapply get_PIR2; eauto.
    + rewrite !map_length.
      rewrite !(@forwardF_length _ (fun _ => bool)).
      rewrite (PIR2_length LE1). reflexivity.
  - assert (poLe (setTopAnn alt b) (setTopAnn alt' b')).
    eapply poLe_setTopAnn; eauto.
    exploit (@forward_monotone sT (fun _ => bool) _ _ unreachable_code_transform );
      try eapply H; eauto using setTopAnn_annotation.
    eapply unreachable_code_transform_monotone.
    eapply H0.
Qed.


Lemma unreachable_code_analysis_complete_isCalled sT ZL BL s a b
      (ST:subTerm s sT)
  : unreachable_code_complete ZL BL s a
    -> forall n, get (snd (forward unreachable_code_transform ZL s ST (setTopAnn a b))) n true
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
            [ eapply IHunreachable_code_complete2; eauto
            | congruence ]
          | eapply TrueIsCalledIf1;
            [ eapply IHunreachable_code_complete1; eauto
            | congruence ]
          ].
    + eapply H3 in COND.
      eapply forward_snd_poLe in H7; eauto. inv H7.
      rewrite COND; eauto.
    + eapply H4 in COND.
      eapply forward_snd_poLe in H5; eauto. inv H5.
      rewrite COND; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H0; eauto; subst.
      destruct l; simpl. econstructor.
    + eapply ListUpdateAt.list_update_at_get_1 in H0; eauto; subst.
      inv_get.
  - exfalso. inv_get.
  - inv_get. rename H6 into Get.
    eapply fold_left_zip_orb_inv in Get.
    destruct Get as [Get|[? [? [GetFwd Get]]]]; dcr.
    + exploit forward_snd_poLe; try eapply Get; eauto.
      etransitivity; eauto.
      exploit IHunreachable_code_complete; eauto.
      eapply TrueIsCalledLet; eauto.
      econstructor 1.
    + inv_get.
      erewrite <- (@setTopAnn_eta _ x3 (getAnn x3)) in Get; eauto.
      exploit H2; eauto.
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.

Lemma ucc_sTA_inv (ZL : 〔params〕) (BL : 〔bool〕)
         (s : stmt) (a : ann bool)
  : unreachable_code_complete ZL BL s (setTopAnn a (getAnn a)) ->
    unreachable_code_complete ZL BL s a.
Proof.
  intros. rewrite setTopAnn_eta in H; eauto.
Qed.

Lemma unreachable_code_analysis_complete sT ZL BL BL' s a (ST:subTerm s sT) b b' c
      (LDEF:labelsDefined s (length ZL))
      (EQ:(fst (forward unreachable_code_transform ZL s ST (setTopAnn a b))) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe (getAnn c) b')
  : unreachable_code_complete ZL BL s a
    -> unreachable_code_complete ZL BL' s (setTopAnn c b').
Proof.
  subst c.
  intros UCC.
  general induction UCC; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; inv LE;
    eauto using unreachable_code_complete, subTerm, ucc_sTA_inv,
    ann_R_setTopAnn_left.
  - econstructor. eapply ucc_sTA_inv.
    eapply IHUCC; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)).
    rewrite getAnn_setTopAnn; eauto.
  - econstructor; intros; cases; eauto using ucc_sTA_inv, ann_R_setTopAnn_left.
    + eapply ucc_sTA_inv. eapply IHUCC1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply ucc_sTA_inv. eapply IHUCC1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply ucc_sTA_inv. eapply IHUCC2; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply ucc_sTA_inv. eapply IHUCC2; eauto.
      rewrite setTopAnn_eta; eauto.
  - econstructor. eapply ucc_sTA_inv.
    eapply IHUCC; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)).
    rewrite getAnn_setTopAnn; eauto.
  - econstructor; eauto using ucc_sTA_inv, ann_R_setTopAnn_left.
    + eapply ucc_sTA_inv. eapply IHUCC; eauto.
      rewrite setTopAnn_eta; eauto.
    + rewrite zip_length, map_length.
      rewrite (@forwardF_length _ (fun _ => bool)).
      rewrite fold_list_length'.
      rewrite (@forward_length _ (fun _ => bool)).
      rewrite app_length, map_length, <- H.
      repeat rewrite min_l; eauto. omega.
      intros; inv_get.
      rewrite (@forward_length _ (fun _ => bool)).
      rewrite (@forward_length _ (fun _ => bool)). reflexivity.
      intros. rewrite zip_length. rewrite min_l; eauto.
    + intros. inv_get.
      rewrite <- (setTopAnn_eta x4 eq_refl).
      edestruct (@get_forwardF sT (fun _ => bool)); eauto.
      exploit H15. eauto.
      eapply zip_get_eq. eauto. eauto. reflexivity.
      eapply H1. eauto. eauto. eauto.
      etransitivity; eauto.
      rewrite (setTopAnn_eta _ eq_refl);
      pose proof (@poLe_setTopAnn bool _ x0 x0).
      eapply H10; eauto. assert (x = x6) by eapply subTerm_PI.
      subst. reflexivity.
      eapply ann_R_get in H8. rewrite getAnn_setTopAnn in H8.
      eauto.
    + intros. inv_get.
      rewrite getAnn_setTopAnn in H6.
      destruct x0; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply unreachable_code_analysis_complete_isCalled in H5; eauto.
        econstructor; split; eauto. econstructor 1.
        eapply ann_R_get in H16.
        rewrite (@forward_getAnn' _ (fun _ => bool)) in H16.
        rewrite getAnn_setTopAnn in H16. eauto.
      * dcr. inv_get.
        rewrite <- (@setTopAnn_eta _ x8 (getAnn x8)) in H11; eauto.
        exploit forward_snd_poLe; try eapply H11; eauto.
        eapply unreachable_code_analysis_complete_isCalled in H11; eauto.
        exploit H2; eauto.
        eapply isCalledFrom_extend; eauto.
    + intros. inv_get. rewrite getAnn_setTopAnn.
      exploit H3; eauto. destruct x0; simpl; eauto.
      destruct b0; eauto.
      destruct b'; invc LEb; eauto.
      destruct b; invc H12; eauto.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply forward_snd_poLe in H5; eauto.
      * dcr. inv_get.
        erewrite <- (@setTopAnn_eta _ x8) in H11; [| reflexivity].
        eapply forward_snd_poLe in H11; eauto.
        exploit H3; eauto. destruct (getAnn x8); isabsurd.
Qed.

Lemma unreachable_code_complete_bottom ZL BL s
  : unreachable_code_complete ZL BL s (setAnn bottom s).
Proof.
  revert ZL BL.
  sind s; intros; destruct s; simpl; eauto 10 using unreachable_code_complete.
  - econstructor; eauto with len.
    + intros; inv_get; eauto.
    + intros; inv_get; eauto.
      unfold comp in H0. rewrite getAnn_setAnn in H0. intuition.
    + intros; inv_get; eauto.
      unfold comp. eauto.
Qed.

Lemma ucc_complete s
  : labelsDefined s ❬nil:list params❭
    -> unreachable_code_complete nil nil s (unreachableCodeAnalysis s).
Proof.
  unfold unreachableCodeAnalysis. destr_sig.
  destruct e as [n [Iter _]].
  subst.
  general induction n.
  - simpl in *. eapply unreachable_code_complete_bottom.
  - rewrite iter_comm.
    eapply ucc_sTA_inv.
    eapply (@unreachable_code_analysis_complete s); eauto.
    + reflexivity.
    + erewrite (setTopAnn_eta _ eq_refl).
      rewrite <- iter_comm.
      eapply (safeFixpoint_chain (unreachable_code_analysis s) n).
Qed.

Lemma ucc_sound_and_complete ZL BL s a
  : unreachable_code_complete ZL BL s a
    -> unreachable_code Sound ZL BL s a
    -> unreachable_code SoundAndComplete ZL BL s a.
Proof.
  intros UCC UCS.
  general induction UCS; inv UCC; eauto using unreachable_code.
Qed.

Lemma correct s
  : labelsDefined s 0
    -> paramsMatch s nil
    -> unreachable_code SoundAndComplete nil nil s (unreachableCodeAnalysis s).
Proof.
  intros.
  eapply ucc_sound_and_complete.
  - eapply ucc_complete; eauto.
  - unfold unreachableCodeAnalysis.
    destr_sig. destr_sig. eauto. dcr.
    eapply ucc_sound; simpl; eauto.
    + simpl in *. simpl_forward_setTopAnn.
    + assert (❬snd (forward unreachable_code_transform nil s (subTerm_refl s) x)❭ = 0).
      rewrite (@forward_length _ (fun _ => bool)); eauto.
      destruct (snd (forward unreachable_code_transform nil s (subTerm_refl s) x)); isabsurd.
      eauto using PIR2.
Qed.

Lemma unreachableCodeAnalysis_getAnn s
  : getAnn (UnreachableCodeAnalysis.unreachableCodeAnalysis s).
Proof.
  unfold unreachableCodeAnalysis.
  destr_sig. destruct e as [n [H1 H2]]. subst x.
  simpl in *; simpl_forward_setTopAnn; destr_sig; simpl in *.
  rewrite H. eauto.
Qed.