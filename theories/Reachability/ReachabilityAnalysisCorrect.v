Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR MoreList.
Require Import Val Var Env IL Annotation AnnotationLattice Infra.Lattice.
Require Import DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForward FiniteFixpointIteration.
Require Import Reachability ReachabilityAnalysis Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} {H1} ftransform ZL st ST a.

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

Lemma forward_getAnn (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT)) s (ST:subTerm s sT) ZL a an
  : poEq (fst (@forward sT Dom _ _ _ f ZL s ST (setTopAnn an a))) an
    -> getAnn an ≣ a.
Proof.
  intros. eapply ann_R_get in H2.
  rewrite forward_getAnn' in H2. rewrite getAnn_setTopAnn in H2.
  symmetry; eauto.
Qed.

Lemma forward_setTopAnn_inv (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fExt:forall (s0 : stmt) (ST0 : subTerm s0 sT) (ZL0 : 〔params〕) (a0 b : Dom sT),
          a0 ≣ b -> f sT ZL0 s0 ST0 a0 ≣ f sT ZL0 s0 ST0 b)
      s (ST:subTerm s sT) ZL a an
  : poEq (fst (@forward sT Dom _ _ _ f ZL s ST (setTopAnn an a))) an
    -> poEq (fst (@forward sT Dom _ _ _ f ZL s ST an)) an /\ getAnn an ≣ a.
Proof.
  intros. split; eauto using forward_getAnn.
  rewrite <- H2 at 2.
  eapply ann_R_get in H2.
  rewrite forward_getAnn' in H2. rewrite getAnn_setTopAnn in H2.
  eapply forward_ext; eauto.
  rewrite setTopAnn_eta_poEq; eauto.
Qed.

Ltac forward_setTopAnn_inv :=
  match goal with
  | [ H: poEq (fst (@forward ?sT ?Dom _ _ _ ?f ?ZL ?s ?ST (setTopAnn ?an ?a))) ?an |- _ ]
    => eapply (@forward_setTopAnn_inv sT Dom _ _ _ f ltac:(eauto)) in H;
      destruct H
  end.

Smpl Add forward_setTopAnn_inv : inv_trivial.

Lemma forward_setTopAnn_inv_snd (sT:stmt) (Dom : stmt -> Type)
      `{JoinSemiLattice (Dom sT)} `{@LowerBounded (Dom sT) H}
      (f: forall sT, list params ->
                forall s, subTerm s sT -> Dom sT -> anni (Dom sT))
      (fExt:forall (s0 : stmt) (ST0 : subTerm s0 sT) (ZL0 : 〔params〕) (a0 b : Dom sT),
          a0 ≣ b -> f sT ZL0 s0 ST0 a0 ≣ f sT ZL0 s0 ST0 b)
      a an (EQ:getAnn an ≣ a)
      s (ST:subTerm s sT) ZL
  : poEq (snd (@forward sT Dom _ _ _ f ZL s ST (setTopAnn an a)))
         (snd (@forward sT Dom _ _ _ f ZL s ST an)).
Proof.
  intros.
  eapply forward_ext; eauto.
  rewrite setTopAnn_eta_poEq; eauto.
Qed.

Ltac forward_setTopAnn_inv_snd :=
  match goal with
  | [ H : context [ snd (@forward ?sT ?Dom ?PO ?JSL ?LB ?f ?ZL ?s ?ST (setTopAnn ?an ?a)) ],
      I : getAnn ?an ≣ ?a |- _ ]
    => rewrite (@forward_setTopAnn_inv_snd sT Dom PO JSL LB f ltac:(eauto) _ _ I s ST ZL) in H
  end.

(* Smpl Add forward_setTopAnn_inv_snd : inv_trivial. *)

Instance zip_join_proper_poEq X `{JoinSemiLattice X}
  : Proper (poEq ==> poEq ==> poEq) (zip join).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_join_zip; eauto.
Qed.

Instance zip_join_proper_poLe' X `{JoinSemiLattice X}
  : Proper (poLe ==> poLe ==> poLe) (zip join).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance drop_proper_poEq X `{PartialOrder X} n
  : Proper (poEq ==> poEq) (drop n).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_drop; eauto.
Qed.

Instance drop_proper_poLe X `{PartialOrder X} n
  : Proper (poLe ==> poLe) (drop n).
Proof.
  unfold Proper, respectful; intros.
  eapply poLe_drop; eauto.
Qed.

Instance fold_left_zip_join_proper_poEq X `{JoinSemiLattice X}
  : Proper (poEq ==> poEq ==> poEq) (fold_left (zip join)).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance fold_left_zip_join_proper_poLe X `{JoinSemiLattice X}
  : Proper (poLe ==> poLe ==> poLe) (fold_left (zip join)).
Proof.
  unfold Proper, respectful; intros.
  eauto.
Qed.

Instance setTopAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (@setTopAnn X).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance setTopAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (@setTopAnn X).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance zip_setTopAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq ==> poEq) (zip (@setTopAnn X)).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance zip_setTopAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe ==> poLe) (zip (@setTopAnn X)).
Proof.
  unfold Proper, respectful; intros. eauto.
Qed.

Instance map_getAnn_proper_poEq X `{PartialOrder X}
  : Proper (poEq ==> poEq) (List.map getAnn).
Proof.
  unfold Proper, respectful; intros.
  eapply poEq_map; eauto.
  intros. rewrite H1; eauto.
Qed.

Instance map_getAnn_proper_poLe X `{PartialOrder X}
  : Proper (poLe ==> poLe) (List.map getAnn).
Proof.
  unfold Proper, respectful; intros.
  eapply poLe_map; eauto.
  intros. rewrite H1; eauto.
Qed.


Lemma setTopAnn_map_inv_poEq X `{PartialOrder X} A B
  : setTopAnn (A:=X) ⊜ A B ≣ A
    -> Take.take ❬A❭ B ≣ getAnn ⊝ A.
Proof.
  intros. general induction A; destruct B; simpl; eauto.
  - exfalso. inv H0.
  - simpl in *. inv H0; inv_cleanup.
    eapply poEq_list_struct; eauto.
    rewrite <- pf. rewrite getAnn_setTopAnn. reflexivity.
Qed.

Definition reachability_sound sT ZL BL s a (ST:subTerm s sT)
  : poEq (fst (forward reachability_transform ZL s ST a)) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length BL)
    -> poLe (snd (@forward sT _ _ _ _ reachability_transform ZL s ST a)) BL
    -> reachability cop2bool Sound BL s a.
Proof.
  intros EQ Ann DefZL DefBL.
  general induction Ann; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      repeat clear_trivial_eqs.
  - forward_setTopAnn_inv_snd.
    econstructor; eauto.
  - repeat forward_setTopAnn_inv_snd.
    econstructor; eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
    + rewrite H3. unfold cop2bool, op2bool. simpl.
      cases; eauto.
      monad_inv COND. rewrite EQ. intros. exfalso; eauto.
    + rewrite H1. unfold cop2bool, op2bool. simpl.
      cases; eauto.
      monad_inv COND. rewrite EQ. intros. exfalso; eauto.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H3; eauto.
    Transparent poLe. hnf in H.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto.
  - econstructor.
  - eapply PIR2_get in H15; eauto; clear H14.
    change (PIR2 poEq) with (@poEq (list (ann bool)) _) in H15.
    repeat forward_setTopAnn_inv_snd.
    set (FWt:=(forward reachability_transform (fst ⊝ s ++ ZL) t
                       (subTerm_EQ_Fun1 eq_refl ST) ta)) in *.
    set (FWF:=forwardF (forward reachability_transform (fst ⊝ s ++ ZL)) s sa
                       (subTerm_EQ_Fun2 eq_refl ST)) in *.
    econstructor; eauto.
    + eapply IHAnn; eauto.
      erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
      * change (PIR2 poLe) with (@poLe (list bool) _).
        rewrite <- H15.
        rewrite getAnn_map_setTopAnn.
        unfold FWF at 1. len_simpl.
        eapply PIR2_take.
        change (PIR2 poLe) with (@poLe (list bool) _).
        eapply PIR2_fold_zip_join_right; try reflexivity.
        unfold FWF; intros; inv_get.
        subst FWt. eauto with len.
      * rewrite <- H2. eapply poLe_drop.
        eapply PIR2_fold_zip_join_right; try reflexivity.
        unfold FWF; intros; inv_get.
        subst FWt. eauto with len.
    + intros.
      assert (n < ❬snd FWt❭). {
        subst FWt. len_simpl.
        eapply get_range in H8. omega.
      }
      edestruct get_in_range; eauto.
      edestruct (get_forwardF (fun _ => bool) (forward reachability_transform (fst ⊝ s ++ ZL))
                              (subTerm_EQ_Fun2 eq_refl ST) H8 H10).
      eapply H1 with (ZL:=(fst ⊝ s ++ ZL)) (ST:=x0); eauto.
      * subst FWt FWF.
        assert (n <
                ❬snd (
                     forward reachability_transform (fst ⊝ s ++ ZL) (snd Zs) x0 a0)❭). {
          erewrite (@forward_length sT (fun _ => bool)). rewrite app_length,map_length.
          eapply get_range in H8. omega.
        }
        edestruct get_in_range; eauto.
        exploit (@get_union_union_A bool _ _).
        eapply map_get_1. apply g0. instantiate (3:=snd). eauto.
        Focus 2.
        destruct H13; dcr.
        eapply PIR2_nth in H15; eauto; dcr.
        Focus 2.
        eapply zip_get_eq. eapply map_get_1. eauto.  eauto. reflexivity.
        exploit (setTopAnn_inv _ _ H18); eauto; subst.
        inv_get. rewrite <- H18 at 2.
        rewrite setTopAnn_eta; eauto.
        eapply (@forward_getAnn' sT (fun _ => bool)).
        clear_all. intros. inv_get.
        len_simpl. eauto with len.
      * rewrite (take_eta ❬sa❭) at 1.
        eapply PIR2_app.
        -- change (PIR2 poLe) with (@poLe (list bool) _).
           rewrite <- H15 at 2.
           rewrite getAnn_map_setTopAnn.
           unfold FWF at 1. len_simpl. rewrite H.
           eapply PIR2_take.
           change (PIR2 poLe) with (@poLe (list bool) _).
           eapply PIR2_fold_zip_join_left; eauto using map_get_1.
           unfold FWF; intros; inv_get.
           subst FWt. eauto with len.
        -- etransitivity; eauto.
           rewrite H. eapply poLe_drop.
           eapply PIR2_fold_zip_join_left; eauto using map_get_1.
           unfold FWF; intros; inv_get.
           subst FWt. eauto with len.
           Grab Existential Variables.
Qed.

Lemma impl_poLe (a b:bool)
  : (a -> b) <-> (poLe a b).
Proof.
  destruct a, b; simpl; firstorder.
Qed.

Lemma orb_poLe_struct a b c
  : a ⊑ c -> b ⊑ c -> a || b ⊑ c.
Proof.
  destruct a, b; simpl; eauto.
Qed.


Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a b c
  : reachability cop2bool Complete BL s a
    -> poLe (getAnn a) c
    -> get (snd (forward reachability_transform ZL s ST (setTopAnn a c))) n b
    -> poLe b c.
Proof.
  revert ZL BL ST n a b c.
  sind s; intros; destruct s; destruct a; invt reachability;
    simpl in *; repeat let_case_eq; repeat simpl_pair_eqs; simpl in *;
      inv_get;
      try solve [ destruct a; simpl; eauto | destruct a1; simpl; eauto ].
  - eapply IH in H1; eauto.
  - cases in H6; cases in H1; clear_trivial_eqs; try congruence.
    + assert (cop2bool e = ⎣ wTA false ⎦). {
        rewrite op2bool_cop2bool in COND; eauto.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA true ⎦). {
        rewrite H2. clear_all. intro. clear_trivial_eqs.
      }
      specialize (H10 ltac:(eauto)).
      eapply IH in H1; eauto.
      eapply orb_poLe_struct; eauto.
      rewrite <- H0. rewrite <- H10.
      eapply IH in H6; simpl in *; eauto; clear_trivial_eqs.
      eauto.
      rewrite H13; eauto. rewrite H2; eauto.
    + assert (cop2bool e = ⎣ wTA true ⎦). {
        rewrite op2bool_cop2bool in COND; eauto.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA false ⎦). {
        rewrite H2. clear_all. intro. clear_trivial_eqs.
      }
      specialize (H9 ltac:(eauto)).
      eapply IH in H6; eauto.
      eapply orb_poLe_struct; eauto.
      eapply IH in H1; simpl in *; eauto.
      rewrite H1; eauto.
      rewrite H14; eauto. rewrite H2; eauto.
    + assert (~ cop2bool e ⊑ ⎣ wTA true ⎦). {
        eauto using op2bool_cop2bool_not_some.
      }
      assert (~ cop2bool e ⊑ ⎣ wTA false ⎦). {
        eauto using op2bool_cop2bool_not_some.
      }
      specialize (H9 ltac:(eauto)).
      specialize (H10 ltac:(eauto)).
      eapply IH in H1; eauto.
      eapply IH in H6; simpl in *; eauto.
      eapply orb_poLe_struct; eauto.
  - decide (labN l = n); subst.
    + eapply ListUpdateAt.list_update_at_get_2 in H1; eauto; subst.
    + eapply ListUpdateAt.list_update_at_get_1 in H1; eauto; subst.
      inv_get. eauto.
  - destruct b; [| destruct c; simpl; eauto].
    eapply fold_left_zip_orb_inv in H1. destruct H1.
    + eapply IH in H1; eauto.
    + dcr. inv_get.
      rewrite <- (setTopAnn_eta x3 eq_refl) in H4.
      eapply IH in H4; eauto.
      exploit H13; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Transparent poLe.

Lemma fold_left_forward_mono sT F t ZL als als' alt alt'
      (STF:forall n s, get F n s -> subTerm (snd s) sT)
      (ST:subTerm t sT)
  : length F = length als
    -> annotation t alt
    -> (forall n Zs a, get F n Zs -> get als n a -> annotation (snd Zs) a)
    -> poLe als als'
    -> poLe alt alt'
    -> poLe (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform (fst ⊝ F ++ ZL)) F als STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST alt)))
         (fold_left
            (zip orb)
            (snd ⊝ forwardF (forward reachability_transform (fst ⊝ F ++ ZL)) F als' STF)
            (snd (forward reachability_transform (fst ⊝ F ++ ZL)
                          t ST alt'))).
Proof.
  intros LEN Ant AnF LE1 LE2.
  eapply fold_left_mono.
  - eapply poLe_map; eauto.
    eapply (@forwardF_monotone sT (fun _ => bool)); eauto.
  - eapply (@forward_monotone sT (fun _ => bool)); eauto.
Qed.

Lemma impl_impb (a b: bool)
  : (a -> b) -> impb a b.
Proof.
  destruct a, b; firstorder.
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
  : reachability cop2bool Complete BL s a
    -> forall n, get (snd (forward reachability_transform ZL s ST (setTopAnn a b))) n true
           -> poLe (getAnn a) b
           -> isCalled true s (LabI n).
Proof.
  intros.
  general induction H; simpl in *;
    repeat let_case_eq; repeat simpl_pair_eqs; subst;
      simpl in *; eauto using isCalled.
  - inv_get. cases in H7; try congruence.
    + eapply forward_snd_poLe in H7; eauto; clear_trivial_eqs.
      * eapply IsCalledIf2; eauto.
        eapply IHreachability2; eauto.
        cases in H5; eauto.
        rewrite H0; eauto.
        eapply op2bool_cop2bool_not_some; eauto.
      * rewrite H3; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
    + cases in H5; try congruence.
      eapply forward_snd_poLe in H5; eauto; clear_trivial_eqs.
      * eapply IsCalledIf1; eauto.
        eapply IHreachability1; eauto.
        rewrite H; eauto.
        eapply op2bool_cop2bool_not_some; eauto.
      * rewrite H4; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
      * eapply orb_prop in EQ. destruct EQ; subst; isabsurd.
        -- eapply IsCalledIf1; eauto.
           eapply IHreachability1; eauto.
           rewrite H; eauto.
           eapply op2bool_cop2bool_not_some; eauto.
        -- eapply IsCalledIf2; eauto.
           eapply IHreachability2; eauto.
           rewrite H0; eauto.
           eapply op2bool_cop2bool_not_some; eauto.
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
      exploit IHreachability; eauto.
      eapply IsCalledLet; eauto.
      econstructor 1.
    + inv_get.
      exploit H2; eauto.
      rewrite <- (setTopAnn_eta x3 eq_refl) in Get.
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.

Lemma reachability_analysis_complete_isCalled' BL s a b
  : reachability cop2bool Complete BL s a
    -> forall n, get BL n true
           -> poLe (getAnn a) b
           -> isCalled true s (LabI n).
Proof.
Admitted.

Lemma reachability_analysis_complete sT ZL BL BL' (Len:❬BL❭ = ❬BL'❭) s a (ST:subTerm s sT) b b' c
      (LDEF:labelsDefined s (length ZL))
      (EQ:(fst (forward reachability_transform ZL s ST (setTopAnn a b))) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe b b')
  : reachability cop2bool Complete BL s a
    -> reachability cop2bool Complete BL' s (setTopAnn c b').
Proof.
  subst c.
  intros RCH.
  general induction RCH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; try inv LE;
    clear_trivial_eqs;
    eauto using reachability, subTerm, reachability_sTA_inv,
    ann_R_setTopAnn_left.
  - econstructor. eapply reachability_sTA_inv.
    eapply IHRCH; eauto.
    rewrite setTopAnn_eta; eauto.
    repeat rewrite (@forward_getAnn' _ (fun _ => bool)). eauto.
  - econstructor; intros; cases; simpl;
      eauto using reachability_sTA_inv, ann_R_setTopAnn_left.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH1; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + eapply reachability_sTA_inv. eapply IHRCH2; eauto.
      rewrite setTopAnn_eta; eauto.
    + intros. exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
    + intros. exfalso.
      eapply op2bool_cop2bool_not_some in NOTCOND; eauto.
  - inv_get. econstructor; eauto. simpl; eauto.
  - econstructor; eauto.
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
      eapply H2. eauto. eauto. len_simpl.
      rewrite H14. len_simpl. omega.
      eauto with len.
      rewrite (setTopAnn_eta _ eq_refl).
      assert (x = x6) by eapply subTerm_PI. subst. eauto.
      rewrite H8. rewrite getAnn_setTopAnn; eauto.
    + intros. inv_get.
      rewrite getAnn_setTopAnn in H6.
      destruct x0; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply reachability_analysis_complete_isCalled in H5; eauto.
        econstructor; split; eauto. econstructor 1.
        eapply ann_R_get in H16.
        rewrite (@forward_getAnn' _ (fun _ => bool)) in H16.
        rewrite getAnn_setTopAnn in H16. eauto.
      * dcr. inv_get.
        rewrite <- (setTopAnn_eta x8 eq_refl) in H11.
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
        rewrite <- (setTopAnn_eta x8 eq_refl) in H11.
        eapply forward_snd_poLe in H11; eauto.
        exploit H4; eauto.
Qed.

Lemma reachability_complete_bottom BL s
  : labelsDefined s ❬BL❭
    -> reachability cop2bool Complete BL s (setAnn bottom s).
Proof.
  revert BL.
  sind s; intros; destruct s; invt labelsDefined; simpl; eauto 10 using reachability.
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

Lemma reachability_complete_initial BL s
  : labelsDefined s ❬BL❭
    -> reachability cop2bool Complete BL s (setTopAnn (setAnn bottom s) true).
Proof.
  revert BL. Opaque bottom.
  intros.
  destruct s; inv H; simpl setAnn; simpl setTopAnn;
    try now (econstructor; eauto using reachability_complete_bottom;
             try rewrite getAnn_setAnn; simpl; eauto).
  - edestruct get_in_range; eauto.
    econstructor; simpl; eauto.
  - econstructor; simpl; eauto using reachability_complete_bottom with len.
    + intros; inv_get; eauto.
      eapply reachability_complete_bottom; eauto.
      len_simpl; eauto.
    + intros; inv_get; eauto.
      unfold comp in H1. rewrite getAnn_setAnn in H1. intuition.
    + intros; inv_get; eauto.
      unfold comp. eauto.
Qed.

Lemma reachability_complete s
  : labelsDefined s ❬nil:list params❭
    -> reachability cop2bool Complete nil s (reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - unfold initial_value. simpl.
    eapply reachability_complete_initial; eauto.
  - intros. rewrite <- (setTopAnn_eta _ eq_refl).
    eapply (@reachability_analysis_complete s nil); eauto.
    + rewrite setTopAnn_eta; reflexivity.
    + simpl. erewrite !(setTopAnn_eta _ eq_refl); eauto.
    + simpl. rewrite (@forward_getAnn' s (fun _ => bool)); eauto.
Qed.

Lemma correct s
  : labelsDefined s 0
    -> reachability cop2bool SoundAndComplete nil s (reachabilityAnalysis s).
Proof.
  intros.
  eapply reachability_sound_and_complete.
  - eapply reachability_complete; eauto.
  - unfold reachabilityAnalysis.
    destr_sig. destr_sig. dcr.
    eapply (@reachability_sound s nil); simpl; eauto.
    + eapply H2.
    + assert (❬snd (forward reachability_transform nil s (subTerm_refl s) x)❭ = 0).
      rewrite (@forward_length _ (fun _ => bool)); eauto.
      destruct (snd (forward reachability_transform nil s (subTerm_refl s) x)); isabsurd.
      eauto using PIR2.
Qed.

Lemma reachabilityAnalysis_getAnn s
  : getAnn (ReachabilityAnalysis.reachabilityAnalysis s).
Proof.
  unfold reachabilityAnalysis. destr_sig.
  destruct e as [n [Iter _]]. subst.
  intros. eapply safeFixpoint_induction.
  - simpl. rewrite getAnn_setTopAnn; eauto.
  - intros. simpl.
    rewrite (@forward_getAnn' s (fun _ => bool)); eauto.
Qed.