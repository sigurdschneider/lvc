Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForward UnreachableCodeAnalysis UnreachableCode Subterm.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} ftransform ZL st ST a.

Ltac simpl_forward_setTopAnn :=
  repeat match goal with
         | [H : ann_R eq (fst (forward ?unreachable_code_transform ?ZL ?s ?ST (setTopAnn ?sa ?a))) ?sa |- _ ] =>
           let X := fresh "H" in
           match goal with
           | [ H' : getAnn sa = a |- _ ] => fail 1
           | _ => exploit (forward_getAnn _ _ _ _ _ H) as X
           end
         end; rewrite setTopAnn_eta in *; try eassumption.

Lemma PIR2_zip_join_inv_left X `{BoundedSemiLattice X} A B C
  : poLe (join ⊜ A B) C
    -> length A = length B
    -> poLe A C.
Proof.
  intros. length_equify. hnf in H1.
  general induction H1; inv H2; simpl in *; eauto using PIR2; try solve [ congruence ].
  - inv Heql; econstructor; eauto.
    + rewrite <- pf. eapply join_poLe.
Qed.

Lemma PIR2_zip_join_inv_right X `{BoundedSemiLattice X} A B C
  : poLe (join ⊜ A B) C
    -> length A = length B
    -> poLe B C.
Proof.
  intros. length_equify. hnf in H1.
  general induction H1; inv H2; simpl in *; eauto using PIR2; try solve [ congruence ].
  - inv Heql; econstructor; eauto.
    + rewrite <- pf. rewrite join_commutative. eapply join_poLe.
Qed.

Lemma PIR2_poLe_zip_join_left X `{BoundedSemiLattice X} A B
  : length A = length B
    -> poLe A (join ⊜ A B).
Proof.
  intros. length_equify.
  general induction H1; simpl in *; eauto using PIR2; try solve [ congruence ].
  - econstructor; eauto using join_poLe.
Qed.

Lemma PIR2_zip_join_commutative X `{BoundedSemiLattice X} A B
  : poLe (join ⊜ B A) (join ⊜ A B).
Proof.
  intros.
  general induction A; destruct B; simpl in *; eauto using PIR2.
  econstructor; eauto. rewrite join_commutative; eauto.
Qed.

Lemma PIR2_poLe_zip_join_right X `{BoundedSemiLattice X} A B
  : length A = length B
    -> poLe B (join ⊜ A B).
Proof.
  intros. rewrite <- PIR2_zip_join_commutative. (* todo: missing morphism *)
  eapply PIR2_poLe_zip_join_left; congruence.
Qed.

Lemma PIR2_fold_zip_join_inv X `{BoundedSemiLattice X} A B C
  : poLe (fold_left (zip join) A B) C
    -> (forall n a, get A n a -> length a = length B)
    -> poLe B C.
Proof.
  intros.
  general induction A; simpl in *; eauto.
  eapply IHA; eauto using get.
  etransitivity; eauto.
  eapply PIR2_fold_zip_join; eauto.
  eapply PIR2_poLe_zip_join_left.
  symmetry. eauto using get.
Qed.

Lemma PIR2_fold_zip_join_right X `{BoundedSemiLattice X} (A:list X) B C
  : (forall n a, get B n a -> length a = length C)
    -> poLe A C
    -> poLe A (fold_left (zip join) B C).
Proof.
  general induction B; simpl; eauto.
  eapply IHB; intros; eauto using get with len.
  - rewrite zip_length2; eauto using eq_sym, get.
  - rewrite H2. eapply PIR2_poLe_zip_join_left. symmetry. eauto using get.
Qed.

Lemma PIR2_fold_zip_join_left X `{BoundedSemiLattice X} (A:list X) B C a k
  : get B k a
    -> poLe A a
    -> (forall n a, get B n a -> length a = length C)
    -> poLe A (fold_left (zip join) B C).
Proof.
  intros.
  general induction B; simpl in *; eauto.
  - isabsurd.
  - inv H1.
    + eapply PIR2_fold_zip_join_right.
      intros. rewrite zip_length2; eauto using eq_sym, get.
      rewrite H2. eapply PIR2_poLe_zip_join_right.
      eauto using eq_sym, get.
    + eapply IHB; eauto using get.
      intros. rewrite zip_length2; eauto using eq_sym, get.
Qed.


Lemma get_union_union_b X `{BoundedSemiLattice X} (A:list (list X)) (b:list X) n x
  : get b n x
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip join) A b) n y /\ poLe x y.
Proof.
  intros GETb LEN. general induction A; simpl in *.
  - eexists x. eauto with cset.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETb (eq_sym H1)) as [y GETa]; eauto.
    exploit (zip_get join GETb GETa).
    + exploit IHA; try eapply GET; eauto.
      rewrite zip_length2; eauto using get with len.
      edestruct H3; dcr; subst. eexists; split; eauto.
      rewrite <- H8; eauto. eapply join_poLe.
Qed.


Lemma get_union_union_A X `{BoundedSemiLattice X} (A:list (list X)) a b n k x
  : get A k a
    -> get a n x
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> exists y, get (fold_left (zip join) A b) n y /\ poLe x y.
Proof.
  intros GETA GETa LEN.
  general induction A; simpl in * |- *; isabsurd.
  inv GETA; eauto.
  - exploit LEN; eauto using get.
    edestruct (get_length_eq _ GETa H1) as [y GETb].
    exploit (zip_get join GETb GETa).
    exploit (@get_union_union_b _ _ _ A); eauto.
    rewrite zip_length2; eauto using get with len.
    destruct H3; dcr; subst. eexists; split; eauto.
    rewrite <- H5; eauto. rewrite join_commutative.
    eapply join_poLe.
  - exploit IHA; eauto.
    rewrite zip_length2; eauto using get.
    symmetry; eauto using get.
Qed.

(*
Lemma get_olist_union_A' X `{OrderedType X} A a b n k x p
  : get A k a
    -> get a n (Some x)
    -> (forall n a, get A n a -> ❬a❭ = ❬b❭)
    -> get (olist_union A b) n p
    -> exists s, p = (Some s) /\ x ⊆ s.
Proof.
  intros. edestruct get_olist_union_A; eauto; dcr.
  get_functional; eauto.
Qed.
*)

Lemma setTopAnn_inv A R (an an':ann A) a
  : ann_R R (setTopAnn an a) an'
    -> R a (getAnn an').
Proof.
  intros; destruct an; inv H; simpl; eauto.
Qed.

Opaque poLe.

Definition unreachable_code_analysis_correct sT ZL BL s a (ST:subTerm s sT)
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
      eapply (@forward_length_ass _ (fun _ => bool)); eauto. symmetry.
      eapply (@forward_length_ass _ (fun _ => bool)); eauto.
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
        repeat rewrite (@forward_length sT (fun _ => bool)); eauto with len.
        rewrite Take.take_less_length. eauto with len.
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
        edestruct (@forwardF_get _ _ _ _ _ _ _ _ _ _ _ H). dcr; subst.
        subst FWt.
        repeat erewrite (@forward_length sT (fun _ => bool)); eauto with len.
      *
        rewrite (take_eta ❬sa❭) at 1.
        eapply PIR2_app.
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
        edestruct (@forwardF_get _ _ _ _ _ _ _ _ _ _ _ H). dcr; subst.
        subst FWt.
        repeat erewrite (@forward_length sT (fun _ => bool)); eauto with len.
        rewrite Take.take_less_length; eauto with len.
        rewrite (@forward_length _ (fun _ => bool)). eauto with len.
        etransitivity; eauto.
        rewrite H. eapply PIR2_drop.
        subst FWF.
        pose proof (@PIR2_fold_zip_join_left bool _ _). eapply H13.
        eauto. reflexivity.
        clear_all. intros. inv_get.
        edestruct (@forwardF_get _ _ _ _ _ _ _ _ _ _ _ H). dcr; subst.
        subst FWt.
        repeat erewrite (@forward_length sT (fun _ => bool)); eauto with len.
    + simpl. eauto.
Qed.


Inductive unreachable_code_complete
  : list params -> list bool -> stmt -> ann bool -> Prop :=
| UCPOpr ZL BL x s b e al
  :  unreachable_code_complete ZL BL s al
     -> unreachable_code_complete ZL BL (stmtLet x e s) (ann1 b al)
| UCPIf ZL BL e b1 b2 b al1 al2
  :  unreachable_code_complete ZL BL b1 al1
     -> unreachable_code_complete ZL BL b2 al2
     -> unreachable_code_complete ZL BL (stmtIf e b1 b2) (ann2 b al1 al2)
| UCPGoto ZL BL l Y a
  : unreachable_code_complete ZL BL (stmtApp l Y) (ann0 a)
| UCReturn ZL BL e b
  : unreachable_code_complete ZL BL (stmtReturn e) (ann0 b)
| UCExtern ZL BL x s b Y al f
  : unreachable_code_complete ZL BL s al
    -> unreachable_code_complete ZL BL (stmtExtern x f Y s) (ann1 b al)
| UCLet ZL BL F t b als alt
  : unreachable_code_complete (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) t alt
    -> length F = length als
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 unreachable_code_complete (fst ⊝ F ++ ZL) (getAnn ⊝ als ++ BL) (snd Zs) a)
    -> (forall n Zs a, get F n Zs ->
                 get als n a ->
                 getAnn a ->
                 trueIsCalled t (LabI n))
-> unreachable_code_complete ZL BL (stmtFun F t) (annF b als alt).


Definition unreachableCodeAnalysis s :=
  Analysis.safeFixpoint (unreachable_code_analysis s).

Lemma unreachable_code_analysis_complete sT ZL BL s a (ST:subTerm s sT) b
  : unreachable_code_complete ZL BL s a
    -> forall n, get (snd (forward unreachable_code_transform ZL s ST (setTopAnn a b))) n true
           -> trueIsCalled s (LabI n).
Proof.
  intros. general induction H; simpl in *; repeat let_case_eq; repeat simpl_pair_eqs; subst;
            simpl in *; eauto using trueIsCalled.
  - admit.
  - admit.
  - exfalso. inv_get.
  -
  econstructor. eapply IHunreachable_code_complete.

Qed.

Lemma unreachable_code_analysis_complete sT ZL BL BL' s a (ST:subTerm s sT) b
  : unreachable_code_complete ZL BL s a
    -> unreachable_code_complete ZL BL' s
                                (fst (forward unreachable_code_transform ZL s ST (setTopAnn a b))).
Proof.
  intros UCC.
  general induction UCC; simpl; repeat let_pair_case_eq; subst; simpl;
    eauto using unreachable_code_complete, subTerm.
  - econstructor; eauto.
    + rewrite zip_length, map_length.
      rewrite (@forwardF_length _ (fun _ => bool)).
      admit.
    + intros. inv_get. eapply H1.
    + intros. inv_get.
      eapply H2; eauto.
Qed.




Ltac destr_sig H :=
  match type of H with
  | context [proj1_sig ?x] => destruct x; simpl in H
  end.

Tactic Notation "destr_sig" :=
  match goal with
  | [ |- context [proj1_sig (proj1_sig ?x)] ] => destruct x; simpl
  | [ |- context [proj1_sig ?x] ] => destruct x; simpl
  end.

Definition correct s
  : labelsDefined s 0
    -> paramsMatch s nil
    -> true_live_sound Imperative nil nil s (livenessAnalysis s).
Proof.
  intros.
  unfold livenessAnalysis.
  destr_sig. destr_sig. dcr.
  eapply (@liveness_analysis_correct s nil nil s); eauto.
  eapply H3.
Qed.
