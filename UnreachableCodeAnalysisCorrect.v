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

Inductive isCalledIn' (als:list (ann bool)) (F:〔params * stmt〕)
  : stmt -> lab -> Prop :=
| IsCalledIn s l
  : trueIsCalled s l -> isCalledIn' als F s l
| IsCalledInNext k s Zs l a
  : trueIsCalled s (LabI k)
    -> get F k Zs
    -> get als k a
    -> getAnn a
    -> isCalledIn' als F (snd Zs) l -> isCalledIn' als F s l.

Lemma isCalledIn'_trueIsCalledIn als F s l
  : isCalledIn' als F s l -> isCalledIn trueIsCalled F s l.
Proof.
  induction 1; eauto using isCalledIn.
Qed.

Hint Resolve isCalledIn'_trueIsCalledIn.

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
          isCalledIn' als F t (LabI n))
    -> (forall n a, get als n a -> impb (getAnn a) b )
    -> impb (getAnn alt) b
-> unreachable_code_complete ZL BL (stmtFun F t) (annF b als alt).

Lemma unreachable_code_complete_annotation ZL BL s a
  : unreachable_code_complete ZL BL s a
    -> annotation s a.
Proof.
  intros. general induction H; eauto using @annotation.
Qed.

Lemma fold_left_zip_orb_inv A b n
  : get (fold_left (zip orb) A b) n true
    -> get b n true \/ exists k a, get A k a /\ get a n true.
Proof.
  intros Get.
  general induction A; simpl in *; eauto.
  edestruct IHA; dcr; eauto 20 using get.
  inv_get. destruct x, x0; isabsurd; eauto using get.
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
      edestruct (forwardF_get _ _ _ _ _ H2); dcr; subst.
      erewrite <- (@setTopAnn_eta _ x3 (getAnn x3)) in H4; eauto.
      eapply IH in H4; eauto.
      exploit H13; eauto. etransitivity; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Lemma unreachable_code_analysis_complete_setTopAnn ZL BL s a b (LE:poLe (getAnn a) b)
  : unreachable_code_complete ZL BL s a
    -> unreachable_code_complete ZL BL s (setTopAnn a b).
Proof.
  intros UCC; general induction UCC; simpl in *;
    eauto using unreachable_code_complete.
  - econstructor; eauto.
    intros; eauto.
    exploit H3; eauto.
Qed.

Lemma isCalledIn_extend (F:list (params * stmt)) k t f Zs
  : isCalledIn trueIsCalled F t (LabI k)
    -> get F k Zs
    -> trueIsCalled (snd Zs) f
    -> isCalledIn trueIsCalled F t f.
Proof.
  intros. general induction H; eauto using isCalledIn, get_range.
Qed.

Lemma isCalledIn'_extend als (F:list (params * stmt)) k t f Zs a
  : isCalledIn' als F t (LabI k)
    -> get F k Zs
    -> get als k a
    -> getAnn a
    -> trueIsCalled (snd Zs) f
    -> isCalledIn' als F t f.
Proof.
  intros. general induction H; eauto using isCalledIn', get_range.
Qed.

Lemma unreachable_code_analysis_complete_isCalled sT ZL BL s a (ST:subTerm s sT) b
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
      destruct x,x0; isabsurd;
        try solve [ eapply TrueIsCalledIf2;
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
  - inv_get.
    eapply fold_left_zip_orb_inv in H6.
    destruct H6; dcr.
    + eapply TrueIsCalledLet.
      exploit IHunreachable_code_complete; eauto.
      econstructor; eauto.
    + inv_get. edestruct (forwardF_get _ _ _ _ _ H8); dcr; subst.
      erewrite <- (@setTopAnn_eta _ x3 (getAnn x3)) in H10; eauto.
      exploit H2; eauto.
      exploit forward_snd_poLe; try eapply H10; eauto.
      exploit H3; eauto.
      econstructor.
      eapply isCalledIn_extend; eauto.
Qed.

Lemma trueIsCalled_snd_forward sT ZL s (ST:subTerm s sT) a n
  : trueIsCalled s (LabI n)
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> get (snd (forward unreachable_code_transform ZL s ST
                        (setTopAnn a true))) n true.
Proof.
  intros.
  general induction H0; invt trueIsCalled; invt labelsDefined; simpl;
    repeat let_pair_case_eq; subst; simpl; eauto.
  - exploit (IHannotation1 sT ZL (subTerm_EQ_If1 eq_refl ST)); eauto.
    cases; try congruence.
    edestruct (@get_length_eq). eapply H0. Focus 2.
    eapply zip_get_eq. eapply H0. eapply H2. eauto.
    repeat rewrite (@forward_length _ (fun _ => bool)). eauto.
  - exploit (IHannotation2 sT ZL (subTerm_EQ_If2 eq_refl ST)); eauto.
    edestruct (@get_length_eq). eapply H0. Focus 2.
    eapply zip_get_eq. eapply H2.
    cases. congruence. eauto. destruct x0; eauto.
    repeat rewrite (@forward_length _ (fun _ => bool)). eauto.
  - exploit get_in_range; eauto; dcr.
    eapply ListUpdateAt.list_update_at_get_3.
    eapply map_get_1. eauto.
  - eapply drop_get.
    general induction H8.
    + eapply (IHannotation sT (fst ⊝ s ++ ZL) (subTerm_EQ_Fun1 eq_refl ST)) in H; eauto.

      edestruct (@get_union_union_b _ _ _ (snd
         ⊝ forwardF (forward unreachable_code_transform) (fst ⊝ s ++ ZL) s sa
         (subTerm_EQ_Fun2 eq_refl ST))). eauto.
      intros. inv_get.
      edestruct (forwardF_get _ _ _ _ _ H6); dcr; subst.
      repeat rewrite (@forward_length _ (fun _ => bool)). eauto.
      dcr. destruct x; isabsurd.
      eapply H8.
    + eapply IHisCalledIn.

Admitted.

Lemma isCalledIn_mono sT F t n Zs ZL (ST:subTerm (stmtFun F t) sT) als k a
  : length F = length als
    -> isCalledIn' als F (snd Zs) (LabI n)
    -> get F k Zs
    -> get als k a
    -> getAnn a
    -> (forall n Zs a, get F n Zs -> get als n a -> annotation (snd Zs) a)
    -> (forall (n : nat) (Zs : params * stmt), get F n Zs -> labelsDefined (snd Zs) (❬F❭ + ❬ZL❭))
    -> exists k a, get (snd ⊝ forwardF (forward unreachable_code_transform) (fst ⊝ F ++ ZL) F als
                      (subTerm_EQ_Fun2 eq_refl ST)) k a /\ get a n true.
Proof.
  intros LEN ICI GetF GetAls Ann IsAnn.
  general induction ICI.
  - inv_get.
    edestruct (@get_forwardF sT (fun _ => bool)); eauto.
    do 2 eexists. split.
    eapply map_get_1. eapply g.
    exploit (@trueIsCalled_snd_forward sT (fst ⊝ F ++ ZL) _ x);
      eauto using unreachable_code_complete_annotation.
    rewrite setTopAnn_eta in H1; eauto.
    eapply Is_true_eq_true; eauto.
  - edestruct IHICI; eauto.
Qed.

Lemma unreachable_code_analysis_complete sT ZL BL BL' s a (ST:subTerm s sT) b
      (LE:impb (getAnn a) b) (LDEF:labelsDefined s (length ZL))
  : unreachable_code_complete ZL BL s a
    -> unreachable_code_complete ZL BL' s
                                (fst (forward unreachable_code_transform ZL s ST (setTopAnn a b))).
Proof.
  intros UCC.
  general induction UCC; simpl; repeat let_pair_case_eq; subst; simpl in *; invt labelsDefined;
    eauto using unreachable_code_complete, subTerm.
  - econstructor; intros; cases; eauto.
    eapply IHUCC1; eauto. rewrite H1; eauto.
    eapply IHUCC2; eauto. rewrite H2; eauto.
  - econstructor; eauto.
    + rewrite zip_length, map_length.
      rewrite (@forwardF_length _ (fun _ => bool)).
      rewrite fold_list_length'.
      rewrite (@forward_length _ (fun _ => bool)).
      rewrite app_length, map_length, <- H.
      repeat rewrite min_l; eauto. omega.
      intros; inv_get.
      edestruct (forwardF_get _ _ _ _ _ H5); dcr; subst.
      rewrite (@forward_length _ (fun _ => bool)).
      rewrite (@forward_length _ (fun _ => bool)). reflexivity.
      intros. rewrite zip_length. rewrite min_l; eauto.
    + intros. inv_get.
      edestruct (forwardF_get _ _ _ _ _ H8); dcr; subst.
      repeat get_functional.
      rewrite <- (setTopAnn_eta x eq_refl).
      eapply unreachable_code_analysis_complete_setTopAnn; eauto.
      erewrite (@forward_getAnn' _ (fun _ => bool)).
      rewrite getAnn_setTopAnn.
      exploit H3; eauto.
      case_eq (getAnn x); intros; [| destruct x0; eauto].
      rewrite H12 in H11; destruct b; isabsurd. destruct b0; isabsurd.
      clear LE H11.
      exploit H2; eauto. rewrite H12; eauto.
      inv H11.
      * exploit (@trueIsCalled_snd_forward _ (fst ⊝ F ++ ZL) _ (subTerm_EQ_Fun1 eq_refl ST));
          eauto using unreachable_code_complete_annotation.
        exploit (@get_union_union_b _ _ _
                                    (snd
                                       ⊝ forwardF (forward unreachable_code_transform)
                                       (fst ⊝ F ++ ZL) F als
                                       (subTerm_EQ_Fun2 eq_refl ST))); eauto.
        intros. inv_get.
        edestruct (forwardF_get _ _ _ _ _ H15); dcr; subst.
        repeat rewrite (@forward_length _ (fun _ => bool)). eauto.
        dcr. get_functional. eauto.
      * intros. eapply (@isCalledIn_mono sT F t n Zs0 ZL ST als) in H17; eauto.
        dcr.
        exploit (@get_union_union_A). eapply H18. eapply H20.
        instantiate (1:=(snd
                           (forward unreachable_code_transform (fst ⊝ F ++ ZL) t
                                    (subTerm_EQ_Fun1 eq_refl ST)
                                    (setTopAnn alt true)))).
        inv_get.
        edestruct (forwardF_get _ _ _ _ _ H17); dcr; subst.
        repeat rewrite (@forward_length _ (fun _ => bool)). eauto.
        dcr. get_functional. eauto.
        intros. exploit H0; eauto. eapply unreachable_code_complete_annotation; eauto.
    + intros. inv_get.
      edestruct (forwardF_get _ _ _ _ _ H8); dcr; subst.
      rewrite getAnn_setTopAnn in H6.
      destruct x0; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply unreachable_code_analysis_complete_isCalled in H5; eauto.
        econstructor; eauto.
        etransitivity; eauto.
      * dcr. inv_get.
        edestruct (forwardF_get _ _ _ _ _ H10); dcr; subst.
        rewrite <- (@setTopAnn_eta _ x8 (getAnn x8)) in H12; eauto.
        exploit forward_snd_poLe; try eapply H12; eauto.
        eapply unreachable_code_analysis_complete_isCalled in H12; eauto.
        exploit H2; eauto.
        eapply isCalledIn'_extend; eauto.
        general induction H11.

    + intros. inv_get. rewrite getAnn_setTopAnn.
      edestruct (forwardF_get _ _ _ _ _ H6); dcr; subst.
      exploit H3; eauto. destruct x0; simpl; eauto.
      destruct b0; eauto. destruct b; isabsurd.
      eapply fold_left_zip_orb_inv in H5. destruct H5.
      * eapply forward_snd_poLe in H5; eauto.
      * dcr. inv_get.
        edestruct (forwardF_get _ _ _ _ _ H8); dcr; subst.
        erewrite <- (@setTopAnn_eta _ x8) in H10; [| reflexivity].
        eapply forward_snd_poLe in H10; eauto.
        exploit H3; eauto. destruct (getAnn x8); isabsurd.
Admitted.

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

Definition unreachableCodeAnalysis s :=
  proj1_sig (proj1_sig (Analysis.safeFixpoint (unreachable_code_analysis s))).

Ltac destr_sig H :=
  match type of H with
  | context [proj1_sig ?x] => destruct x; simpl in H
  end.

Tactic Notation "destr_sig" :=
  match goal with
  | [ |- context [proj1_sig (proj1_sig ?x)] ] => destruct x; simpl
  | [ |- context [proj1_sig ?x] ] => destruct x; simpl
  end.

Lemma ucc_complete s
  : unreachable_code_complete nil nil s (unreachableCodeAnalysis s).
Proof.
  unfold unreachableCodeAnalysis. destr_sig; dcr.
  clear H1. subst. simpl.
  general induction x0.
  - simpl in *. eapply unreachable_code_complete_bottom.
  - rewrite iter_comm; simpl.
    let_pair_case_eq. simpl.
    erewrite <- (setTopAnn_eta x); [| reflexivity].
    eapply unreachable_code_analysis_complete. reflexivity.
    specialize (IHx0 s).
    rewrite H in IHx0. eauto.
Qed.

Lemma ucc_sound_and_complete ZL BL s a
  : unreachable_code_complete ZL BL s a
    -> unreachable_code Sound ZL BL s a
    -> unreachable_code SoundAndComplete ZL BL s a.
Proof.
  intros UCC UCS.
  general induction UCS; inv UCC; eauto using unreachable_code.
Qed.
