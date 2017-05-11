Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet OptionR MoreList.
Require Import Val Var Env IL Annotation Infra.Lattice.
Require Import DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisForwardSSA FiniteFixpointIteration.
Require Import Reachability Subterm AnnotationLattice DomainSSA.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {D} {H} {H0} exp_transf reach_transf ZL ZLIncl st ST d anr.

Opaque poLe.

(* Coq can't figure out the instantiation (fun _ => bool) via unification,
   so we have to add this specialized lemma *)

(*Lemma forward_length_ass_UC
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
 *)

Lemma poEq_pair_inv A `{PartialOrder A} B `{PartialOrder B} (x y:A * B)
  : poEq x y <-> poEq (fst x) (fst y) /\ poEq (snd x) (snd y).
Proof.
  firstorder.
Qed.

Smpl Add 120
     match goal with
     | [ H : poEq (_,_) (_,_) |- _ ] =>
       rewrite poEq_pair_inv in H; simpl fst in H; simpl snd in H;
         let H' := fresh H in destruct H as [H H']
     | [H : poEq ?x ?x |- _ ] => clear H
     end : inv_trivial.


Ltac is_in_context X :=
  match goal with
  | [ H : ?Y  |- _ ] =>
    unify X Y
  end.

Smpl Add 120 match goal with
         | [ H : ?x = getAnn ?y, I : context [ setTopAnn ?y ?x ] |- _ ] =>
           rewrite (@setTopAnn_eta _ _ _ (eq_sym H)) in I
         | [ H : getAnn ?y = ?x, I : context [ setTopAnn ?y ?x ] |- _ ] =>
           rewrite (@setTopAnn_eta _ _ _ H) in I
         end : inv_trivial.

Ltac simpl_forward_setTopAnn :=
  match goal with
  | [H : ann_R _ (snd (fst (@forward ?sT ?D ?PO ?JSL ?f ?fr ?ZL ?ZLIncl
                                     ?s ?ST ?d ?r))) ?r' |- _ ] =>
    let X := fresh "HEQ" in
    match goal with
    | [ H' : getAnn r = getAnn r' |- _ ] => fail 1
    | _ => first
            [ unify r r'; fail 1
            | exploit (@forward_getAnn sT D PO JSL f fr ZL ZLIncl s ST d r r' H) as X;
              subst]
    end
  end; subst; try eassumption;
  try rewrite getAnn_setTopAnn in *;
  repeat rewrite setTopAnn_eta' in *.

Smpl Add 130 simpl_forward_setTopAnn : inv_trivial.


Opaque poEq.
Opaque poLe.


Definition reachability_sound (sT:stmt) D `{JoinSemiLattice D}
           f fr pr ZL BL s (d:VDom (occurVars sT) D) r (ST:subTerm s sT) ZLIncl
           (EQ:(fst (forward f fr ZL ZLIncl s ST d r)) ≣ (d,r))
    (Ann: annotation s r)
    (DefZL: labelsDefined s (length ZL))
    (DefBL: labelsDefined s (length BL))
    (BL_le: poLe (snd (forward f fr ZL ZLIncl s ST d r)) BL)
    (fExt: forall U e (a a':VDom U D), a ≣ a' -> forall b b', b ≣ b' -> f _ b a e ≣ f _ b' a' e)
    (frExt:forall U e (a a':VDom U D),
        a ≣ a' -> forall b b', b ≣ b' -> fr _ b a e ≣ fr _ b' a' e)
  : reachability pr Sound BL s r.
Proof.
  general induction Ann; simpl in *; inv DefZL; inv DefBL;
    repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *;
      simpl in *.
  - clear_trivial_eqs.
    econstructor; eauto.
    eapply IHAnn; eauto. split; simpl; eauto.
    rewrite EQ.
  - clear_trivial_eqs.
    econstructor; eauto.
    + admit.
    + admit.
    + eapply IHAnn1; eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
      split; eauto. simpl. reflexivity.
    + eapply IHAnn2; eauto using @PIR2_zip_join_inv_left, @PIR2_zip_join_inv_right with len.
      split; eauto.
  - edestruct get_in_range; eauto.
    edestruct get_in_range; try eapply H4; eauto.
    Transparent poLe. hnf in BL_le.
    edestruct PIR2_nth; eauto using ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; simpl; eauto.
  - econstructor.
  - clear_trivial_eqs.
    set (FWt:=(forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t
                       (subTerm_EQ_Fun1 eq_refl ST) d ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) s (joinTopAnn (A:=bool) ⊜ sa (snd FWt)) (fst (fst FWt)) (subTerm_EQ_Fun2 eq_refl ST)) in *.
    intros.
    eapply PIR2_get in H15; eauto with len.
    exploit (snd_forwardF_inv _ _ _ _ _ _ _ _ H15); eauto.
    subst FWt. len_simpl. omega.
    subst FWt. len_simpl. omega.
    exploit (snd_forwardF_inv' _ _ _ _ _ _ _ _ H15); eauto.
    subst FWt. len_simpl. omega.
    subst FWt. len_simpl. omega.
    assert (forall (n : nat) (r : ann bool) (Zs : params * stmt),
       get sa n r ->
       get s n Zs ->
       forall STZs : subTerm (snd Zs) sT,
       ann_R eq
         (snd
            (fst
               (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)
                        (snd Zs) STZs (fst (fst FWt)) r))) r).
    eapply (@snd_forwardF_inv_get); eauto.
    subst FWt. len_simpl.  omega.
    subst FWt. len_simpl. omega.
    intros. admit.
    Ltac PIR2_eq_simpl :=
      match goal with
      | [ H : PIR2 (ann_R eq) _ _ |- _ ] =>
        eapply PIR2_R_impl with (R':=eq) in H;
        [|intros ? ?; rewrite <- ann_R_eq; let A := fresh "A" in intros A; apply A]
      | [ H : PIR2 eq _ _ |- _ ] =>
        eapply PIR2_eq in H
      | [ H : ann_R eq _ _ |- _ ] => rewrite ann_R_eq in H
      end.
    Transparent poEq. simpl in *.
    repeat PIR2_eq_simpl.
    subst FWF FWt.
    rewrite H3 in *.
    rewrite H4 in *.
    set (FWt:=(forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t
                       (subTerm_EQ_Fun1 eq_refl ST) d ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward f fr (fst ⊝ s ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) s sa (fst (fst FWt)) (subTerm_EQ_Fun2 eq_refl ST)) in *.
    econstructor; eauto.
    + eapply IHAnn; eauto.
      * split; eauto. simpl. reflexivity.
        simpl. Transparent poEq. rewrite <- H16 at 2.
        unfold FWt. reflexivity.
      * erewrite (take_eta ❬s❭) at 1. eapply PIR2_app; eauto.
        -- change (PIR2 impb) with (@poLe (list bool) _).
           assert (PIR2 impb (Take.take ❬s❭ (snd FWt)) (getAnn ⊝ sa)). {
             change (PIR2 impb) with (PIR2 (@poLe bool _)).
             rewrite H.
             eapply (@joinTopAnn_map_inv).
             rewrite <- H3 at 2. reflexivity.
           }
           rewrite <- H4. subst FWF.
           subst FWt.
           rewrite H10.
           rewrite <- (@forwardF_mon' sT Dom f fr); eauto.
        -- rewrite <- BL_le.
           eapply PIR2_drop.
           etransitivity;[|
                          eapply forwardF_mon; eauto].
           reflexivity.
           subst FWt. eauto with len.
    + intros.
      eapply H1; eauto.
      -- split; eauto. simpl. reflexivity.
      -- rewrite (take_eta ❬sa❭) at 1.
         eapply PIR2_app; eauto.
         ++ eapply setTopAnn_map_inv in H15.
           rewrite <- H15. eapply PIR2_take.
           change (PIR2 impb) with (@poLe (list bool) _).
           eapply forwardF_PIR2; eauto.
           subst FWt. clear_all. eauto with len.

         ++ etransitivity; eauto.
           rewrite H. eapply PIR2_drop.
           eapply forwardF_PIR2; eauto.
           subst FWt. eauto with len.
           admit.
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

Opaque poLe.


Lemma forward_snd_poLe sT BL ZL s (ST:subTerm s sT) n a b c
  : reachability cop2bool Complete BL s a
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
      eapply IH in H6; simpl in *; eauto.
      rewrite H6. eauto.
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
      eapply IH in H4; eauto.
      exploit H13; eauto.
Qed.

Local Hint Extern 0 => first [ erewrite (@forward_getAnn' _ (fun _ => bool))
                            | erewrite getAnn_setTopAnn
                            | rewrite getAnn_setAnn ].

Transparent poLe.

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
    + PI_simpl.
      eapply (@forward_monotone sT (fun _ => bool) _ _ _ reachability_transform ); eauto.
      eapply reachability_transform_monotone; eauto.
      eapply ann_R_get.
      eapply get_PIR2; eauto.
      eapply get_PIR2; eauto.
    + rewrite !map_length.
      rewrite !(@forwardF_length _ (fun _ => bool)).
      rewrite (PIR2_length LE1). reflexivity.
  - exploit (@forward_monotone sT (fun _ => bool) _ _ _ reachability_transform );
      try eapply H; eauto.
    eapply reachability_transform_monotone.
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

Opaque poLe.

Lemma reachability_analysis_complete_isCalled sT ZL BL s a b
      (ST:subTerm s sT)
  : reachability cop2bool Complete BL s a
    -> forall n, get (snd (forward reachability_transform ZL s ST b a)) n true
           -> poLe (getAnn a) b
           -> isCalled true s (LabI n).
Proof.
  intros.
  general induction H; simpl in *;
    repeat let_case_eq; repeat simpl_pair_eqs; subst;
      simpl in *; eauto using isCalled.
  - inv_get. cases in H7; try congruence.
    + eapply forward_snd_poLe in H7; eauto; clear_trivial_eqs.
      * destruct x; isabsurd. simpl in *; subst.
        eapply IsCalledIf2; eauto.
        eapply IHreachability2; eauto.
        cases in H5; eauto.
        rewrite H0; eauto.
        eapply op2bool_cop2bool_not_some; eauto.
      * rewrite H3; eauto.
        rewrite op2bool_cop2bool in COND. rewrite COND. reflexivity.
    + cases in H5; try congruence.
      eapply forward_snd_poLe in H5; eauto; clear_trivial_eqs.
      * destruct x0; isabsurd.
        eapply orb_prop in EQ. destruct EQ; subst; isabsurd.
        eapply IsCalledIf1; eauto.
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
      exploit forward_snd_poLe; try eapply Get; eauto.
      exploit H3; eauto; dcr.
      edestruct isCalledFrom_extend; eauto; dcr.
      econstructor; eauto.
Qed.

Lemma reachability_analysis_complete sT ZL BL BL' (Len:❬BL❭ = ❬BL'❭) s a (ST:subTerm s sT) b b' c
      (LDEF:labelsDefined s (length ZL))
      (EQ:(fst (forward reachability_transform ZL s ST b a)) = c)
      (LE:poLe a (setTopAnn c b'))
      (LEb: poLe (getAnn c) b')
  : reachability cop2bool Complete BL s a
    -> reachability cop2bool Complete BL' s (setTopAnn c b').
Proof.
  subst c.
  intros RCH.
  general induction RCH; simpl in *; repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst; simpl in *; invt labelsDefined; try inv LE;
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
  - inv_get. econstructor; eauto.
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
      eapply H2. eauto. rewrite setTopAnn_eta. eauto.
      eauto.
      eauto with len.
      eauto.
      eapply ann_R_get in H8. rewrite getAnn_setTopAnn in H8.
      eauto.
      etransitivity; eauto.
      rewrite (setTopAnn_eta _ eq_refl).
      Transparent poLe.
      eapply H8.
      pose proof (@poLe_setTopAnn bool _ x0 x0).
      eapply H10; eauto. assert (x = x6) by eapply subTerm_PI.
      subst. rewrite setTopAnn_eta. reflexivity. eauto.
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

Lemma reachability_complete s
  : labelsDefined s ❬nil:list params❭
    -> reachability cop2bool Complete nil s (reachabilityAnalysis s).
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
    -> reachability cop2bool SoundAndComplete nil s (reachabilityAnalysis s).
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