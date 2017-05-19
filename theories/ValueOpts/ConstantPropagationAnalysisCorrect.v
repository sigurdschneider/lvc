Require Import Util SizeInduction Get MapDefined Coq.Classes.RelationClasses.
Require Import IL Var Val OptionR AllInRel.
Require Import CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice.
Require Import Analysis AnalysisForwardSSA Subterm CSet MapAgreement RenamedApart.
Require Import Infra.PartialOrder Infra.Lattice Infra.WithTop.
Require Import LabelsDefined Annotation.
Require Import Reachability ReachabilityAnalysisCorrectSSA.
Require Import ConstantPropagation ConstantPropagationAnalysis.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} ftransform reach_transf ZL ZLIncl st.


Notation "'getAE' X" := (proj1_sig (fst (fst X))) (at level 10, X at level 0).

Local Arguments exist {A} {P} x _.
Local Arguments forward {sT} {Dom} ftransform reach_transf ZL {ZLIncl} st {ST}.
Local Arguments cp_trans_dep {sT} ZL st {ST} {ZLIncl}.
Local Arguments cp_trans_domain {sT} ZL st {ST} {ZLIncl} a b.



Definition cp_sound sT AE AE' AV ZL s (ST:subTerm s sT) ZLIncl ra anr
  : let X := @forward sT _ (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s ST AE anr in
    renamedApart s ra
    -> annotation s anr
    -> labelsDefined s (length ZL)
    -> poEq (fst X) (AE,anr)
    -> poEq AE' AE
    -> disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra))
    -> ❬ZL❭ = ❬AV❭
    -> paramsMatch s (length ⊝ ZL)
    -> PIR2 eq AV (List.map (fun Z => lookup_list (domenv (proj1_sig AE')) Z) ZL)
    -> (forall n Z, get ZL n Z -> NoDupA eq Z)
    -> cp_sound (domenv (proj1_sig AE')) (zip pair ZL AV) s anr.
Proof.
  intros LET RA ANN LD EQ1 EQ2 DISJ LEN PM AVREL NODUP. subst LET.
  general induction LD; invt @renamedApart;
    try invt @annotation; simpl in *; simpl; invt @paramsMatch;
      simpl in *; dcr;
        repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst;
          simpl in *; try invtc @ann_R; subst.
  - destruct e; simpl in *; simpl in *; clear_trivial_eqs.
    + assert (EVALEQ:op_eval (domenv (proj1_sig AE')) e = domenv (proj1_sig AE) x). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=(domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e)))
          in AGR.
        instantiate (2:=(cp_trans_domain ZL (stmtLet x (Operation e) s) AE a)) in AGR.
        exploit (AGR x). pe_rewrite. instantiate (2:={x; Ds}).
        eapply renamedApart_disj in H4. pe_rewrite.
        revert H4 DISJ; clear_all. cset_tac.
        exploit (H x).
        eapply option_R_inv in H0.
        eapply option_R_inv in H1. unfold domenv in H0.
        unfold domenv. rewrite <- H1.
        unfold domenv.
        rewrite <- H0.
        rewrite domupd_eq; eauto.
        exploit  eqMap_op_eval. eapply EQ2.
        eapply option_R_inv in H5. eauto.
      }
      assert (MAPEQ:eqMap (proj1_sig AE')
                          (domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e))). {
        rewrite EQ2.
        eapply eqMap_domupd.
        unfold domenv in EVALEQ.
        rewrite <- EVALEQ.
        rewrite <- eqMap_op_eval; [|eapply EQ2].
        reflexivity.
      }
      simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
      econstructor; eauto.
      eapply IHLD with (AE:=(exist (domupd (proj1_sig AE) x (op_eval (domenv (proj1_sig AE)) e))
                      (cp_trans_domain ZL (stmtLet x (Operation e) s) AE (getAnn sa)))); eauto.
      * split; eauto.
        -- simpl.
           etransitivity; eauto.
           etransitivity; eauto.
           symmetry; eauto.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
      * intros; simpl; eauto.
        rewrite EVALEQ.
        exploit (EQ2 x). eapply option_R_inv in H1.
        unfold domenv. congruence.
    + assert (find x (proj1_sig AE') = ⎣ Top ⎦). {
        set_simpl.
        exploit cp_forward_agree_def as AGR. eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (3:=add x Top (proj1_sig AE)) in AGR.
        instantiate (2:=cp_trans_domain ZL (stmtLet x (Call f Y) s) AE a) in AGR.
        exploit (AGR x). pe_rewrite. instantiate (2:={x; Ds}).
        eapply renamedApart_disj in H4. pe_rewrite.
        revert H4 DISJ; clear_all. cset_tac.
        exploit (H x).
        eapply option_R_inv in H0.
        eapply option_R_inv in H1. unfold domenv in H0.
        exploit (EQ2 x).
        eapply option_R_inv in H5. rewrite H5.
        rewrite <- H1. rewrite <- H0.
        mlud; eauto. exfalso; eauto.
      }
      assert (eqMap (proj1_sig AE') (add x Top (proj1_sig AE))). {
        hnf; intros. mlud; eauto. rewrite <- e.
        rewrite <- H0. reflexivity.
      }
      simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
      econstructor; eauto.
      eapply IHLD with (AE:=(exist (add x Top (proj1_sig AE))
                     (cp_trans_domain ZL (stmtLet x (Call f Y) s) AE (getAnn sa)))); eauto.
      * split; eauto; simpl.
        etransitivity; eauto.
        etransitivity; eauto.
        symmetry; eauto.
      * pe_rewrite. set_simpl.
        eapply disj_incl; eauto with cset.
  - assert (MEQ: eqMap (proj1_sig AE')
    (getAE (@forward sT DDom (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s (subTerm_EQ_If1 eq_refl ST)
              (exist (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a))
              (setTopAnn sa
                 (if [op_eval (domenv (proj1_sig AE)) e = ⎣⎦] then false else if [
                  op_eval (domenv (proj1_sig AE)) e = ⎣ wTA val_false ⎦] then false else a))))). {
        hnf; intros.
        edestruct (@cp_forward_agree sT ZL (fst
                     (fst
                        (@forward sT DDom (@cp_trans_dep) (@cp_trans_reach) ZL ZLIncl s
                                  (subTerm_EQ_If1 eq_refl ST)
                           (exist (proj1_sig AE)
                              (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a))
                           (setTopAnn sa
                              (if [op_eval (domenv (proj1_sig AE)) e = ⎣⎦] then false else if [
                               op_eval (domenv (proj1_sig AE)) e =
                               ⎣ wTA val_false ⎦] then false else a)))))). eauto.
        eapply setTopAnn_annotation; eauto.
        instantiate (4:=singleton x) in H1. pe_rewrite.
        decide (x ∈ (Dt ∪ list_union (of_list ⊝ ZL))).
        -- edestruct (@cp_forward_agree sT ZL (exist (proj1_sig AE) (@cp_trans_domain sT ZL (stmtIf e s t) ST ZLIncl AE a)) (singleton x) s). eauto.
           eapply setTopAnn_annotation; eauto.
           pe_rewrite.
           assert ((x ∈ Dt /\ x ∉ list_union (of_list ⊝ ZL))
                   \/ (x ∈ list_union (of_list ⊝ ZL) /\ x ∉ Dt /\ x ∉ Ds)). {
             revert i DISJ H4.
             clear_all; cset_tac.
           } destruct H15; dcr.
           ++ exploit (H7 x).
             revert H17 H18 H3 i; clear_all. cset_tac.
             unfold domenv in H15.
             etransitivity; eauto.
           ++ etransitivity; eauto.
             eapply poLe_antisymmetric.
             eapply H14. revert H22; clear_all; cset_tac.
             etransitivity.
             eapply H1. revert H21; clear_all; cset_tac.
             exploit (H x).
             rewrite <- H15. unfold domenv. reflexivity.
        -- exploit (H0 x). revert n; clear_all. cset_tac.
           rewrite H7.
           etransitivity. eapply EQ2.
           symmetry. exploit (H x).
           rewrite <- H14.
           unfold domenv. reflexivity.
    }
    simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
    symmetry in HEQ. symmetry in HEQ0.
    rewrite <- (setTopAnn_eta _ HEQ0).
    rewrite <- (setTopAnn_eta _ HEQ).
    econstructor; eauto.
    + eapply IHLD1.
      * eauto.
      * eauto using setTopAnn_annotation.
      * eauto.
      * split.
        -- etransitivity.
           symmetry.
           eapply MEQ. simpl. eauto.
        -- eapply ann_R_setTopAnn_right; eauto.
           ++ rewrite forward_fst_snd_getAnn.
             rewrite getAnn_setTopAnn; eauto.
      * simpl. eauto.
      * pe_rewrite. clear MEQ. set_simpl.
        eapply disj_incl. eapply DISJ.
        eauto. eauto with cset.
      * eauto.
      * eauto.
      * eauto.
      * eauto.
    + eapply IHLD2; eauto.
      * eapply setTopAnn_annotation. eauto.
      * split.
        -- etransitivity; eauto.
           etransitivity; eauto.
           symmetry; eauto.
        -- etransitivity; eauto.
           eapply ann_R_setTopAnn_right; eauto.
      * clear MEQ.
        pe_rewrite. set_simpl.
        eapply disj_incl. eapply DISJ.
        reflexivity. eauto with cset.
  - econstructor.
  - clear_trivial_eqs. set_simpl.
    edestruct get_in_range; eauto.
    erewrite get_nth in *; eauto.
    inv_get.
    edestruct PIR2_nth; eauto using map_get_1, ListUpdateAt.list_update_at_get_3; dcr.
    econstructor; eauto using zip_get; intros.
    + PIR2_inv; clear_trivial_eqs; inv_get.
      eapply PIR2_get.
      * rewrite lookup_list_map.
        intros; inv_get.
        exploit (H0 x1) as EQA. unfold domenv.
        exploit (EQ2 x1) as EQB. rewrite <- EQA in EQB.
        rewrite EQB.
        cases.
        exploit domupd_list_get; [|eapply H6| eapply map_get_1; try eapply H5|].
        -- exploit NODUP; eauto.
        -- etransitivity;[| eapply H7].
           exploit eqMap_op_eval; try eapply EQ2.
           eapply option_R_inv in H8.
           unfold domenv in H8.
           rewrite H8. reflexivity.
      * rewrite map_length. rewrite lookup_list_length; eauto.
  -
    assert (ZipEq:((fun Zs0 : params * stmt => (fst Zs0, lookup_list (domenv (proj1_sig AE')) (fst Zs0))) ⊝ F ++ pair ⊜ ZL AV) = (zip pair (fst ⊝ F ++ ZL) ((fun Zs => lookup_list (domenv (proj1_sig AE')) (fst Zs)) ⊝ F ++ AV))). {
      clear_all. general induction F; simpl; eauto.
      f_equal. eapply IHF.
    }
    simpl_forward_setTopAnn. subst. repeat rewrite setTopAnn_eta' in *.
    assert (joinTopAnn (A:=bool) ⊜ sa (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t (subTerm_EQ_Fun1 eq_refl ST) AE ta)) = sa). {
      eapply PIR2_eq.
      eapply PIR2_R_impl. intros.
      eapply ann_R_eq. eapply H2.
      eapply snd_forwarF_inv; eauto.
      clear. eauto with len.
      rewrite forward_length. reflexivity.
      eapply PIR2_get in H23; eauto.
    }
    exploit eqMap_forwardF_t; eauto.
    clear. len_simpl. omega.
    reflexivity. pe_rewrite. set_simpl.
    eapply funConstr_disj_Dt'; eauto.
    pe_rewrite.
    rewrite list_union_defVars_decomp in *; eauto. set_simpl.
    eapply disj_Dt_getAnn; eauto.
    set_simpl.
    eapply funConstr_disj_ZL_getAnn; eauto.
    set_simpl.
    eapply disj_1_incl.
    eapply funConstr_disj_ZL_getAnn; eauto.
    rewrite List.map_app. rewrite list_union_app.
    clear_all. cset_tac.
    revert H9. clear_all. len_simpl. intros. rewrite H9. eauto with len.
    intros. inv_get. eapply setTopAnn_annotation. eauto.
    econstructor; eauto.
    + intros; inv_get.
      setoid_rewrite ZipEq.
      pose proof H16 as GET.
      assert (FWDP:forall STZs, PIR2 impb (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) (snd Zs) STZs AE r))
                                (snd
                                   (forwardF (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t ((subTerm_EQ_Fun1 eq_refl ST)) AE ta))
                                             (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl)) F
                                             (joinTopAnn (A:=bool) ⊜ sa
                                                         (snd (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) t ((subTerm_EQ_Fun1 eq_refl ST)) AE ta)))
                                             AE
                                             (subTerm_EQ_Fun2 eq_refl ST)))). {
        intros.
        eapply forwardF_PIR2.
        +++ revert H9. clear_all; intros; len_simpl.
           rewrite H9. eauto with len.
        +++ clear_all. eauto with len.
        +++ intros.
           inv_get.
           destruct H14.
           eapply H26; eauto.
           eapply zip_get; eauto.
        +++ eapply transf_ext.
        +++ eapply cp_trans_reach_ext.
        +++ rewrite H2. eauto.
        +++ eauto.
      }
      eapply H0;
        eauto.
      * clear_all; eauto with len.
      * split.
        -- eapply H14; eauto.
           rewrite H2; eauto.
        -- eapply PIR2_get in H23; eauto.
           exploit snd_forwarF_inv; eauto.
           clear; eauto with len.
           clear; eauto with len.
           exploit snd_forwarF_inv'; eauto.
           clear; eauto with len.
           clear; eauto with len.
           destruct H14.
           rewrite (@forwardF_ext sT DDom _
                                  (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (@ZLIncl_ext sT (stmtFun F t) F t ZL (@eq_refl stmt (stmtFun F t)) ST
                                                                                            ZLIncl)) (@forward _ _ (@cp_trans_dep) (@cp_trans_reach) (fst ⊝ F ++ ZL) (@ZLIncl_ext sT (stmtFun F t) F t ZL (@eq_refl stmt (stmtFun F t)) ST
                   ZLIncl))) in H20;
             try eapply e; intros; try reflexivity.
           eapply snd_forwarF_inv_get; try eapply H20; eauto.
           clear; eauto with len.
           clear; eauto with len.
           intros.
           eapply PIR2_nth_2 in H19; eauto; dcr.
           intros. eapply p; eauto.
           rewrite ann_R_eq in H27. subst. eauto.
           eapply forward_ext; eauto.
           eapply transf_ext; eauto.
           eapply cp_trans_reach_ext; eauto.
      * set_simpl. eauto.
        eapply disj_2_incl.
        eapply funConstr_disj_ZL_getAnn; eauto.
        eapply incl_list_union; eauto using zip_get.
      * revert LEN; clear_all; eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        clear_all.
        eauto with len.
      * intros ? ? GET2. eapply get_app_cases in GET2. destruct GET2.
        inv_get. edestruct H5; eauto.
        dcr. inv_get. eapply NODUP; eauto.
    + setoid_rewrite ZipEq.
      eapply IHLD; eauto.
      * clear; eauto with len.
      * split; dcr. eauto. eauto.
      * pe_rewrite. set_simpl.
        rewrite List.map_app. rewrite list_union_app.
        eapply disj_union_left.
        -- symmetry.
           eapply funConstr_disj_Dt; eauto.
        -- symmetry. eapply disj_incl; eauto.
      * revert LEN. clear; eauto with len.
      * rewrite List.map_app.
        eapply PIR2_app; eauto.
        eapply PIR2_get; intros; inv_get. reflexivity.
        clear.
        eauto with len.
      * intros ? ? GET. eapply get_app_cases in GET. destruct GET.
        inv_get. edestruct H5; eauto.
        dcr. inv_get. eapply NODUP; eauto.
        Grab Existential Variables.
        eapply subTerm_EQ_Fun2; eauto.
Qed.