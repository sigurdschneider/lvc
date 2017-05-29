Require Import Util SizeInduction Get MapDefined Coq.Classes.RelationClasses.
Require Import IL Var Val OptionR AllInRel.
Require Import CMap CMapDomain CMapPartialOrder CMapJoinSemiLattice.
Require Import Analysis AnalysisForwardSSA Subterm CSet MapAgreement RenamedApart.
Require Import Infra.PartialOrder Infra.Lattice Infra.WithTop.
Require Import LabelsDefined Annotation.
Require Import Reachability ReachabilityAnalysisCorrectSSA.
Require Import ConstantPropagation ConstantPropagationAnalysis DomainSSA.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {D} {H} {H0} exp_transf reach_transf ZL ZLIncl st ST d anr.

Notation "'getAE' X" := (proj1_sig (fst (fst X))) (at level 10, X at level 0).

Local Arguments exist {A} {P} x _.

Lemma domenv_map_proper D `{PartialOrder D} Z
  : Proper (poEq ==> poEq) (fun AE => domenv AE ⊝ Z).
Proof.
  unfold Proper, respectful; intros.
  general induction Z; simpl; eauto using poEq_list_struct.
Qed.


Lemma domjoin_list_domenv D `{JoinSemiLattice D} Z (Y:list (option D)) AE
  (ND : NoDupA eq Z)
  (LEN : ❬Z❭ = ❬Y❭)
  : Y ⊑ domenv (domjoin_list AE Z Y) ⊝ Z.
Proof.
  general induction LEN; simpl; eauto.
  eapply poLe_list_struct.
  - unfold domenv at 1.
    rewrite domupd_var_eq; eauto.
  - eapply PIR2_get; eauto with len.
    intros; inv_get.
    unfold domenv. rewrite domupd_var_ne; eauto.
    exploit IHLEN; eauto.
    + eapply PIR2_nth in H3; eauto; dcr; inv_get.
      eapply H6.
    + intro EQ; invc EQ. inv ND. eapply H5.
      eapply get_InA in H2. eauto.
Qed.

Definition cp_sound sT AE ZL s (ST:subTerm s sT) ZLIncl ra anr
  : let X := @forward sT _ _ _ (@cp_trans) (@cp_reach) ZL ZLIncl s ST AE anr in
    renamedApart s ra
    -> annotation s anr
    -> labelsDefined s (length ZL)
    -> poEq (fst X) (AE,anr)
    -> disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra))
    -> paramsMatch s (length ⊝ ZL)
    -> (forall n Z, get ZL n Z -> NoDupA eq Z)
    -> cp_sound (domenv (proj1_sig AE))
               (zip pair ZL (lookup_list (domenv (proj1_sig AE)) ⊝ ZL)) s anr.
Proof.
  intros LET RA ANN LD EQ1 DISJ PM NODUP. subst LET.
  general induction LD; invt @renamedApart;
    try invt @annotation; simpl in *; simpl; invt @paramsMatch;
      simpl in *; dcr;
        repeat let_pair_case_eq; repeat let_case_eq; repeat simpl_pair_eqs; subst;
          simpl in *; try invtc @ann_R; subst.
  - set_simpl. clear_trivial_eqs.
    + pose proof EQ1 as EQ3.
      eapply forward_domupdd_eq in EQ3; eauto.
      * econstructor; eauto.
        eapply IHLD; eauto.
        split; simpl. rewrite <- EQ1 at 2.
        eapply forward_ext; eauto using cp_trans_ext, cp_reach_ext.
        rewrite <- EQ3. symmetry; eauto.
        rewrite <- H10 at 2.
        eapply forward_ext; eauto using cp_trans_ext, cp_reach_ext.
        rewrite <- EQ3. symmetry; eauto.
        pe_rewrite. eauto with cset.
        intros.
        rewrite EQ1 in EQ3.
        specialize (EQ3 x). unfold domenv.
        eapply option_R_inv in EQ3.
        rewrite EQ3. simpl. rewrite domupd_var_eq; try reflexivity.
      * rewrite renamedApart_occurVars; eauto. pe_rewrite.
        eapply renamedApart_disj in H4; eauto.
        pe_rewrite. revert DISJ H4; clear_all; cset_tac.
  - clear_trivial_eqs.
    set_simpl.
    exploit (forward_if_inv _ _ _ _ _ _ EQ1); eauto.
    repeat rewrite renamedApart_occurVars; eauto;
      pe_rewrite; eauto with cset.
    repeat rewrite renamedApart_occurVars; eauto;
      pe_rewrite; eauto with cset.
    rewrite forward_ext in EQ1; eauto using cp_reach_ext, cp_trans_ext; try reflexivity.
    econstructor; eauto.
    + eapply IHLD1; eauto.
      split; eauto. pe_rewrite. eauto with cset.
    + eapply IHLD2; eauto.
      split; eauto.
      rewrite forward_ext; eauto using cp_reach_ext, cp_trans_ext. symmetry; eauto.
      pe_rewrite. eapply disj_2_incl; eauto with cset.
  - econstructor; eauto.
  - inv_get.
    econstructor; eauto using zip_get_eq.
    intros. cases in EQ1. inv_get.
    set_simpl.
    unfold domjoin_listd in EQ1.
    destruct AE as [AE pf]; simpl in *; clear_trivial_eqs.
    unfold poEq in EQ1. simpl in EQ1.
    rewrite (get_nth nil H3) in *.
    exploit NODUP; eauto.
    rewrite lookup_list_map.
    symmetry in EQ1.
    rewrite domenv_map_proper; eauto.
    eapply domjoin_list_domenv; eauto with len.
  - clear_trivial_eqs.
    eapply PIR2_get in H21; try eassumption. clear H20.
    exploit (snd_forwardF_inv _ _ _ _ _ _ _ H21); eauto with len.
    exploit (snd_forwardF_inv' _ _ _ _ _ _ _ H21); eauto with len.
    Transparent poEq. simpl poEq in H21.
    repeat PIR2_eq_simpl. repeat ST_pat.
    Opaque poEq.
    set (FWt:=(forward cp_trans cp_reach (fst ⊝ F ++ ZL) ZLIncl0 t ST0 AE ta)) in *.
    set (FWF:=forwardF (snd FWt) (forward cp_trans cp_reach (fst ⊝ F ++ ZL) ZLIncl0)
                       F sa (fst (fst FWt)) STF) in *.
    assert (fst (fst (FWt)) ≣ AE /\
            forall (n : nat) (Zs : params * stmt) (r : ann bool) (ST0 : subTerm (snd Zs) sT),
              get F n Zs ->
              get sa n r ->
              fst
                (fst
                   (forward cp_trans cp_reach (fst ⊝ F ++ ZL) (ZLIncl_ext ZL eq_refl ST ZLIncl) (snd Zs) ST0 AE r))
                ≣ AE). {
      pe_rewrite. set_simpl.
      eapply forwardF_agree_get; eauto. eauto with len.
      rewrite <- EQ1. unfold FWF. reflexivity.
      unfold FWt. reflexivity.
      pe_rewrite. eauto with ren.
      pe_rewrite.
      eapply disj_Dt_getAnn; eauto.
      eapply funConstr_disj_ZL_getAnn; eauto.
      eapply disj_1_incl.
      eapply funConstr_disj_ZL_getAnn; eauto.
      rewrite List.map_app. rewrite list_union_app.
      clear_all. cset_tac.
      eapply cp_trans_ext. eapply cp_reach_ext.
    } dcr.

    assert (forall (n : nat) (r : ann bool) (Zs : params * stmt),
       get sa n r ->
       get F n Zs ->
       forall STZs : subTerm (snd Zs) sT,
         (snd
            (fst
               (forward cp_trans cp_reach (fst ⊝ F ++ ZL)
                        ZLIncl0 (snd Zs) STZs AE r))) ≣ r). {
      eapply (@snd_forwardF_inv_get) with (BL:=(snd FWt)); eauto.
      subst FWt; eauto with len.
      subst FWt; eauto with len.
      rewrite <- H2 at 2. unfold FWF.
      rewrite forwardF_ext'; try reflexivity; eauto.
      eapply cp_trans_ext; eauto.
      eapply cp_reach_ext; eauto.
      symmetry; eauto.
      eapply cp_trans_ext; eauto.
      eapply cp_reach_ext; eauto.
    }
    econstructor; eauto.
    + intros. inv_get. exploit H7; eauto.
      assert (EQ:
                ((fun Zs0 : params * stmt =>
      (fst Zs0, lookup_list (domenv (proj1_sig AE)) (fst Zs0))) ⊝ F ++
     pair ⊜ ZL (lookup_list (domenv (proj1_sig AE)) ⊝ ZL))
              = zip pair (fst ⊝ F ++ ZL) (lookup_list (domenv (proj1_sig AE)) ⊝ (fst ⊝ F ++ ZL))). {
        rewrite !List.map_app. rewrite !zip_app; eauto with len.
        rewrite !zip_map_l. rewrite !zip_map_r.
        f_equal; eauto.
        clear_all. general induction F; simpl; f_equal; eauto.
      }
      rewrite EQ.
      eapply H0; eauto.
      -- eauto with len.
      -- split; simpl; eauto.
      -- set_simpl.
         eapply disj_2_incl.
         eapply funConstr_disj_ZL_getAnn; eauto with ren.
         eapply incl_list_union; eauto using zip_get.
      -- intros ? ? GET2. eapply get_app_cases in GET2. destruct GET2.
         inv_get. edestruct H5; eauto.
         dcr. inv_get. eapply NODUP; eauto.
    + assert (EQ:
                (fun Zs : params * stmt => (fst Zs, lookup_list (domenv (proj1_sig AE)) (fst Zs)))
                  ⊝ F ++ pair ⊜ ZL (lookup_list (domenv (proj1_sig AE)) ⊝ ZL)
                = zip pair (fst ⊝ F ++ ZL) (lookup_list (domenv (proj1_sig AE)) ⊝ (fst ⊝ F ++ ZL))). {
        rewrite !List.map_app. rewrite !zip_app; eauto with len.
        rewrite !zip_map_l. rewrite !zip_map_r.
        f_equal; eauto.
        clear_all. general induction F; simpl; f_equal; eauto.
      }
      rewrite EQ.
      eapply IHLD; eauto with len.
      * split; simpl; eauto.
      * pe_rewrite. set_simpl.
        rewrite List.map_app. rewrite list_union_app.
        eapply disj_union_left.
        -- symmetry.
           eapply funConstr_disj_Dt; eauto.
        -- symmetry. eapply disj_incl; eauto.
      * intros ? ? GET2. eapply get_app_cases in GET2. destruct GET2.
        inv_get. edestruct H5; eauto.
        dcr. inv_get. eapply NODUP; eauto.
        Grab Existential Variables.
        eauto.
Qed.

Definition cp_reachability_sound (sT:stmt)
           ZL BL s (d:VDom (occurVars sT) _) r (ST:subTerm s sT) ZLIncl
           (EQ:(fst (forward cp_trans cp_reach ZL ZLIncl s ST d r)) ≣ (d,r)) ra
    (Ann: annotation s r) (RA:renamedApart s ra)
    (DefZL: labelsDefined s (length ZL))
    (DefBL: labelsDefined s (length BL))
    (BL_le: poLe (snd (forward cp_trans cp_reach ZL ZLIncl s ST d r)) BL)
    (Disj:disj (list_union (of_list ⊝ ZL)) (snd (getAnn ra)))
  : reachability (cop2bool (domenv (proj1_sig d))) Sound BL s r.
Proof.
  eapply reachability_sound with (pr:=fun d => cop2bool (domenv (proj1_sig d)));
    eauto using cp_trans_ext, cp_reach_ext.
  - unfold cp_reach, cop2bool, Dom; intros;
      repeat cases; simpl in *; unfold Dom in *; clear_trivial_eqs; eauto.
    + exfalso. eapply H. rewrite COND; simpl. eauto.
    + exfalso. eapply H. rewrite COND; simpl. eauto.
    + exfalso. eapply H. rewrite COND; simpl. eauto.
  - unfold cp_reach, cop2bool, Dom; intros;
      repeat cases; simpl in *; unfold Dom in *; clear_trivial_eqs; eauto.
    + exfalso. eapply H. rewrite COND; simpl. eauto.
    + exfalso. eapply H. rewrite COND0; simpl. eauto.
    + exfalso. eapply H. rewrite COND; simpl. eauto.
Qed.