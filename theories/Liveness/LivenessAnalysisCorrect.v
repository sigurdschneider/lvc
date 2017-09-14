Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Envs IL Annotation Infra.Lattice DecSolve Analysis Filter Terminating.
Require Import Analysis AnalysisBackward LivenessAnalysis TrueLiveness Subterm.
Require Import FiniteFixpointIteration.

Set Implicit Arguments.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments backward {sT} {Dom} btransform ZL AL st {ST} a.

Definition liveness_analysis_correct (i:overapproximation) sT ZL LV s a (ST:subTerm s sT)
  : ann_R poEq (@backward _ _ (liveness_transform_dep i) ZL LV s ST a) a
    -> annotation s a
    -> labelsDefined s (length ZL)
    -> labelsDefined s (length LV)
    -> paramsMatch s (length ⊝ ZL)
    -> true_live_sound i ZL (proj1_sig ⊝ LV) s
                      (mapAnn proj1_sig a).
Proof.
  intros EQ Ann DefZL DefLV PM.
  general induction Ann; simpl in *; inv DefZL; inv DefLV; inv PM; destruct a;
    clear_trivial_eqs.
  - pose proof (ann_R_get H7); simpl in *.
    econstructor.
    + eapply IHAnn; eauto.
    + intros.
      rewrite getAnn_mapAnn in H0.
      rewrite <- H in H0.
      cases in H2.
      eapply live_exp_sound_incl; [eapply Exp.live_freeVars|].
      rewrite <- H2. eapply incl_right.
    + intros.
      rewrite <- H2.
      simpl. rewrite getAnn_mapAnn.
      eapply incl_union_left.
      rewrite H. reflexivity.
  - econstructor; intros.
    + eapply IHAnn1; eauto.
    + eapply IHAnn2; eauto.
    + repeat cases in H9; try congruence.
      eapply live_op_sound_incl; [eapply Op.live_freeVars|].
      simpl. rewrite <- H9. eauto with cset.
    + rewrite getAnn_mapAnn. simpl.
      rewrite <- H9.
      eapply ann_R_get in H12. rewrite <- H12.
      eauto with cset.
    + rewrite getAnn_mapAnn. simpl.
      rewrite <- H9.
      eapply ann_R_get in H13. rewrite <- H13.
      eauto with cset.
  - edestruct (get_in_range _ H2) as [Z ?]; eauto.
    edestruct (get_in_range _ H3) as [[Lv ?] ?]; eauto.
    econstructor; eauto.
    + simpl. cases; eauto. rewrite <- H4.
      repeat erewrite get_nth; eauto.
      eapply incl_left.
    + simpl in *.
      erewrite get_nth in H4; eauto using map_get_1.
      erewrite get_nth in H4; eauto. simpl in *.
      eapply filter_by_incl_argsLive; eauto.
      inv_get; eauto.
      rewrite <- H4; eauto with cset.
    + inv_get; eauto.
  - econstructor.
    simpl in *. rewrite <- H1. eapply Op.live_freeVars.
  - simpl in *.
    econstructor.
    + rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- List.map_app.
      eapply (IHAnn i (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV)
             (subTerm_EQ_Fun1 eq_refl ST)); eauto.
      etransitivity; eauto.
      refine (@backward_ext sT (fun s => { x : ⦃var⦄ | x ⊆ occurVars s}) _
                            (liveness_transform_dep i)
                            (@liveness_transform_dep_ext i sT) _ _ _ _ _ _ _ _ _ _); eauto.
      eapply PIR2_app; eauto.
      eapply PIR2_get.
      * intros; inv_get.
        exploit H16; eauto.
      * len_simpl; eauto.
    + rewrite map_length. eauto.
    + intros. inv_get.
      rewrite map_map.
      erewrite map_ext with (l:=sa);[| intros; rewrite getAnn_mapAnn; reflexivity].
      rewrite <- map_map with (l:=sa). rewrite <- List.map_app.
      edestruct (@get_backwardF sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                                (liveness_transform_dep i))); eauto.
      eapply (H1 _ _ _ H3 H2 i (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV) x1); eauto.
    + intros. inv_get. cases; eauto.
      rewrite <- H13. eapply incl_union_left.
      edestruct (@get_backwardF sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                                (liveness_transform_dep i))); eauto.
      exploit H16; eauto.
      eapply incl_list_union. eapply zip_get. eapply Take.get_take; eauto using get_range.
      eapply map_get_1. eapply get_app_lt; eauto with len.
      eapply Take.get_take; eauto using get_range. eapply get_app_lt; eauto with len.
      rewrite getAnn_mapAnn.
      eapply ann_R_get in H9.
      eapply SigR.sig_R_proj1_sig in H9.
      rewrite H9. eauto.
    + rewrite getAnn_mapAnn.
      eapply ann_R_get in H17.
      rewrite <- H17.
      rewrite <- H13. cases; eauto with cset.
Qed.

Definition correct i s
  : paramsMatch s nil
    -> true_live_sound i nil nil s (livenessAnalysis i s).
Proof.
  intros.
  unfold livenessAnalysis.
  destr_sig. destr_sig. dcr.
  eapply (@liveness_analysis_correct i s nil nil s); eauto.
  eapply H2.
Qed.

(* For now, settle for occur vars;
   TODO: Show that the fixpoint is contained in freeVars (and union of Lv) *)
Lemma livenessAnalysis_getAnn i s
  : getAnn (livenessAnalysis i s) ⊆ occurVars s.
Proof.
  unfold livenessAnalysis. repeat destr_sig.
  rewrite getAnn_mapAnn. destr_sig; eauto.
Qed.


Require Import RenamedApart.

Lemma extend_incl sT ZL LV D Dt s ans sa
      (IFC:Indexwise.indexwise_R (funConstr D Dt) s ans)
      (Len: ❬s❭ = ❬sa❭) (Len2 : ❬s❭ = ❬ans❭)
      (LE:forall (n : nat) (a : ann ⦃var⦄) (b : ann (⦃var⦄ * ⦃var⦄)),
          get (mapAnn proj1_sig ⊝ sa) n a ->
          get ans n b -> ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) a b)
      (BND : forall (n : nat) (lv : {X : ⦃var⦄ | X ⊆ occurVars sT}) (Z : params),
          get ZL n Z -> get LV n lv -> proj1_sig lv \ of_list Z ⊆ D)
  : forall n x0 x2, get sa n x2 -> get ans n x0 -> forall (n0 : nat) (lv : {X : ⦃var⦄ | X ⊆ occurVars sT}) (Z : params),
                   get (fst ⊝ s ++ ZL) n0 Z -> get (getAnn ⊝ sa ++ LV) n0 lv
                   -> proj1_sig lv \ of_list Z ⊆ fst (getAnn x0).
  intros ? ? ? Get1 Get2 ? ? ? Get4 Get5.
  eapply get_app_cases in Get4; len_simpl; destruct Get4; dcr; inv_get.
  - edestruct IFC; eauto; dcr. rewrite H2.
    exploit LE as GET; eauto.
    eapply ann_R_get in GET. rewrite getAnn_mapAnn in GET.
    rewrite GET.
    edestruct IFC; try eapply H0; eauto; dcr.
    rewrite H4.
    clear; cset_tac.
  - rewrite get_app_ge in Get5; len_simpl; try rewrite <- Len in *; eauto with len.
    exploit BND; eauto.
    rewrite H2.
    edestruct IFC; eauto; dcr.
    rewrite H3. eauto with cset.
Qed.

Lemma extend_incl' i sT s t (ST:subTerm (stmtFun s t) sT) ZL LV D Dt ans sa
      (IFC:Indexwise.indexwise_R (funConstr D Dt) s ans)
      (Len: ❬s❭ = ❬sa❭) (Len2 : ❬s❭ = ❬ans❭)
      (LE:forall (n : nat) (a : ann ⦃var⦄) (b : ann (⦃var⦄ * ⦃var⦄)),
          get (mapAnn proj1_sig ⊝ sa) n a ->
          get ans n b -> ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) a b)
      (BND : forall (n : nat) (lv : {X : ⦃var⦄ | X ⊆ occurVars sT}) (Z : params),
          get ZL n Z -> get LV n lv -> proj1_sig lv \ of_list Z ⊆ D)
      (RA: forall (n : nat) (Zs : params * stmt) (a : ann (⦃var⦄ * ⦃var⦄)),
          get s n Zs -> get ans n a -> renamedApart (snd Zs) a)
      (IH:forall (n : nat) (s' : params * stmt) (sa' : ann {X : ⦃var⦄ | X ⊆ occurVars sT}),
          get sa n sa' ->
          get s n s' ->
          forall (i : overapproximation) (ZL : 〔params〕) (LV : 〔{X : ⦃var⦄ | X ⊆ occurVars sT}〕)
            (ST : subTerm (snd s') sT) (ra : ann (⦃var⦄ * ⦃var⦄)),
            renamedApart (snd s') ra ->
            labelsDefined (snd s') ❬ZL❭ ->
            labelsDefined (snd s') ❬LV❭ ->
            (forall (n0 : nat) (lv : {X : ⦃var⦄ | X ⊆ occurVars sT}) (Z : params),
                get ZL n0 Z -> get LV n0 lv -> proj1_sig lv \ of_list Z ⊆ fst (getAnn ra)) ->
            ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) (mapAnn proj1_sig sa') ra ->
            ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y)
                  (mapAnn proj1_sig (@backward _ _ (liveness_transform_dep i) ZL LV (snd s') ST sa')) ra)
      (LDef:forall (n : nat) (Zs : params * stmt), get s n Zs -> labelsDefined (snd Zs) (❬s❭ + ❬ZL❭))
      (LDef':forall (n : nat) (Zs : params * stmt), get s n Zs -> labelsDefined (snd Zs) (❬s❭ + ❬LV❭))
  :forall (n : nat) (lv : {X : ⦃var⦄ | X ⊆ occurVars sT}) (Z : params),
    get (fst ⊝ s ++ ZL) n Z ->
    get
      (getAnn
         ⊝ backwardF (backward (liveness_transform_dep i)) (fst ⊝ s ++ ZL) (getAnn ⊝ sa ++ LV) s sa
         (subTerm_EQ_Fun2 eq_refl ST) ++ LV) n lv -> proj1_sig lv \ of_list Z ⊆ D.
Proof.
  intros ? ? ? Get1 Get2.
  eapply get_app_cases in Get1; destruct Get1; dcr; inv_get.
  - rewrite get_app_lt in Get2; eauto with len. inv_get.
    edestruct (@backwardF_get sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                              (liveness_transform_dep i))); eauto; dcr; subst.
    exploit RA; eauto.
    exploit IH; try eapply H2. Focus 7.
    eapply ann_R_get in H3. rewrite getAnn_mapAnn in H3.
    rewrite H3. edestruct IFC; eauto; dcr.
    rewrite H4. repeat get_functional. clear; cset_tac.
    eauto. eauto. eauto. len_simpl.
    rewrite <- Len. eauto. eauto using extend_incl. eauto.
  - rewrite get_app_ge in Get2; eauto with len.
Qed.

Lemma live_ann_incl_ra  (i:overapproximation) sT ZL LV s a (ST:subTerm s sT) ra
      (RA:renamedApart s ra)
      (Ann:annotation s a)
      (DefZL:labelsDefined s (length ZL))
      (DefLV:labelsDefined s (length LV))
      (BND:forall n lv Z, get ZL n Z -> get LV n lv -> proj1_sig lv \ of_list Z ⊆ fst (getAnn ra))
      (LE:ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) (mapAnn proj1_sig a) ra)
  : ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) (mapAnn proj1_sig (@backward _ _ (liveness_transform_dep i) ZL LV s ST a)) ra.
Proof.
  general induction Ann; invt renamedApart;
    invt @ann_R; inv DefZL; inv DefLV; simpl; econstructor; simpl; eauto;
    simpl in *.
  - exploit (IHAnn i ZL LV) as IH; eauto.
    + intros; pe_rewrite. rewrite BND; eauto with cset.
    + eapply ann_R_get in IH. rewrite getAnn_mapAnn in IH.
      cases; erewrite IH; pe_rewrite; try rewrite H3;
        revert H2; clear; cset_tac.
  - eapply IHAnn; eauto.
    + intros. pe_rewrite. rewrite BND; eauto with cset.
  - exploit (IHAnn1 i ZL LV) as IH1; eauto.
    + intros. pe_rewrite. rewrite BND; eauto with cset.
    + eapply ann_R_get in IH1. rewrite getAnn_mapAnn in IH1.
      exploit (IHAnn2 i ZL LV) as IH2; eauto.
      * intros. pe_rewrite. rewrite BND; eauto with cset.
      * eapply ann_R_get in IH2. rewrite getAnn_mapAnn in IH2.
        rewrite H2, IH1, IH2. pe_rewrite.
        clear_all. cset_tac.
  - eapply IHAnn1; eauto.
    + intros. pe_rewrite. rewrite BND; eauto with cset.
  - eapply IHAnn2; eauto.
    + intros. pe_rewrite. rewrite BND; eauto with cset.
  - edestruct (get_in_range _ H5) as [Z ?]; eauto.
    edestruct (get_in_range _ H6) as [[Lv ?] ?]; eauto.
    repeat erewrite get_nth; eauto.
    rewrite list_union_incl with (s':=D); only 3: eauto with cset.
    + cases; eauto with cset.
    + intros; inv_get. rewrite <- H1.
      eapply incl_list_union; eauto using get.
  - exploit (IHAnn i) as IH; try eapply H8; try assumption. eauto.
    Focus 3.
    eapply ann_R_get in IH. rewrite getAnn_mapAnn in IH.
    rewrite IH.
    pe_rewrite. cases; [| eauto with cset].
    eapply union_incl_split; eauto.
    eapply list_union_incl; only 2: eauto with cset; intros; inv_get.

    rewrite get_app_lt in H3; [| eauto with len].
    inv_get.

    edestruct (@backwardF_get sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                              (liveness_transform_dep i))); eauto; dcr; subst.
    exploit H5; eauto.
    exploit H1 as IH'; try eapply H15.
    Focus 7.
    eapply ann_R_get in IH'. rewrite getAnn_mapAnn in IH'.
    rewrite IH'.
    edestruct H6; eauto; dcr.
    rewrite H23. repeat get_functional. clear; cset_tac.
    eauto. eauto. eauto. eauto. eauto using extend_incl.
    eapply H17; eauto. eauto. eauto with len.
    pe_rewrite. eapply extend_incl'; eauto.
  - eauto with len.
  - intros; inv_get.
    edestruct (@backwardF_get sT _ (@backward _ (fun s0 : stmt => {x1 : ⦃var⦄ | x1 ⊆ occurVars s0})
                                              (liveness_transform_dep i))); eauto; dcr; subst.
    eapply H1; eauto using extend_incl.
  - eapply IHAnn; eauto with len.
    pe_rewrite. eapply extend_incl'; eauto.
Qed.

Lemma renamedApart_annotation s ang
: renamedApart s ang
  -> annotation s ang.
Proof.
  intros. general induction H; eauto 20 using @annotation.
Qed.

Lemma livenessAnalysis_renamedApart_incl i s ra
      (RA:renamedApart s ra) (LD:labelsDefined s 0)
  : ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x ⊆ fst y) (livenessAnalysis i s) ra.
Proof.
  unfold livenessAnalysis.
  eapply safeFixpoint_induction; intros.
  - clear LD.
    unfold initial_value. simpl.
    generalize (occurVars s).
    general induction RA; simpl; econstructor; simpl; set_simpl; eauto with cset len.
    intros; inv_get. eapply H1; eauto.
  - intros. simpl. destruct a; simpl.
    eapply live_ann_incl_ra; eauto.
    isabsurd.
Qed.
