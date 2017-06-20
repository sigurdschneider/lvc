Require Import Util CSet Map LengthEq.
Require Import Env IL Alpha StableFresh Subset1 OptionR.
Require Import Annotation AnnP RenamedApart RenameApart SetOperations Take.
Require Import LabelsDefined PairwiseDisjoint Liveness.Liveness Coherence Restrict.

Set Implicit Arguments.

Local Hint Immediate incl_union_incl : cset.

Lemma lv_ra_lv_bnd ZL Lv lv ra VD s
      (aIncl:ann_R (fun (x : ⦃var⦄) (y : ⦃var⦄ * ⦃var⦄) => x [<=] fst y) lv ra)
      (LV:live_sound Imperative ZL Lv s lv)
      (RA:renamedApart s ra)
      (Incl:fst (getAnn ra) ∪ snd (getAnn ra) ⊆ VD)
  : ann_P (fun lv0 : ⦃var⦄ => lv0 [<=] VD) lv.
Proof.
  general induction aIncl; invt live_sound; invt renamedApart;
    econstructor; simpl in *;
      try (rewrite <- Incl; eauto with cset); pe_rewrite; set_simpl.
  - eapply IHaIncl; eauto.
    rewrite <- Incl. clear; cset_tac.
  - eapply IHaIncl1; eauto.
    rewrite <- Incl. clear; cset_tac.
  - eapply IHaIncl2; eauto.
    rewrite <- Incl. clear; cset_tac.
  - intros. inv_get. eapply H2; eauto.
    edestruct H15; eauto; dcr. rewrite H8.
    rewrite <- Incl.
    rewrite <- incl_list_union; eauto using zip_get;[|reflexivity].
    unfold defVars. clear; cset_tac.
  - eapply IHaIncl; eauto.
    rewrite <- Incl. clear; cset_tac.
Qed.

Definition renameApartF_live (fresh:StableFresh)
           (renameApart_live:StableFresh -> env var -> set var -> stmt -> ann (set var) -> set var * ann (set var)) G ϱ :=
  (fix f (N:set var) (F:list (params*stmt)) (anF:list (ann (set var))) :=
     match F, anF with
     | Zs::F, a::anF =>
       let Y := fst (fresh_list_stable fresh (N ∪ G) (fst Zs)) in
       let ϱZ := ϱ [ fst Zs <-- Y ] in
       let (N', alv') := renameApart_live fresh ϱZ (G ∪ N ∪ of_list Y) (snd Zs) a in
       let (anF', N'') := f (N' ∪ of_list Y ∪ N) F anF in
       (setTopAnn alv' (getAnn alv' ∪ of_list Y)::anF', N'')
     | _, _ => (nil, N)
     end).


Fixpoint renameApart_live (fresh:StableFresh) (ϱ:env var) (G:set var) (s:stmt) (alv:ann (set var))
  : set var * ann (set var) :=
  match s, alv with
  | stmtLet x e s0, ann1 lv alv =>
    let y := fresh G x in
    let ϱ' := ϱ[x <- y] in
    let (G', alv') := renameApart_live fresh ϱ' {y; G} s0 alv in
    ({y; G'}, ann1 (lookup_set ϱ lv) alv')
  | stmtIf e s1 s2, ann2 lv alv1 alv2 =>
    let (G', alv1') := renameApart_live fresh ϱ G s1 alv1 in
    let (G'', alv2') := renameApart_live fresh ϱ (G ∪ G') s2 alv2 in
    (G' ∪ G'', ann2 (lookup_set ϱ lv) alv1' alv2')
  | stmtApp l Y, ann0 lv => (∅, ann0 (lookup_set ϱ lv))
  | stmtReturn e, ann0 lv => (∅, ann0 (lookup_set ϱ lv))
  | stmtFun F s2, annF lv anF alv2 =>
    let (anF', G') := renameApartF_live fresh renameApart_live G ϱ ∅ F anF in
    let (G'', alv2') := renameApart_live fresh ϱ (G ∪ G') s2 alv2 in
    (G' ∪ G'', annF (lookup_set ϱ lv) anF' alv2')
  | _ , _ => (∅, alv)
  end.

Lemma getAnn_snd_renameApart_live fresh o ZL LV ϱ G s lv
  : live_sound o ZL LV s lv
    -> getAnn (snd (renameApart_live fresh ϱ G s lv)) = lookup_set ϱ (getAnn lv).
Proof.
  intros LS; inv LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.


Lemma snd_renameApartF_live fresh als L X G ϱ F (Len:❬F❭ = ❬als❭)
      (IH:forall n Zs a, get F n Zs -> get als n a ->
                    forall (ϱ : env var) (G : ⦃var⦄),
                      fst (renameApart_live fresh ϱ G (snd Zs) a) = fst (renameApart' fresh ϱ G (snd Zs)))
  : snd (renameApartF_live fresh renameApart_live G ϱ X F als) =
    snd (renameApartF fresh renameApart' G ϱ F (L, X)).
Proof.
  length_equify.
  general induction Len.
  - eauto.
  - simpl. repeat let_pair_case_eq;simpl; subst.
    unfold renameApartFStep.
    repeat let_pair_case_eq; simpl; subst; eauto. simpl.
    erewrite <- IHLen; eauto using get.
    erewrite <- IH; eauto using get.
Qed.


Lemma fst_renameApart_live fresh o ZL LV ϱ G s lv
  : live_sound o ZL LV s lv
    -> fst (renameApart_live fresh ϱ G s lv) = fst (renameApart' fresh ϱ G s).
Proof.
  intros LS.
  general induction LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite IHLS; eauto.
  - rewrite IHLS1, IHLS2; eauto.
  - erewrite snd_renameApartF_live; eauto.
    f_equal; eauto.
Qed.


Lemma renameApartF_live_length fresh G G' ϱ F anF (Len:❬F❭ = ❬anF❭)
: length (fst (renameApartF_live fresh renameApart_live G ϱ G' F anF)) = length F.
Proof.
  length_equify.
  general induction Len; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.

Smpl Add match goal with
         | [ H : context [ ❬fst (renameApartF_live ?fresh ?renameApart' ?G ?ϱ ?s ?F ?anF)❭ ] |- _ ] =>
           rewrite (@renameApartF_live_length fresh G s ϱ F anF) in H
         | [ |- context [ ❬fst (renameApartF_live ?fresh ?renameApart' ?G ?ϱ ?s ?F ?anF)❭ ] ] =>
           rewrite (@renameApartF_live_length fresh G s ϱ F anF)
         end : len.

Lemma get_fst_renameApartF_live fresh G G' ϱ F n anF ans
  (Get: get (fst (renameApartF_live fresh renameApart_live G ϱ G' F anF)) n ans)
  (Len:❬F❭=❬anF❭)
  :  exists Zs a  G'' (Y:list var) ans',
    get F n Zs /\ get anF n a
    /\ ans' = snd (renameApart_live fresh (ϱ [fst Zs <-- Y]) G'' (snd Zs) a) /\
    ans = setTopAnn ans' (getAnn ans' ∪ of_list Y)/\
    G'' = G ∪ snd (renameApartF_live fresh renameApart_live G ϱ G' (take n F) (take n anF))
            ∪ of_list Y
    /\ Y = (fresh_list_stable fresh (snd (renameApartF_live fresh renameApart_live G ϱ G' (take n F) (take n anF)) ∪ G) (fst Zs)).
Proof.
  length_equify.
  general induction Len; simpl in * |- *; [ isabsurd |].
  - revert Get; let_pair_case_eq; simpl_pair_eqs; subst; intros Get.
    revert Get; let_pair_case_eq; simpl_pair_eqs; subst; intros Get. simpl in *.
    inv Get.
    + eexists x, y; eauto 100 using get.
    + edestruct IHLen as [? [? ?]]; dcr; subst; eauto 20 using get.
      subst.
      do 5 eexists; split; [| split]; eauto 100 using get.
      split. reflexivity. simpl.
      repeat let_pair_case_eq; repeat simpl_pair_eqs; subst. simpl.
      split.
      reflexivity. split; reflexivity.
Qed.

Tactic Notation "orewrite" constr(A) "all" :=
  let X := fresh "OX" in assert A as X by omega; rewrite X in *; clear X.

Lemma renameApart_live_sound fresh ZL LV ZL' LV' s lv ϱ G
      (LenZL:❬ZL❭ = ❬ZL'❭) (LenLV:❬LV❭=❬LV'❭)
      (ParamLen:forall n Z Z', get ZL n Z -> get ZL' n Z' -> ❬Z❭ = ❬Z'❭)
  : live_sound Functional ZL LV s lv
    -> live_sound Functional ZL' LV'
                 (snd (renameApart' fresh ϱ G s))
                 (snd (renameApart_live fresh ϱ G s lv)).
Proof.
  intros LS.
  general induction LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - econstructor; eauto using live_exp_rename_sound.
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite lookup_set_update_union_minus_single; eauto.
      rewrite <- H0. eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto.
      lset_tac. eexists x; lud; eauto.
  - econstructor; eauto using live_op_rename_sound.
    + erewrite fst_renameApart_live; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
  - inv_get. exploit ParamLen; eauto.
    econstructor; eauto with len.
    intros; inv_get; eauto using live_op_rename_sound.
  - econstructor; eauto using live_op_rename_sound.
  - econstructor; eauto.
    + erewrite snd_renameApartF_live; eauto.
      * eapply IHLS; eauto.
        -- rewrite !app_length, !map_length, rev_length, renameApartF_length; eauto.
        -- rewrite !app_length, !map_length, renameApartF_live_length; eauto.
        -- intros; inv_get.
           eapply get_app_cases in H4; destruct H4.
           ++ rewrite get_app_lt in H5; inv_get; len_simpl.
             edestruct (get_fst_renameApartF fresh _ _ _ H5)
               as [? [? ?]]; eauto; dcr.
             assert (n < ❬F❭) by eauto using get_range.
             orewrite (❬F❭ - S (❬F❭ - S n) = n) in H9.
             get_functional; eauto. eauto with len.
           ++ dcr. rewrite get_app_ge in H5; eauto with len.
      * intros. erewrite fst_renameApart_live; eauto.
    + eauto with len.
    + intros; inv_get.
      edestruct (get_fst_renameApartF _ _ _ _ H4) as [? [? ?]];
        eauto; dcr.
      rewrite H7.
      edestruct (get_fst_renameApartF_live _ _ _ _ _ _ H5); eauto; dcr; subst.
      rewrite renameApartF_length in H8.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n) in H8. get_functional.
      rewrite H16.
      rewrite drop_rev.
      rewrite renameApartFRight_corr.
      erewrite <- snd_renameApartF_live.
      rewrite renameApartF_length. rewrite rev_rev. rewrite rev_length.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      eapply live_sound_monotone2.
      eapply H1; eauto.
      revert LenZL; clear; eauto with len.
      revert H LenLV; clear; eauto with len.
      -- intros ? ? ? GetA GetB; inv_get.
         eapply get_app_cases in GetA; destruct GetA.
         ++ rewrite get_app_lt in GetB; inv_get.
           edestruct (get_fst_renameApartF _ _ _ _ GetB) as [? [? ?]];
             eauto; dcr. subst.
           rewrite renameApartF_length in H21.
           assert (n0 < ❬F❭) by eauto using get_range.
           orewrite (❬F❭ - S (❬F❭ - S n0) = n0) in H21. get_functional. eauto.
           rewrite map_length, rev_length, renameApartF_length; eauto using get_range.
         ++ dcr. rewrite get_app_ge in GetB; eauto with len.
      -- eauto with cset.
      -- rewrite rev_length, renameApartF_length, rev_rev.
         assert (n < ❬F❭) by eauto using get_range.
         orewrite (❬F❭ - S (❬F❭ - S n) = n).
         repeat rewrite take_length_le; eauto; omega.
      -- intros. inv_get. len_simpl.
         assert (n0 < ❬F❭) by eauto using get_range.
         orewrite (❬F❭ - S (❬F❭ - S n0) = n0) all.
         exploit H0; try eapply H15; eauto.
         erewrite fst_renameApart_live; eauto.
    + intros ? ? ? GetA GetB; inv_get; simpl.
      edestruct (get_fst_renameApartF _ _ _ _ GetA) as [? [? ?]];
        eauto; dcr; subst.
      rewrite H14.
      edestruct (get_fst_renameApartF_live _ _ _ _ _ _ GetB);
        eauto; dcr; subst.
      erewrite getAnn_snd_renameApart_live; eauto.
      exploit H2; eauto; dcr. simpl in H19.
      rewrite renameApartF_length in H6.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n) in H6.
      get_functional.
      rewrite renameApartF_length.
      rewrite drop_rev.
      rewrite rev_rev. rewrite rev_length.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      rewrite renameApartFRight_corr.
      erewrite <- (@snd_renameApartF_live _ (take n als)).
      split.
      rewrite getAnn_setTopAnn. eauto with cset.
      rewrite getAnn_setTopAnn.
      split.
      eapply fresh_list_stable_nodup; eauto.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      rewrite H19. clear. cset_tac. eauto with len.
      rewrite take_length; eauto with len.
      -- intros. inv_get.
         exploit H0; eauto.
         erewrite fst_renameApart_live; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
Qed.

Lemma renameApart_live_sound_srd b fresh o DL ZL LV (ZL':list params) LV' s lv ϱ G
      (ParamLen:forall n Z Z', get ZL n Z -> get ZL' n Z' -> ❬Z❭ = ❬Z'❭)
  (LS: live_sound o ZL LV s lv)
  (SRD:srd DL s lv)
  (iEQ:PIR2 (ifFstR Equal) DL (LV \\ ZL))
  (iEQ':PIR2 (ifFstR Equal) (option_map (fun (s:set var) => map ϱ s) ⊝ DL) (LV' \\ ZL'))
  (NUC:noUnreachableCode (isCalled b) s)
  (LenZL:❬ZL❭ = ❬ZL'❭) (LenLV:❬LV❭=❬LV'❭) (LenDL:❬DL❭=❬ZL❭) (LenLV2:❬LV❭=❬ZL❭)
  (Incl:map ϱ (getAnn lv) ⊆ G) (isImp:isImperative o)
  : live_sound o ZL' LV' (snd (renameApart' fresh ϱ G s)) (snd (renameApart_live fresh ϱ G s lv)).
Proof.
  general induction LS; invt srd; invt noUnreachableCode; simpl;
    repeat let_pair_case_eq; simpl; subst; eauto.
  - econstructor; eauto 20 using live_exp_rename_sound, restrict_ifFstR.
    + eapply IHLS; eauto using live_exp_rename_sound, restrict_ifFstR with len.
      eapply PIR2_get.
      * intros; inv_get. unfold restr; repeat (cases; simpl); eauto using @ifFstR.
        edestruct PIR2_nth as [? [? iF]]; eauto; invc iF; inv_get.
        econstructor. rewrite <- H11. revert COND; clear.
        cset_tac'. lud; cset_tac'. eexists x0; lud; eauto.
      * len_simpl. rewrite min_l; try omega.
      * simpl in *. rewrite <- Incl at 3.
        revert H0; clear; cset_tac'; lud; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite lookup_set_update_union_minus_single; eauto.
      rewrite <- H0. eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto.
      lset_tac. eexists x; lud; eauto.
  - simpl in *.
    econstructor; eauto using live_op_rename_sound, restrict_ifFstR.
    + eapply IHLS1; eauto with cset.
    + erewrite fst_renameApart_live; eauto.
      eapply IHLS2; eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
  - inv_get. exploit ParamLen; eauto.
    econstructor; eauto with len.
    + cases; cases in H1; eauto.
      edestruct PIR2_nth as [? [? iF]]; eauto using zip_get; invc iF; inv_get.
      edestruct PIR2_nth as [? [? iF]]; try eapply iEQ; eauto using zip_get; invc iF; inv_get.
      rewrite <- H10, H11. rewrite map_incl; eauto with cset.
    + intros; inv_get; eauto using live_op_rename_sound.
  - econstructor; eauto using live_op_rename_sound.
  - econstructor; eauto.
    + erewrite snd_renameApartF_live; eauto.
      * eapply IHLS; eauto using restrict_ifFstR.
        -- intros; inv_get.
           eapply get_app_cases in H4; destruct H4.
           ++ rewrite get_app_lt in H5; inv_get.
             edestruct (get_fst_renameApartF _ _ _ _ H5) as [? [? ?]]; eauto; dcr.
             rewrite renameApartF_length in H14.
             assert (n < ❬F❭) by eauto using get_range.
             orewrite (❬F❭ - S (❬F❭ - S n) = n) in H14. get_functional. eauto.
             rewrite map_length, rev_length, renameApartF_length;
               eauto using get_range.
           ++ dcr. rewrite get_app_ge in H5; eauto with len.
        -- rewrite zip_app;[| eauto with len].
           eauto using PIR2_app, PIR2_ifFstR_refl.
        -- rewrite !zip_app, List.map_app;[| eauto with len].
           apply PIR2_app; eauto with len.
           eapply PIR2_get; intros; inv_get; simpl; [|eauto with len].
           econstructor. len_simpl. destruct x2 as [Z s], x as [Z' s'].
           exploit H0; eauto.
           edestruct (get_fst_renameApartF _ _ _ _ H5) as [? [? ?]]; eauto; dcr.
           edestruct (get_fst_renameApartF_live _ _ _ _ _ _ H10); eauto; dcr; subst.
           assert (n < ❬F❭) by eauto using get_range.
           orewrite (❬F❭ - S (❬F❭ - S n) = n) in H16. get_functional.
           inv_get.
           rewrite getAnn_setTopAnn. erewrite getAnn_snd_renameApart_live; eauto.
           rewrite drop_rev in *.
           rewrite renameApartFRight_corr in *.
           simpl in *. subst.
           len_simpl. rewrite rev_rev in *.
           orewrite (❬F❭ - S (❬F❭ - S n) = n) all.
           erewrite (snd_renameApartF_live _ nil); eauto;
             intros; inv_get; eauto using fst_renameApart_live with len.
           rewrite minus_dist_union.
           rewrite lookup_set_update_union_minus_list; eauto with len.
           setoid_rewrite disj_minus_eq at 2.
           unfold lookup_set. clear; cset_tac.
           symmetry. eapply disj_2_incl.
           eapply fresh_list_stable_spec; eauto.
           exploit H8; eauto.
           edestruct srd_globals_live_From; eauto; dcr.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           inv_get. simpl in *.
           eapply incl_union_right.
           rewrite <- Incl. eauto with cset.
        -- revert LenZL; clear; eauto with len.
        -- revert H LenLV; clear; eauto with len.
        -- revert H LenDL; clear; eauto with len.
        -- revert H LenLV2; clear; eauto with len.
        -- simpl in *. rewrite <- Incl at 1.
           eauto with cset.
      * intros. erewrite fst_renameApart_live; eauto.
    + rewrite rev_length, renameApartF_length, renameApartF_live_length; eauto.
    + intros; inv_get. len_simpl.
      edestruct (get_fst_renameApartF _ _ _ _ H4) as [? [? ?]]; eauto; dcr. subst.
      clear H15 H14.
      edestruct (get_fst_renameApartF_live _ _ _ _ _ _ H5); eauto; dcr; subst.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n) all. get_functional.
      rewrite H10, H21.
      rewrite drop_rev. rewrite rev_rev. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      rewrite renameApartFRight_corr.
      erewrite <- (@snd_renameApartF_live _ (take n als));
        intros; inv_get; eauto using fst_renameApart_live with len.
      eapply live_sound_monotone2.
      eapply H1; eauto with len.
      -- intros ? ? ? GetA GetB; inv_get.
         eapply get_app_cases in GetA; destruct GetA.
         ++ rewrite get_app_lt in GetB; inv_get.
           edestruct (get_fst_renameApartF _ _ _ _ GetB) as [? [? ?]];
             eauto; dcr. subst.
           len_simpl.
           assert (n0 < ❬F❭) by eauto using get_range.
           orewrite (❬F❭ - S (❬F❭ - S n0) = n0) all. get_functional. eauto.
           eauto with len.
         ++ dcr. rewrite  get_app_ge in GetB;[|eauto with len ].
           len_simpl.
           exploit ParamLen; eauto.
      -- rewrite !zip_app; eauto with len.
         eauto using PIR2_app, PIR2_ifFstR_refl, restrict_ifFstR.
      -- rewrite !zip_app, !List.map_app; eauto with len.
         apply PIR2_app; eauto with len.
         ++ eapply PIR2_get; intros; inv_get; simpl; [|eauto with len].
           repeat cases; simpl; econstructor.
           len_simpl. destruct x4 as [Z s], x2 as [Z' s'], x0 as [Z'' s''].
           edestruct (get_fst_renameApartF _ _ _ _ H20) as [? [? ?]]; eauto; dcr.
           edestruct (get_fst_renameApartF_live _ _ _ _ _ _ H22); eauto; dcr; subst.
           clear H28 H27.
           assert (n0 < ❬F❭) by eauto using get_range.
           orewrite (❬F❭ - S (❬F❭ - S n0) = n0) all. get_functional.
           inv_get.
           rewrite getAnn_setTopAnn. erewrite getAnn_snd_renameApart_live; eauto.
           rewrite drop_rev in *.
           rewrite renameApartFRight_corr in *. rewrite rev_rev in *.
           simpl in *. subst. len_simpl.
           orewrite (❬F❭ - S (❬F❭ - S n0) = n0) all.
           erewrite <- (@snd_renameApartF_live _ (take n0 als));
             intros; inv_get; eauto using fst_renameApart_live with len.
           assert (MME:forall (s t:set var), (t ∪ s) \ s [=] t \ s) by (clear; intros; cset_tac).
           rewrite MME.
           rewrite lookup_set_update_union_minus_list; eauto with len.
           setoid_rewrite disj_minus_eq at 2.
           rewrite lookup_set_update_disj; eauto.
           rewrite COND. clear; hnf; cset_tac.
           exploit (H8 n0); eauto.
           edestruct srd_globals_live_From; eauto; dcr.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           inv_get.
           simpl in *. eapply disj_1_incl. symmetry.
           eapply fresh_list_stable_spec; eauto.
           eapply incl_union_right. rewrite <- Incl. eapply map_incl; eauto.
           rewrite H34; eauto.
         ++ eapply PIR2_get; intros; inv_get; simpl.
           ** destruct x; simpl; try now econstructor.
              unfold restr. cases; simpl; econstructor.
              rewrite lookup_set_update_disj; eauto.
              exploit PIR2_nth; try eapply iEQ'; eauto using map_get_eq. dcr.
              inv_get. simpl in *. inv H28. eauto.
              rewrite COND. clear; hnf; cset_tac.
           ** len_simpl. exploit PIR2_length; eauto. len_simpl. eauto.
      -- exploit (H8 n); eauto.
         edestruct srd_globals_live_From; eauto; dcr.
         destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         rewrite lookup_set_update_with_list_in_union_length; eauto with len.
         inv_get.
         rewrite H25. unfold lookup_set. rewrite H3. rewrite Incl.
         clear; cset_tac.
      -- eauto with cset.
    + intros ? ? ? GetA GetB; inv_get; simpl.
      edestruct (get_fst_renameApartF _ _ _ _ GetA) as [? [? ?]]; eauto; dcr. subst.
      rewrite H19. len_simpl.
      edestruct (get_fst_renameApartF_live _ _ _ _ _ _ GetB); eauto; dcr; subst.
      erewrite getAnn_snd_renameApart_live; eauto.
      exploit H2; eauto; dcr.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n) all.
      get_functional.
      rewrite drop_rev in *.
      rewrite rev_rev in *. len_simpl.
      assert (n < ❬F❭) by eauto using get_range.
      orewrite (❬F❭ - S (❬F❭ - S n) = n) all.
      rewrite renameApartFRight_corr.
      erewrite <- (@snd_renameApartF_live _ (take n als)).
      split.
      -- rewrite getAnn_setTopAnn. eauto with cset.
      -- split.
         ++ eapply fresh_list_stable_nodup; eauto.
         ++ rewrite getAnn_setTopAnn. cases; eauto.
           rewrite lookup_set_update_with_list_in_union_length; eauto.
           rewrite H24. clear. cset_tac. eauto with len.
      -- eauto with len.
      -- intros. inv_get.
         exploit H0; eauto.
         erewrite fst_renameApart_live; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
Qed.
*)