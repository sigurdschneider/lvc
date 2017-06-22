Require Import Util CSet Map LengthEq.
Require Import Env IL Alpha StableFresh Subset1 OptionR.
Require Import Annotation AnnP RenamedApart RenameApart SetOperations Take.
Require Import LabelsDefined PairwiseDisjoint Liveness.Liveness Coherence Restrict.
Require Import FreshGen.

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
      only 1-3,5,8: (rewrite <- Incl; eauto with cset);
      pe_rewrite; set_simpl.
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

Definition renameApartF_live {Fi} (FG:FreshGen Fi)
           (renameApart_live: FreshGen Fi -> Fi -> env var -> stmt -> ann (set var) -> Fi * ann (set var))
           ϱ :=
  (fix f fi (F:list (params*stmt)) (anF:list (ann (set var))) :=
     match F, anF with
     | Zs::F, a::anF =>
       let (Y, fi) := fresh_list FG fi (fst Zs) in
       let ϱZ := ϱ [ fst Zs <-- Y ] in
       let '(fi, alv') := renameApart_live FG fi ϱZ (snd Zs) a in
       let (YL, fi) := f fi F anF in
       (setTopAnn alv' (getAnn alv' ∪ of_list Y)::YL, fi)
     | _, _ => (nil, fi)
     end).


Fixpoint renameApart_live {Fi} (FG:FreshGen Fi) fi
         (ϱ:env var) (s:stmt) (alv:ann (set var))
  : Fi * ann (set var) :=
  match s, alv with
  | stmtLet x e s0, ann1 lv alv =>
    let (y,fi) := fresh FG fi x in
    let ϱ' := ϱ[x <- y] in
    let (fi, alv') := renameApart_live FG fi ϱ' s0 alv in
    (fi, ann1 (lookup_set ϱ lv) alv')
  | stmtIf e s1 s2, ann2 lv alv1 alv2 =>
    let (fi, alv1') := renameApart_live FG fi ϱ s1 alv1 in
    let (fi, alv2') := renameApart_live FG fi ϱ s2 alv2 in
    (fi, ann2 (lookup_set ϱ lv) alv1' alv2')
  | stmtApp l Y, ann0 lv => (fi, ann0 (lookup_set ϱ lv))
  | stmtReturn e, ann0 lv => (fi, ann0 (lookup_set ϱ lv))
  | stmtFun F s2, annF lv anF alv2 =>
    let (anF', fi) := renameApartF_live FG renameApart_live ϱ fi F anF in
    let (fi, alv2') := renameApart_live FG fi ϱ s2 alv2 in
    (fi, annF (lookup_set ϱ lv) anF' alv2')
  | _ , _ => (fi, alv)
  end.

Lemma getAnn_snd_renameApart_live {Fi} (FG:FreshGen Fi) fi o ZL LV ϱ s lv
  : live_sound o ZL LV s lv
    -> getAnn (snd (renameApart_live FG fi ϱ s lv)) = lookup_set ϱ (getAnn lv).
Proof.
  intros LS; inv LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.


Lemma snd_renameApartF_live' {Fi} (FG:FreshGen Fi) fi als L ϱ F (Len:❬F❭ = ❬als❭)
      (IH:forall n Zs a fi, get F n Zs -> get als n a ->
                    forall (ϱ : env var),
                      fst (renameApart_live FG fi ϱ (snd Zs) a) =
                      fst (renameApart FG fi ϱ (snd Zs)))
  : snd (renameApartF_live FG renameApart_live ϱ fi F als) =
    snd (renameApartF FG renameApart ϱ F (L, fi)).
Proof.
  length_equify.
  general induction Len.
  - eauto.
  - simpl. repeat let_pair_case_eq; simpl; subst; simpl.
    erewrite <- IHLen; eauto using get.
    erewrite <- IH; eauto using get.
Qed.


Lemma fst_renameApart_live {Fi} (FG:FreshGen Fi) fi o ZL LV ϱ s lv
  : live_sound o ZL LV s lv
    -> fst (renameApart_live FG fi ϱ s lv) = fst (renameApart FG fi ϱ s).
Proof.
  intros LS.
  general induction LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite IHLS1, IHLS2; eauto.
  - erewrite snd_renameApartF_live'; eauto.
Qed.

Lemma snd_renameApartF_live {Fi} (FG:FreshGen Fi) fi als L ϱ F (Len:❬F❭ = ❬als❭) ZL Lv i
      (LS:forall (n : nat) (Zs : params * stmt) (a : ann ⦃nat⦄),
            get F n Zs ->
            get als n a -> live_sound i ZL Lv (snd Zs) a)
  : snd (renameApartF_live FG renameApart_live ϱ fi F als) =
    snd (renameApartF FG renameApart ϱ F (L, fi)).
Proof.
  eapply snd_renameApartF_live'; eauto.
  intros.
  eapply fst_renameApart_live; eauto.
Qed.


Lemma renameApartF_live_length {Fi} (FG:FreshGen Fi) fi ϱ F anF (Len:❬F❭ = ❬anF❭)
: length (fst (renameApartF_live FG renameApart_live ϱ fi F anF)) = length F.
Proof.
  general induction Len; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.

Smpl Add match goal with
         | [ H : context [ ❬fst (renameApartF_live ?FG ?renameApart' ?ϱ ?fi ?F ?anF)❭ ] |- _ ] =>
           rewrite (@renameApartF_live_length _ FG fi ϱ F anF) in H
         | [ |- context [ ❬fst (renameApartF_live ?FG ?renameApart' ?ϱ ?fi ?F ?anF)❭ ] ] =>
           rewrite (@renameApartF_live_length _ FG fi ϱ F anF)
         end : len.

Lemma get_fst_renameApartF_live {Fi} (FG:FreshGen Fi) fi  ϱ F n anF ans
  (Get: get (fst (renameApartF_live FG renameApart_live ϱ fi F anF)) n ans)
  (Len:❬F❭=❬anF❭)
  :  exists Zs a Yfi ans',
    get F n Zs /\ get anF n a
    /\ ans' = snd (renameApart_live FG (snd Yfi) (ϱ [fst Zs <-- fst Yfi]) (snd Zs) a) /\
    ans = setTopAnn ans' (getAnn ans' ∪ of_list (fst Yfi)) /\
(*    fi'' = snd (renameApartF_live FG renameApart_live ϱ (snd Yfi) (take n F) (take n anF))*)
    Yfi = (fresh_list FG (snd (renameApartF_live FG renameApart_live ϱ fi (take n F) (take n anF))) (fst Zs)).
Proof.
  general induction Len; simpl in * |- *; [ isabsurd |].
  - revert Get; repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; intros Get.
    inv Get.
    + eexists x, y; eauto 100 using get.
    + edestruct IHLen as [? [? [? ?]]]; dcr; subst; eauto 20 using get.
      subst.
      do 4 eexists; split; [| split]; eauto 100 using get.
      split. reflexivity. simpl.
      repeat let_pair_case_eq; repeat simpl_pair_eqs; subst. simpl.
      split.
      reflexivity. split; reflexivity.
Qed.

Smpl Add
     match goal with
     | [ H : get (fst (renameApartF_live ?FG renameApart_live ?ϱ ?fi ?F ?anF)) ?n ?ans |- _ ] =>
       eapply get_fst_renameApartF_live in H
         as [? [? [? [? [? [? [? [? ?]]]]]]]]; eauto; subst
     end : inv_get.


Tactic Notation "orewrite" constr(A) "in *" :=
  let X := fresh "OX" in assert A as X by omega; rewrite X in *; clear X.

Lemma renameApart_live_sound {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG)
      fi ZL LV ZL' LV' s lv ϱ
      (LenZL:❬ZL❭ = ❬ZL'❭) (LenLV:❬LV❭=❬LV'❭)
      (ParamLen:forall n Z Z', get ZL n Z -> get ZL' n Z' -> ❬Z❭ = ❬Z'❭)
  : live_sound Functional ZL LV s lv
    -> live_sound Functional ZL' LV'
                 (snd (renameApart FG fi ϱ s))
                 (snd (renameApart_live FG fi ϱ s lv)).
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
           ++ rewrite get_app_lt in H5; inv_get; len_simpl; inv_get; eauto.
             rewrite fresh_list_len; eauto.
           ++ dcr. rewrite get_app_ge in H5; eauto with len.
    + eauto with len.
    + intros; inv_get; len_simpl; inv_get.
      rewrite drop_rev.
      rewrite renameApartFRight_corr.
      erewrite <- snd_renameApartF_live. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n). rewrite rev_rev.
      eapply live_sound_monotone2.
      eapply H1; eauto.
      revert LenZL; clear; eauto with len.
      revert H LenLV; clear; eauto with len.
      -- intros ? ? ? GetA GetB; inv_get.
         eapply get_app_cases in GetA as [?|[? ?]].
         ++ rewrite get_app_lt in GetB; inv_get. len_simpl. inv_get.
           rewrite fresh_list_len; eauto.
           eauto with len.
         ++ rewrite get_app_ge in GetB; eauto with len.
      -- eauto with cset.
      -- len_simpl.
         orewrite (❬F❭ - S (❬F❭ - S n) = n). eauto with len.
      -- intros. inv_get. len_simpl. inv_get.
         exploit H0; try eapply H15; eauto.
    + intros ? ? ? GetA GetB; inv_get. len_simpl. inv_get.
      erewrite getAnn_snd_renameApart_live; eauto.
      exploit H2; eauto. destruct H6 as [? [? ?]].
      rewrite drop_rev.
      rewrite renameApartFRight_corr. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      rewrite rev_rev.
      erewrite <- (@snd_renameApartF_live _ FG fi (take n als)).
      split.
      rewrite getAnn_setTopAnn. eauto with cset.
      rewrite getAnn_setTopAnn.
      split.
      eapply fresh_list_nodup; eauto. simpl in *.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      rewrite <- H8. clear. cset_tac.
      rewrite fresh_list_len; eauto with len. eauto with len.
      intros; inv_get; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
Qed.

Lemma renameApart_live_sound_srd b {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi o DL ZL LV (ZL':list params) LV' s lv ϱ
      (ParamLen:forall n Z Z', get ZL n Z -> get ZL' n Z' -> ❬Z❭ = ❬Z'❭)
  (LS: live_sound o ZL LV s lv)
  (SRD:srd DL s lv)
  (iEQ:PIR2 (ifFstR Equal) DL (LV \\ ZL))
  (iEQ':PIR2 (ifFstR Equal) (option_map (fun (s:set var) => map ϱ s) ⊝ DL) (LV' \\ ZL'))
  (NUC:noUnreachableCode (isCalled b) s)
  (LenZL:❬ZL❭ = ❬ZL'❭) (LenLV:❬LV❭=❬LV'❭) (LenDL:❬DL❭=❬ZL❭) (LenLV2:❬LV❭=❬ZL❭)
  (Incl:map ϱ (getAnn lv) ⊆ domain FG fi) (isImp:isImperative o)
  : live_sound o ZL' LV' (snd (renameApart FG fi ϱ s))
               (snd (renameApart_live FG fi ϱ s lv)).
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
      * simpl in *. rewrite <- fresh_domain_spec; eauto.
        rewrite <- Incl.
        revert H0; clear_all; cset_tac'; lud; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite lookup_set_update_union_minus_single; eauto.
      rewrite <- H0. eauto with cset.
    + erewrite getAnn_snd_renameApart_live; eauto.
      revert H1. clear_all. lset_tac. eexists x; lud; eauto.
  - simpl in *.
    econstructor; eauto using live_op_rename_sound, restrict_ifFstR.
    + eapply IHLS1; eauto with cset.
    + erewrite fst_renameApart_live; eauto.
      eapply IHLS2; eauto.
      rewrite <- domain_incl_renameApart; eauto.
      rewrite <- Incl. eauto with cset.
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
           eapply get_app_cases in H4 as [?|[? ?]].
           ++ rewrite get_app_lt in H5; inv_get. len_simpl; inv_get.
             rewrite fresh_list_len; eauto.
             eauto with len.
           ++ rewrite get_app_ge in H5; eauto with len.
        -- rewrite zip_app;[| eauto with len].
           eauto using PIR2_app, PIR2_ifFstR_refl.
        -- rewrite !zip_app, List.map_app;[| eauto with len].
           apply PIR2_app; eauto with len.
           eapply PIR2_get; intros; inv_get; [|eauto with len].
           len_simpl. inv_get.
           econstructor. destruct x as [Z' s'].
           exploit H0; eauto.
           rewrite getAnn_setTopAnn. erewrite getAnn_snd_renameApart_live; eauto.
           rewrite drop_rev in *.
           rewrite renameApartFRight_corr in *.
           len_simpl. rewrite rev_rev in *.
           orewrite (❬F❭ - S (❬F❭ - S n) = n).
           erewrite (snd_renameApartF_live); eauto;
             intros; inv_get; eauto using fst_renameApart_live with len.
           rewrite minus_dist_union.
           rewrite lookup_set_update_union_minus_list; eauto with len. simpl.
           setoid_rewrite disj_minus_eq at 2.
           unfold lookup_set. clear; cset_tac.
           symmetry. eapply disj_2_incl. symmetry.
           eapply fresh_list_disj; eauto.
           exploit H8; eauto.
           edestruct srd_globals_live_From as [? [? [? [? ?]]]]; eauto.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           inv_get. simpl in *.
           rewrite <- domain_incl_renameApartF; eauto.
           rewrite <- Incl. eauto with cset.
           rewrite fresh_list_len; eauto.
        -- revert LenZL; clear; eauto with len.
        -- revert H LenLV; clear; eauto with len.
        -- revert H LenDL; clear; eauto with len.
        -- revert H LenLV2; clear; eauto with len.
        -- simpl in *.
           rewrite <- domain_incl_renameApartF; eauto.
           rewrite <- Incl.
           eauto with cset.
    + rewrite rev_length, renameApartF_length, renameApartF_live_length; eauto.
    + intros; inv_get. len_simpl. inv_get.
      rewrite drop_rev. rewrite rev_rev. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      rewrite renameApartFRight_corr.
      erewrite <- (@snd_renameApartF_live _ _ _ (take n als));
        intros; inv_get; eauto using fst_renameApart_live with len.
      eapply live_sound_monotone2.
      eapply H1; eauto.
      -- intros ? ? ? GetA GetB; inv_get.
         eapply get_app_cases in GetA as [?|[? ?]].
         ++ rewrite get_app_lt in GetB; inv_get; len_simpl; inv_get.
           rewrite fresh_list_len; eauto.
           eauto with len.
         ++ rewrite get_app_ge in GetB;[|eauto with len ].
           len_simpl.
           exploit ParamLen; eauto.
      -- rewrite !zip_app; eauto with len.
         eauto using PIR2_app, PIR2_ifFstR_refl, restrict_ifFstR.
      -- rewrite !zip_app, !List.map_app; eauto with len.
         apply PIR2_app; eauto with len.
         ++ eapply PIR2_get; intros; inv_get; [|eauto with len].
           rewrite getAnn_setTopAnn. simpl restr.
           repeat cases; eauto; econstructor.
           len_simpl.
           inv_get.
           erewrite getAnn_snd_renameApart_live; eauto.
           rewrite drop_rev in *.
           rewrite renameApartFRight_corr. rewrite rev_rev.
           len_simpl.
           orewrite (❬F❭ - S (❬F❭ - S n0) = n0).
           erewrite (@snd_renameApartF_live _ _ _ (take n0 als));
             intros; inv_get; eauto using fst_renameApart_live with len.
           assert (MME:forall (s t:set var), (t ∪ s) \ s [=] t \ s) by (clear; intros; cset_tac).
           rewrite MME.
           rewrite lookup_set_update_union_minus_list; eauto with len.
           setoid_rewrite disj_minus_eq at 2.
           rewrite lookup_set_update_disj; eauto.
           rewrite COND. clear; hnf; cset_tac.
           exploit (H8 n0); eauto.
           edestruct srd_globals_live_From as [? [? [? [? ?]]]]; eauto.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           destruct o; simpl in *;
             [ isabsurd | |]; eauto using live_sound_overapproximation_I.
           inv_get.
           simpl in *. eapply disj_1_incl.
           eapply fresh_list_disj; eauto.
           rewrite <- domain_incl_renameApartF; eauto.
           rewrite <- Incl. eapply map_incl; eauto.
           eauto with cset.
           rewrite fresh_list_len; eauto.
         ++ eapply PIR2_get; intros; inv_get; simpl.
           ** destruct x1; simpl; try now econstructor.
              cases; simpl; econstructor.
              rewrite lookup_set_update_disj; eauto.
              exploit PIR2_nth; try eapply iEQ'; eauto using map_get_eq.
              destruct H16 as [? [? ?]].
              inv_get. simpl in *. clear_trivial_eqs. eauto.
              rewrite COND. clear; hnf; cset_tac.
           ** len_simpl. exploit PIR2_length; eauto. len_simpl. eauto.
      -- exploit (H8 n); eauto.
         edestruct srd_globals_live_From; eauto; dcr.
         destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         eauto with len.
      -- eauto with len.
      -- eauto with len.
      -- rewrite <- fresh_list_domain_spec; eauto.
         rewrite lookup_set_update_with_list_in_union_length.
         erewrite (@snd_renameApartF_live _ _ _ (take n als));
           intros; inv_get; eauto using fst_renameApart_live with len.
         rewrite <- domain_incl_renameApartF; eauto.
         rewrite union_comm. eapply incl_union_lr; eauto.
         rewrite <- Incl. simpl.
         edestruct srd_globals_live_From; eauto.
          destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         destruct o; simpl in *;
           [ isabsurd | |]; eauto using live_sound_overapproximation_I.
         dcr. inv_get. rewrite H15. rewrite <- H3; eauto.
         eauto. rewrite fresh_list_len; eauto.
      -- cset_tac.
    + intros ? ? ? GetA GetB; inv_get. len_simpl. inv_get.
      erewrite getAnn_snd_renameApart_live; eauto.
      exploit H2; eauto. destruct H9 as [? [? ?]].
      rewrite drop_rev.
      rewrite rev_rev. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n).
      rewrite renameApartFRight_corr.
      erewrite <- (@snd_renameApartF_live _ _ _ (take n als)).
      split.
      -- rewrite getAnn_setTopAnn. eauto with cset.
      -- split.
         ++ eapply fresh_list_nodup; eauto.
         ++ rewrite getAnn_setTopAnn. cases; eauto.
           rewrite lookup_set_update_with_list_in_union_length; eauto.
           rewrite H13. clear. cset_tac.
           rewrite fresh_list_len; eauto.
      -- eauto with len.
      -- intros. inv_get.
         exploit H0; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto with cset.
Qed.
