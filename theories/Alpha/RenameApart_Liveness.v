Require Import Util CSet Map LengthEq.
Require Import Env IL Alpha Fresh Annotation RenamedApart RenameApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint Liveness.


Definition renameApartF_live
  (renameApart_live:env var -> set var -> stmt -> ann (set var) -> set var * ann (set var)) G ϱ :=
  (fix f (N:set var) (F:list (params*stmt)) (anF:list (ann (set var))) :=
     match F, anF with
     | Zs::F, a::anF =>
       let Y := fresh_list fresh (N ∪ G) (length (fst Zs)) in
       let ϱZ := ϱ [ fst Zs <-- Y ] in
       let (N', alv') := renameApart_live ϱZ (G ∪ N ∪ of_list Y) (snd Zs) a in
       let (anF', N'') := f (N' ∪ of_list Y ∪ N) F anF in
       (alv'::anF', N'')
     | _, _ => (nil, N)
     end).


Fixpoint renameApart_live (ϱ:env var) (G:set var) (s:stmt) (alv:ann (set var))
  : set var * ann (set var) :=
match s, alv with
   | stmtLet x e s0, ann1 lv alv =>
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in
     let (G', alv') := renameApart_live ϱ' {y; G} s0 alv in
       ({y; G'}, ann1 (lookup_set ϱ lv) alv')
   | stmtIf e s1 s2, ann2 lv alv1 alv2 =>
     let (G', alv1') := renameApart_live ϱ G s1 alv1 in
     let (G'', alv2') := renameApart_live ϱ (G ∪ G') s2 alv2 in
      (G' ∪ G'', ann2 (lookup_set ϱ lv) alv1' alv2')
   | stmtApp l Y, ann0 lv => (∅, ann0 (lookup_set ϱ lv))
   | stmtReturn e, ann0 lv => (∅, ann0 (lookup_set ϱ lv))
   | stmtFun F s2, annF lv anF alv2 =>
     let (anF', G') := renameApartF_live renameApart_live G ϱ ∅ F anF in
     let (G'', alv2') := renameApart_live ϱ (G ∪ G') s2 alv2 in
     (G' ∪ G'', annF (lookup_set ϱ lv) anF' alv2')
   | _ , _ => (∅, alv)
   end.

Lemma getAnn_snd_renameApart_live ZL LV ϱ G s lv
  : live_sound Functional ZL LV s lv
    -> getAnn (snd (renameApart_live ϱ G s lv)) = lookup_set ϱ (getAnn lv).
Proof.
  intros LS; inv LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.


Lemma snd_renameApartF_live L X G ϱ F als (Len:❬F❭ = ❬als❭)
      (IH:forall n Zs a, get F n Zs -> get als n a ->
                    forall (ϱ : env var) (G : ⦃var⦄),
                      fst (renameApart_live ϱ G (snd Zs) a) = fst (renameApart' ϱ G (snd Zs)))
  : snd (renameApartF_live renameApart_live G ϱ X F als) =
    snd (renameApartF renameApart' G ϱ F (L, X)).
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


Lemma fst_renameApart_live ZL LV ϱ G s lv
  : live_sound Functional ZL LV s lv
    -> fst (renameApart_live ϱ G s lv) = fst (renameApart' ϱ G s).
Proof.
  intros LS.
  general induction LS; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite IHLS; eauto.
  - rewrite IHLS1, IHLS2; eauto.
  - erewrite snd_renameApartF_live; eauto.
    f_equal; eauto.
Qed.


Lemma renameApartF_live_length G G' ϱ F anF (Len:❬F❭ = ❬anF❭)
: length (fst (renameApartF_live renameApart_live G ϱ G' F anF)) = length F.
Proof.
  length_equify.
  general induction Len; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
Qed.

Lemma renameApart_live_sound ZL LV ZL' LV' s lv ϱ G
      (LenZL:❬ZL❭ = ❬ZL'❭) (LenLV:❬LV❭=❬LV'❭)
      (ParamLen:forall n Z Z', get ZL n Z -> get ZL' n Z' -> ❬Z❭ = ❬Z'❭)
  : live_sound Functional ZL LV s lv
    -> live_sound Functional ZL' LV' (snd (renameApart' ϱ G s)) (snd (renameApart_live ϱ G s lv)).
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
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite H0; eauto.
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite H1; eauto.
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
           ++ rewrite get_app_lt in H5; inv_get.
             edestruct (get_fst_renameApartF _ _ _ H5) as [? [? ?]]; eauto; dcr.
             rewrite renameApartF_length in H9.
             assert (n < ❬F❭) by eauto using get_range.
             orewrite (❬F❭ - S (❬F❭ - S n) = n) in H9. get_functional. eauto.
             rewrite map_length, rev_length, renameApartF_length; eauto using get_range.
           ++ dcr. rewrite get_app_ge in H5.
             rewrite ?map_length,?rev_length in *.
             rewrite renameApartF_length in H5.
             exploit ParamLen; eauto.
             rewrite map_length in *.
             rewrite rev_length, renameApartF_length; eauto.
      * intros. erewrite fst_renameApart_live; eauto.
    + rewrite rev_length, renameApartF_length, renameApartF_live_length; eauto.
    + intros; inv_get.
      edestruct (get_fst_renameApartF _ _ _ H4) as [? [? ?]]; eauto; dcr.
      rewrite H7. admit.
    + intros; inv_get; simpl.
      admit.
    + erewrite getAnn_snd_renameApart_live; eauto.
      rewrite H3; eauto.
Qed.