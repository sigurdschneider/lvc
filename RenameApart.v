Require Import CSet Le.

Require Import Plus Util Map.
Require Import Env EnvTy IL Alpha Fresh Annotation RenamedApart SetOperations.

Set Implicit Arguments.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Fixpoint renameApart' (ϱ:env var) (G:set var) (s:stmt) : set var * stmt:=
match s with
   | stmtLet x e s0 =>
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in
     let (G', s') := renameApart' ϱ' {y; G} s0 in
       ({y; G'}, stmtLet y (rename_exp ϱ e) s')
   | stmtIf e s1 s2 =>
     let (G', s1') := renameApart' ϱ G s1 in
     let (G'', s2') := renameApart' ϱ (G ∪ G') s2 in
      (G' ∪ G'', stmtIf (rename_exp ϱ e) s1' s2')
   | stmtApp l Y => (∅, stmtApp l (List.map (rename_exp ϱ) Y))
   | stmtReturn e => (∅, stmtReturn (rename_exp ϱ e))
   | stmtExtern x f Y s =>
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in
     let (G', s') := renameApart' ϱ' {y; G} s in
       ({y; G'}, stmtExtern y f (List.map (rename_exp ϱ) Y) s')
   | stmtFun Z s1 s2 =>
     let Y := fresh_list fresh G (length Z) in
     let ϱZ := ϱ [ Z <-- Y ] in
     let (G', s1') := renameApart' ϱZ (G ∪ of_list Y) s1 in
     let (G'', s2') := renameApart' ϱ (G ∪ (G' ∪ of_list Y)) s2 in
     (G' ∪ (G'' ∪ of_list Y), stmtFun Y s1'  s2')
   end.

Lemma renameApart'_disj ϱ G s
  : disj G (fst (renameApart' ϱ G s)).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite disj_add; split; eauto using fresh_spec.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply IHs].
    cset_tac; intuition.
  - rewrite disj_app; split; eauto.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply IHs2].
    cset_tac; intuition.
  - rewrite disj_add; split; eauto using fresh_spec.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply IHs].
    cset_tac; intuition.
  - repeat (rewrite disj_app; split); eauto.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply IHs1].
    cset_tac; intuition.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply IHs2].
    cset_tac; intuition.
    symmetry. eapply fresh_list_spec, fresh_spec.
Qed.

Fixpoint renamedApartAnn (s:stmt) (G:set var) : ann (set var * set var) :=
  match s with
    | stmtLet x e s =>
      let an := renamedApartAnn s {x; G} in
      ann1 (G, {x; snd (getAnn an) }) an
    | stmtIf e s t =>
      let ans := renamedApartAnn s G in
      let ant := renamedApartAnn t G in
      ann2 (G, snd (getAnn ans) ∪ snd (getAnn ant)) ans ant
    | stmtReturn e =>
      ann0 (G, ∅)
    | stmtApp f Y =>
      ann0 (G, ∅)
    | stmtExtern x f Y s =>
      let an := renamedApartAnn s {x; G} in
      ann1 (G, {x; snd (getAnn an)}) an
    | stmtFun Z s t =>
      let ans := renamedApartAnn s (G ∪ of_list Z) in
      let ant := renamedApartAnn t G in
      ann2 (G, snd (getAnn ans) ∪ (snd (getAnn ant) ∪ of_list Z)) ans ant
  end.

Instance renamedApart_ann_morph
: Proper (eq ==> Equal ==> ann_R (@pe _ _ )) renamedApartAnn.
Proof.
  unfold Proper, respectful; intros. subst.
  general induction y; simpl; eauto using ann_R.
  - econstructor. rewrite H0 at 1. rewrite IHy. reflexivity.
    rewrite H0; reflexivity.
    eapply IHy. rewrite H0; reflexivity.
  - econstructor; eauto.
    rewrite H0 at 1. rewrite IHy1, IHy2; eauto. reflexivity.
  - econstructor; rewrite H0; reflexivity.
  - econstructor; rewrite H0; reflexivity.
  - econstructor. rewrite H0 at 1. rewrite IHy. reflexivity.
    rewrite H0; reflexivity.
    eapply IHy. rewrite H0; reflexivity.
  - econstructor; eauto.
    rewrite H0 at 1.
    rewrite IHy1, IHy2; eauto. reflexivity.
    rewrite H0; reflexivity.
    eapply IHy1. rewrite H0. reflexivity.
Qed.

Lemma fst_renamedApartAnn s G
 : fst (getAnn (renamedApartAnn s G)) = G.
Proof.
  general induction s; eauto.
Qed.


Lemma snd_renameApartAnn s G ϱ G'
: snd (getAnn (renamedApartAnn (snd (renameApart' ϱ G s)) G')) = fst (renameApart' ϱ G s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; eauto.
  - subst. rewrite IHs. reflexivity.
  - subst. rewrite IHs1. rewrite IHs2. reflexivity.
  - subst. rewrite IHs. reflexivity.
  - subst. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

Lemma renameApartAnn_decomp s G
: pe (getAnn (renamedApartAnn s G)) (G, snd (getAnn (renamedApartAnn s G))).
Proof.
  destruct s; simpl; try reflexivity.
Qed.

Lemma ann_R_pe_notOccur G G' s
:  notOccur G' s
   -> G \ G' [=] G
   -> ann_R (@pe var _)
           (renamedApartAnn s G)
                     (mapAnn (pminus G') (renamedApartAnn s (G ∪ G'))).
Proof.
  intros. general induction H; simpl; try now (econstructor; reflexivity).
  - assert ({x ; G ++ G'} [=] {x; G} ++ G'). {
      cset_tac; intuition.
    }
    econstructor.
    + rewrite H3. rewrite IHnotOccur.
      rewrite getAnn_mapAnn. unfold pminus.
      let_pair_case_eq; simpl; eauto.
      econstructor; try reflexivity.
      revert H2; clear_all; cset_tac; intuition.
      eapply H2 in H; intuition.
      rewrite <- H2.
      revert H; clear_all; cset_tac; intuition.
    + rewrite H3.
      eapply IHnotOccur.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition.
  - econstructor; eauto.
    rewrite IHnotOccur1, IHnotOccur2; eauto.
    repeat rewrite getAnn_mapAnn.
    unfold pminus.
    repeat let_pair_case_eq; simpl; eauto.
    econstructor; try reflexivity.
    rewrite <- H2. clear_all; cset_tac; intuition.
  - econstructor. econstructor. rewrite <- H0; cset_tac; intuition; eauto. reflexivity.
  - econstructor. econstructor; try rewrite <- H0; clear_all; cset_tac; intuition.
  - assert ({x ; G ++ G'} [=] {x; G} ++ G'). {
      cset_tac; intuition.
    }
    econstructor.
    + rewrite H3. rewrite IHnotOccur.
      rewrite getAnn_mapAnn. unfold pminus.
      let_pair_case_eq; simpl.
      econstructor; try reflexivity.
      rewrite <- H2; clear_all; cset_tac; intuition.
      rewrite <- H2; revert H0; clear_all; cset_tac; intuition.
    + rewrite H3.
      eapply IHnotOccur.
      rewrite <- H2; revert H0; clear_all; cset_tac; intuition.
  - assert ((G ++ G') ++ of_list Z [=] (G ++ of_list Z) ++ G'). {
      cset_tac; intuition.
    }
    econstructor; eauto.
    + rewrite H3. rewrite IHnotOccur1.
      rewrite getAnn_mapAnn. unfold pminus.
      let_pair_case_eq; simpl.
      econstructor. rewrite <- H2; clear_all; cset_tac; intuition.
      rewrite IHnotOccur2, getAnn_mapAnn.
      unfold pminus. let_pair_case_eq; simpl; eauto. reflexivity. eauto.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition; eauto.
    + rewrite H3.
      eapply IHnotOccur1.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition; eauto.
Qed.


Lemma freeVars_rename_exp_list ϱ Y
  : list_union (List.map Exp.freeVars (List.map (rename_exp ϱ) Y))[=]
               lookup_set ϱ (list_union (List.map Exp.freeVars Y)).
Proof.
  unfold list_union. rewrite lookup_set_list_union; eauto using lookup_set_empty.
  repeat rewrite map_map. eapply fold_left_union_morphism; [|reflexivity].
  clear_all. general induction Y; simpl; eauto using AllInRel.PIR2, freeVars_renameExp.
Qed.

Lemma freeVars_renamedApart' ϱ G s
: lookup_set ϱ (freeVars s) ⊆ G
  -> freeVars (snd (renameApart' ϱ G s)) [=] lookup_set ϱ (freeVars s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
          repeat rewrite lookup_set_union; try rewrite freeVars_renameExp; eauto; try reflexivity.
  - rewrite IHs.
    + rewrite lookup_set_update_union_minus; eauto.
      assert (fresh G ∉ lookup_set ϱ (freeVars s \ {{x}})).
      intro. eapply lookup_set_incl in H0; eauto.
      eapply H in H0. eapply fresh_spec; eauto.
      cset_tac; intuition.
      cset_tac; intuition.
    + rewrite lookup_set_update_in_union; eauto.
      rewrite <- H at 3. repeat rewrite lookup_set_union; eauto.
      cset_tac; intuition.
  - rewrite IHs1, IHs2.
    + reflexivity.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto. cset_tac; intuition.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto. cset_tac; intuition.
  - eapply freeVars_rename_exp_list.
  - rewrite IHs.
    + rewrite freeVars_rename_exp_list.
      rewrite lookup_set_update_union_minus; eauto.
      assert (fresh G ∉ lookup_set ϱ (freeVars s \ {{x}})).
      intro. eapply lookup_set_incl in H0; eauto.
      eapply H in H0. eapply fresh_spec; eauto.
      cset_tac; intuition.
      cset_tac; intuition.
    + rewrite lookup_set_update_in_union; eauto.
      rewrite <- H at 3. repeat rewrite lookup_set_union; eauto.
      cset_tac; intuition.
  - rewrite IHs1, IHs2.
    + rewrite lookup_set_update_union_minus_list; eauto.
      rewrite lookup_set_union in H; eauto.
      pose proof (fresh_list_spec _ fresh_spec G (length Z)).
      cset_tac; intuition; eauto.
      assert (a ∈ G). eapply H; eauto. cset_tac; intuition.
      left; intuition; eauto.
      rewrite fresh_list_length; eauto.
    + rewrite <- H at 1. rewrite lookup_set_union; eauto.
      cset_tac; intuition.
    + rewrite lookup_set_update_with_list_in_union_length; eauto.
      rewrite <- H at 2. rewrite lookup_set_union; eauto. cset_tac; intuition.
      rewrite fresh_list_length; eauto.
Qed.

Lemma definedVars_renamedApart' ϱ G s
: definedVars (snd (renameApart' ϱ G s)) [=] fst (renameApart' ϱ G s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
          repeat rewrite lookup_set_union; try rewrite freeVars_renameExp; eauto; try reflexivity.
  - rewrite IHs; eauto; reflexivity.
  - rewrite IHs1, IHs2; reflexivity.
  - rewrite IHs; reflexivity.
  - rewrite IHs1, IHs2. rewrite union_assoc. reflexivity.
Qed.


Lemma renameApart'_renamedApart (s:stmt) ϱ G
  : lookup_set ϱ (freeVars s) ⊆ G
  -> renamedApart (snd (renameApart' ϱ G s)) (renamedApartAnn (snd (renameApart' ϱ G s)) G).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl.
  - subst. econstructor; eauto using fresh_spec, renameApartAnn_decomp.
    + simpl in H.
      rewrite rename_exp_freeVars; eauto. etransitivity; eauto.
      eapply lookup_set_incl; eauto.
    + eapply IHs. simpl in *.
      hnf; intros. eapply lookup_set_spec in H0; eauto; dcr.
      lud.
      * rewrite H3. cset_tac. left; eauto.
      * cset_tac; intuition. right. rewrite H3. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.
    + reflexivity.
  - subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply renamedApartIf with (Ds := Gs1) (Dt := Gs2).
    + rewrite <- H. rewrite Exp.rename_exp_freeVars; eauto.
      eapply lookup_set_incl; eauto.
    + assert (Gs1 ⊆ G ++ Gs1) by (cset_tac; intuition).
      pose proof (renameApart'_disj ϱ (G ++ Gs1) s2).
      rewrite H2, <- H0 in H3. eapply H3.
    + repeat rewrite snd_renameApartAnn. subst; reflexivity.
    + subst. eapply IHs1. etransitivity; eauto. eapply lookup_set_incl; eauto.
      cset_tac; intuition.
    + pose proof (renameApart'_disj ϱ G s1). rewrite H1 in H0.
      pose proof (renameApart'_disj ϱ (G ++ Gs1) s2). rewrite H2 in H3.
      assert (notOccur Gs1 (snd (renameApart' ϱ (G ++ Gs1) s2))). {
        eapply occurVars_disj_notOccur.
        rewrite occurVars_freeVars_definedVars, disj_app.
        rewrite freeVars_renamedApart'. split.
        rewrite lookup_set_incl; eauto.
        rewrite H. symmetry; eauto. cset_tac; intuition.
        rewrite definedVars_renamedApart'. rewrite H2.
        rewrite incl_right; eauto.
        rewrite <- H. repeat rewrite lookup_set_union; cset_tac; intuition.
      }
      eapply renamedApart_minus; [|eapply IHs2|eapply ann_R_pe_notOccur]; eauto.
      * rewrite <- H. repeat rewrite lookup_set_union; cset_tac; intuition.
      * eapply minus_inane_set, H0.
    + rewrite renameApartAnn_decomp. rewrite snd_renameApartAnn.
      subst; reflexivity.
    + rewrite renameApartAnn_decomp. rewrite <- H2.
      rewrite snd_renameApartAnn.
      subst. reflexivity.
  - econstructor; [| reflexivity]. simpl in H.
    rewrite <- H.
    unfold list_union. rewrite lookup_set_list_union; eauto.
    instantiate (1:={}).
    eapply fold_left_subset_morphism; try reflexivity.
    repeat rewrite map_map.
    eapply map_ext_get; intros.
    rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
    eapply lookup_set_empty; eauto.
  - econstructor. simpl in H. rewrite <- H.
    rewrite Exp.rename_exp_freeVars; eauto.
    eapply lookup_set_incl; eauto.
    reflexivity. reflexivity.
  - subst. econstructor; eauto using fresh_spec, renameApartAnn_decomp.
    + simpl in H.
      assert  (lookup_set ϱ
        (list_union (List.map Exp.freeVars Y)) [<=]G).
      rewrite <- H.
      eapply lookup_set_incl; eauto.
      rewrite <- H0.
      unfold list_union. rewrite lookup_set_list_union; eauto.
      instantiate (1:={}).
      eapply fold_left_subset_morphism; try reflexivity.
      repeat rewrite map_map.
      eapply map_ext_get; intros.
      rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
      eapply lookup_set_empty; eauto.
    + eapply IHs. simpl in *.
      hnf; intros. eapply lookup_set_spec in H0; eauto; dcr.
      lud.
      * rewrite H3. cset_tac. left; eauto.
      * cset_tac. right. rewrite H3. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.
    + reflexivity.
  - simpl. subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply renamedApartLet with (Ds:=Gs1) (Dt:=Gs2).
    + eapply fresh_set_spec. eapply fresh_spec.
    + pose proof (renameApart'_disj ϱ (G ++ (Gs1 ++ of_list (fresh_list fresh G (length Z)))) s2).
      rewrite H2 in H0.
      pose proof (renameApart'_disj (ϱ [Z <-- fresh_list fresh G (length Z)])
                                    (G ++ of_list (fresh_list fresh G (length Z))) s1).
      rewrite H1 in H3.
      revert H0 H3; unfold disj; clear_all; cset_tac; intuition; eauto.
    + rewrite snd_renameApartAnn; try reflexivity.
      rewrite H1.
      rewrite snd_renameApartAnn; try reflexivity.
      rewrite H2. cset_tac; intuition.
    + eapply IHs1.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      eapply incl_union_lr; eauto. rewrite <- H.
      eapply lookup_set_incl; eauto. intuition. reflexivity.
      rewrite fresh_list_length; eauto.
    + rewrite renameApartAnn_decomp.
      econstructor. rewrite union_comm. reflexivity.
      rewrite snd_renameApartAnn. subst; reflexivity.
    + pose proof (renameApart'_disj (ϱ [Z <-- fresh_list fresh G (length Z)])
                                    (G ++ of_list (fresh_list fresh G (length Z))) s1).
      rewrite H1 in H0.
      pose proof (renameApart'_disj ϱ (G ++ Gs1 ++ of_list (fresh_list fresh G (length Z))) s2).
      rewrite H2 in H3.
      assert (notOccur (Gs1 ++ of_list (fresh_list fresh G (length Z))) (snd (renameApart' ϱ (G ++ Gs1 ++ of_list (fresh_list fresh G (length Z))) s2))). {
        eapply occurVars_disj_notOccur.
        rewrite occurVars_freeVars_definedVars, disj_app.
        rewrite freeVars_renamedApart'. split.
        rewrite lookup_set_incl; eauto.
        rewrite H. symmetry. rewrite disj_app; split.
        rewrite incl_left; eauto.
        symmetry; eapply fresh_list_spec, fresh_spec.
        cset_tac; intuition.
        rewrite definedVars_renamedApart'. rewrite H2.
        rewrite incl_right; eauto.
        rewrite <- H at 1. repeat rewrite lookup_set_union; cset_tac; intuition.
      }
      eapply renamedApart_minus; [|eapply IHs2| eapply ann_R_pe_notOccur]; eauto.
      * rewrite <- H at 1. rewrite lookup_set_union; cset_tac; intuition.
      * eapply minus_inane_set. change (disj G (Gs1 ++ of_list (fresh_list fresh G (length Z)))).
        eapply disj_app. split.
        rewrite incl_left; eauto.
        symmetry. eapply fresh_list_spec, fresh_spec.
    + rewrite renameApartAnn_decomp. econstructor. reflexivity.
      rewrite snd_renameApartAnn. rewrite H2. reflexivity.
    + eapply fresh_list_unique. eapply fresh_spec.
Qed.

Lemma rename_apart_alpha' G ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ G
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (renameApart' ϱ G s)) s.
Proof.
  general induction s; simpl; repeat let_pair_case_eq; subst; simpl in * |- *; eauto using alpha.

  - econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto. cset_tac; eauto.
    eapply IHs.
    + rewrite <- H at 3. rewrite lookup_set_update_in_union; intuition.
      rewrite lookup_set_union; cset_tac; intuition.
    + eapply inverse_on_update_inverse. intuition.
      eapply inverse_on_incl; eauto. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                         lookup_set ϱ (freeVars s \ {{x}} ∪ Exp.freeVars e)).
      rewrite lookup_set_union; cset_tac; intuition.
      rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor; eauto.
    + eapply alpha_exp_sym. eapply Exp.alpha_exp_rename_injective.
      eapply inverse_on_incl; eauto. eapply incl_right.
    + eapply IHs1.
      * eapply Subset_trans; eauto. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_right.
      * eapply inverse_on_incl; eauto. rewrite union_assoc, union_comm. eapply incl_right.
    + eapply IHs2; eauto.
      * rewrite <- H at 1. repeat rewrite lookup_set_union; cset_tac; intuition.
      * eapply inverse_on_incl; eauto.
        cset_tac; intuition.
  - econstructor. rewrite map_length; eauto.
    intros. edestruct map_get_4; eauto; dcr; get_functional; subst.
    eapply alpha_exp_sym. eapply Exp.alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto. eapply incl_list_union; try reflexivity.
    eapply map_get_1; eauto.

  - econstructor; eauto. eapply alpha_exp_sym.
    eapply Exp.alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto. reflexivity.

  - econstructor.
    + rewrite map_length; eauto.
    + intros. edestruct map_get_4; eauto; dcr; get_functional; subst.
      eapply alpha_exp_sym. eapply Exp.alpha_exp_rename_injective.
      eapply inverse_on_incl; eauto. etransitivity; [| eapply incl_right].
      eapply  incl_list_union; try reflexivity.
      eapply map_get_1; eauto.
    + eapply IHs; eauto.
      * rewrite <- H at 3. rewrite lookup_set_update_in_union; intuition.
        rewrite lookup_set_union; cset_tac; intuition.
      * eapply inverse_on_update_inverse. intuition.
        eapply inverse_on_incl; eauto. cset_tac; eauto.
        assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                           lookup_set ϱ (freeVars s \ {{x}} ∪ list_union (List.map Exp.freeVars Y))).
        rewrite lookup_set_union; cset_tac; intuition.
        rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor. eapply fresh_list_length.
    + eapply IHs1.
      * rewrite lookup_set_update_with_list_in_union_length.
        eapply incl_union_lr. rewrite <- H.
        eapply lookup_set_incl; intuition. reflexivity.
        intuition. rewrite fresh_list_length; eauto.
      * eapply inverse_on_update_fresh; eauto.
        eapply inverse_on_incl; eauto; cset_tac; eauto.
        eapply fresh_list_unique. eapply fresh_spec.
        rewrite fresh_list_length; eauto.
        assert (lookup_set ϱ (freeVars s1 \ of_list Z) ⊆
                           lookup_set ϱ ((freeVars s1 \ of_list Z) ++ freeVars s2)).
        rewrite lookup_set_union; cset_tac; intuition.
        rewrite H1. rewrite H. eapply fresh_list_spec, fresh_spec.
    + eapply IHs2.
      * rewrite <- H at 1.
        rewrite lookup_set_union; eauto. cset_tac; intuition.
      * eapply inverse_on_incl; eauto. eapply incl_right.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)
Definition rename_apart s := snd (renameApart' id (freeVars s) s).

Lemma rename_apart_renamedApart (s:stmt)
: renamedApart (rename_apart s)
               (renamedApartAnn (snd (renameApart' id (freeVars s) s)) (freeVars s)).
  eapply renameApart'_renamedApart. eapply lookup_set_on_id. reflexivity.
Qed.

Lemma rename_apart_alpha s
  : alpha id id (rename_apart s) s.
Proof.
  eapply rename_apart_alpha'.
  + eapply lookup_set_on_id; reflexivity.
  + eapply inverse_on_id.
Qed.

(*
Lemma rename_apart_2 G ϱ ϱ' s s' f g
:  alpha ϱ ϱ' s s'
  -> agree_on (freeVars s') (ϱ' ∘ f) g
  -> rename_apart f G s = rename_apart g G s'.
Proof.
  intros. general induction H;
  simpl. f_equal. f_equal. rewrite <- H0. eapply H1.

  rewrite (IHalpha _ _ (g [y <- fresh G])).

  simpl in H1. eapply agree_on_trans.
  eapply lookup_set_agree_on_comp. intuition.
  eapply alpha_sym in H0.
  eapply alpha_inverse_on in H0. eapply inverse_on_injective_on in H0.
  intro. eapply lookup_set_spec in H2. destruct H2; dcr.
  specialize (H0 x0 y).
*)



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
