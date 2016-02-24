Require Import CSet Le.

Require Import Plus Util Map.
Require Import Env EnvTy IL Alpha Fresh Annotation RenamedApart SetOperations.

Set Implicit Arguments.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Definition renameApartFStep (renameApart':env var -> set var -> stmt -> set var * stmt) G ϱ :=
  (fun Ys'G (Zs:params*stmt) =>
     let Y := fresh_list fresh (snd Ys'G ∪ G) (length (fst Zs)) in
     let ϱZ := ϱ [ fst Zs <-- Y ] in
     let (G', s1') := renameApart' ϱZ (G ∪ snd Ys'G ∪ of_list Y) (snd Zs) in
     ((Y, s1')::fst Ys'G, G' ∪ of_list Y ∪ snd Ys'G)).

Definition renameApartF (renameApart':env var -> set var -> stmt -> set var * stmt) G ϱ
           := fold_left (renameApartFStep renameApart' G ϱ).

Definition renameApartFRight (renameApart':env var -> set var -> stmt -> set var * stmt) G ϱ
           := fold_right (fun x y => renameApartFStep renameApart' G ϱ y x).

Lemma renameApartFRight_corr renameApart' G ϱ s F
: renameApartFRight renameApart' G ϱ s (rev F) =
  renameApartF renameApart' G ϱ F s.
Proof.
  unfold renameApartF, renameApartFRight.
  erewrite <- fold_left_rev_right; eauto.
Qed.

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
   | stmtFun F s2 =>
     let (F', G') := renameApartF renameApart' G ϱ F (nil, ∅) in
     let (G'', s2') := renameApart' ϱ (G ∪ G') s2 in
     (G' ∪ G'', stmtFun (rev F')  s2')
   end.

Lemma renamedApartF_disj renameApart' G ϱ F
: (forall ϱ G n Zs, get F n Zs -> disj G (fst (renameApart' ϱ G (snd Zs))))
  -> forall Ys G', disj G G' -> disj G (snd (renameApartF renameApart' G ϱ F (Ys, G'))).
Proof.
  general induction F; simpl; eauto.
  - unfold renameApartFStep.
    let_pair_case_eq; simpl_pair_eqs.
    eapply IHF; eauto using get.
    rewrite disj_app; split; eauto.
    rewrite disj_app; split; eauto.
    + subst. eapply disj_1_incl; eauto using get with cset.
    + symmetry. eapply disj_2_incl.
      eapply fresh_list_spec; eauto using fresh_spec with cset.
      eauto with cset.
Qed.

Lemma renameApart'_disj ϱ G s
  : disj G (fst (renameApart' ϱ G s)).
Proof.
  revert ϱ G. sind s; intros; destruct s; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite disj_add; split; eauto using fresh_spec.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply (IH s)]; eauto with cset.
  - rewrite disj_app; split; eauto.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply (IH s2)]; eauto with cset.
  - rewrite disj_add; split; eauto using fresh_spec.
    eapply disj_subset_subset_flip_impl; [| reflexivity | eapply (IH s)]; eauto with cset.
  - repeat (rewrite disj_app; split); eauto.
    + cut (forall Ys G', disj G G' -> disj G (snd (renameApartF renameApart' G ϱ s (Ys, G')))); eauto using renamedApartF_disj.
    + eapply disj_subset_subset_flip_impl; [| reflexivity | eapply (IH s0)]; eauto with cset.
Qed.

Definition renamedApartAnnF (renameApartAnn:stmt -> set var -> ann (set var * set var)) G
           := fold_right (fun (Zs:params*stmt) anFG =>
                        let ans := renameApartAnn (snd Zs) (G ∪ of_list (fst Zs)) in
                        (ans::fst anFG, snd (getAnn ans) ∪ of_list (fst Zs) ∪ snd anFG)).

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
    | stmtFun F t =>
      let (ans, G') := renamedApartAnnF renamedApartAnn G (nil, {}) F in
      let ant := renamedApartAnn t G in
      annF (G, G' ∪ (snd (getAnn ant))) ans ant
  end.

(*
Instance renamedApart_ann_morph
: Proper (eq ==> Equal ==> ann_R (@pe _ _ )) renamedApartAnn.
Proof.
  unfold Proper, respectful; intros. subst.
  revert x0 y0 H0. sind y; destruct y; simpl; intros; eauto using ann_R.
  - econstructor. rewrite H0 at 1. rewrite (IH y); eauto. reflexivity.
    rewrite H0; reflexivity.
    eapply IH; eauto. rewrite H0; reflexivity.
  - econstructor; eauto.
    rewrite H0 at 1. rewrite (IH y1), (IH y2); eauto. reflexivity.
  - econstructor; rewrite H0; reflexivity.
  - econstructor; rewrite H0; reflexivity.
  - econstructor. rewrite H0 at 1. rewrite (IH y); eauto. reflexivity.
    rewrite H0; reflexivity.
    eapply IH; eauto. rewrite H0; reflexivity.
  - repeat (let_pair_case_eq; simpl_pair_eqs); subst.
    econstructor; eauto with len.
    + rewrite H0 at 1.
      econstructor; eauto. rewrite IH; eauto.
      eapply union_eq_decomp; eauto.
      .
    + .
    + intros.
      inv_map H. inv_map H1.
    pose proof (IH (snd x)).
    eapply ann_R_get in H5.
    unfold comp.
    erewrite H5. reflexivity. eauto. rewrite H0; eauto.
    pose proof (IH y).
    eapply ann_R_get in H; eauto.
    rewrite H; eauto.
    intros. inv_map H. inv_map H1.
    eapply IH; eauto. rewrite H0; eauto.
Qed.
 *)

Lemma fst_renamedApartAnn s G
 : fst (getAnn (renamedApartAnn s G)) = G.
Proof.
  sind s; destruct s; eauto.
  - simpl. let_pair_case_eq. simpl; eauto.
Qed.

Lemma snd_renamedApartAnnF_fst G G' G'' s ϱ L L' G'''
: (forall n Zs G ϱ G',
     get s n Zs ->
     snd (getAnn (renamedApartAnn (snd (renameApart' ϱ G (snd Zs))) G')) = fst (renameApart' ϱ G (snd Zs)))
  -> snd (renamedApartAnnF renamedApartAnn G' (L', G''') L) = G''
  ->
   snd
     (renamedApartAnnF renamedApartAnn
        G' (L', G''') (fst (renameApartFRight renameApart' G ϱ (L, G'') s))) =
   snd (renameApartFRight renameApart' G ϱ (L, G'') s).
Proof.
  intros.
  revert_except s. induction s; intros.
  - simpl. eauto.
  - simpl.
    unfold renameApartFStep.
    repeat (let_pair_case_eq). simpl in *.
    erewrite <- IHs; intros; eauto using get; try congruence.
    subst.
    erewrite H; eauto using get.
Qed.

Lemma definedVars_renameApartF G ϱ F
: (forall ϱ G n Zs, get F n Zs -> definedVars (snd (renameApart' ϱ G (snd Zs)))
                                        [=] fst (renameApart' ϱ G (snd Zs)))
  -> list_union
      (List.map
         (fun f : params * stmt =>
            (definedVars (snd f) ++ of_list (fst f))%set)
         (fst (renameApartF renameApart' G ϱ F (nil, {}))))[=]
      snd (renameApartF renameApart' G ϱ F (nil, {})).
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F).
  assert (forall n Zs, get l n Zs -> exists n', get F n' Zs).
  intros. subst. eapply get_rev in H. eauto. clear Heql.
  general induction l.
  - reflexivity.
  - simpl.
    unfold renameApartFStep. let_pair_case_eq.
    simpl_pair_eqs. subst. simpl.
    simpl. rewrite list_union_start_swap.
    simpl.
    eapply union_eq_decomp; eauto.
    + edestruct H; eauto using get.
      rewrite H0; eauto. cset_tac; intuition.
    + eapply IHl; eauto using get.
Qed.

Lemma definedVars_renamedApart' ϱ G s
: definedVars (snd (renameApart' ϱ G s)) [=] fst (renameApart' ϱ G s).
Proof.
  revert ϱ G.
  sind s; destruct s; intros; simpl; repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
  repeat rewrite lookup_set_union; try rewrite freeVars_renameExp; eauto;
  repeat rewrite IH; eauto; try reflexivity.
  eapply union_eq_decomp; eauto.
  intros.
  rewrite <- definedVars_renameApartF; eauto.
  rewrite map_rev.
  rewrite <- list_union_rev; eauto.
Qed.


Lemma snd_renamedApartAnnF' G s
: (forall n Zs, get s n Zs -> forall G, snd (getAnn (renamedApartAnn (snd Zs) G)) [=] definedVars (snd Zs))
  -> snd (renamedApartAnnF renamedApartAnn G (nil, {}) s)[=]
        list_union
        (List.map
           (fun f : params * stmt =>
              (definedVars (snd f) ++ of_list (fst f))%set) s).
Proof.
  general induction s; simpl; eauto.
  - rewrite H; eauto using get. simpl.
    rewrite list_union_start_swap. rewrite IHs; intros; eauto using get.
    cset_tac; intuition.
Qed.

Lemma get_fst_renamedApartAnnF G F n ans
:  get (fst (renamedApartAnnF renamedApartAnn G (nil, {}) F)) n ans
   -> exists Zs G', get F n Zs
              /\ ans = renamedApartAnn (snd Zs) G'
              /\ G' = G ∪ of_list (fst Zs).
Proof.
  general induction F; simpl in * |- *; isabsurd. inv H.
  - do 2 eexists; split; eauto using get.
  - edestruct IHF as [? [? [? [? ?]]]]; eauto.
    do 2 eexists; split; eauto using get.
Qed.

Lemma get_fst_renameApartF G ϱ F n ans
:  get (fst (renameApartF renameApart' G ϱ F (nil, {}))) n ans
   -> exists ϱ' Zs G', get F (length F - S n) Zs
                 /\ snd ans = snd (renameApart' ϱ' G' (snd Zs))
                 /\ G ⊆ G'
                 /\ of_list (fst ans) ⊆ G'
                 /\ agree_on eq (freeVars (snd Zs) ∪ of_list (fst Zs)) (ϱ [fst Zs <-- fst ans]) ϱ'
                 /\ length (fst Zs) = length (fst ans)
                 /\ disj G (of_list (fst ans))
                 /\ unique (fst ans)
                 /\ G' [=] (G ++ snd (renameApartFRight renameApart' G ϱ (nil, {}) (drop (S n) (rev F)))) ++ (of_list (fst ans)).
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F).
  general induction l; simpl in * |- *; isabsurd.
  - unfold renameApartFStep in *.
    revert H; let_pair_case_eq; simpl_pair_eqs.
    inv H0; subst.
    + do 3 eexists; split; eauto using get.
      eapply get_rev. rewrite <- Heql. econstructor.
      simpl. split. reflexivity.
      split. cset_tac; intuition.
      split. eauto.
      split. eauto.
      split.
      rewrite fresh_list_length; eauto.
      split.
      intros.
      symmetry. eapply disj_2_incl.
      eapply fresh_list_spec. eapply fresh_spec. eauto.
      split.
      eapply fresh_list_unique, fresh_spec.
      eauto.
    + edestruct IHl as [? [? [? [? ?]]]]; eauto.
      instantiate (1:=rev (tl (rev F))). rewrite <- Heql. simpl. rewrite rev_involutive; eauto.
      rewrite <- Heql in *. simpl in *.
      assert (S (length (rev l)) = length (rev F)).
      rewrite <- Heql. simpl. rewrite rev_length; eauto.
      do 3 eexists; split; eauto using get.
      assert (length F = S (length (rev l))).
      rewrite rev_length.
      rewrite <- rev_length. rewrite <- Heql. eauto.
      exploit rev_swap. symmetry; eauto. simpl in *.
      rewrite X at 1. eapply get_app.
      rewrite H3. simpl. eauto.
Qed.

Lemma snd_renameApartAnn_fst s G ϱ G'
: snd (getAnn (renamedApartAnn (snd (renameApart' ϱ G s)) G')) [=] fst (renameApart' ϱ G s).
Proof.
  revert G ϱ G'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; simpl; eauto.
  - subst. rewrite (IH s); eauto.
  - subst. rewrite (IH s1); eauto. rewrite (IH s2); eauto.
  - subst. rewrite (IH s); eauto.
  - subst.
    let_pair_case_eq; simpl_pair_eqs; subst. simpl.
    rewrite (IH s0); eauto.
    eapply union_eq_decomp; eauto.
    rewrite snd_renamedApartAnnF'; eauto.
    rewrite <- definedVars_renameApartF; eauto using definedVars_renamedApart'.
    rewrite map_rev.
    rewrite <- list_union_rev; eauto.
    intros.
    eapply get_rev in H.
    edestruct get_fst_renameApartF as [? [? [? ?]]]; dcr; eauto.
    rewrite H3. rewrite definedVars_renamedApart'.
    eapply IH; eauto.
Qed.


Lemma snd_renamedApartAnn s G
 : snd (getAnn (renamedApartAnn s G)) [=] definedVars s.
Proof.
  sinduction s; simpl; repeat rewrite H; eauto.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl. rewrite H; eauto.
    eapply union_eq_decomp; eauto.
    rewrite snd_renamedApartAnnF'; eauto.
Qed.

Lemma snd_renamedApartAnnF G s
: snd (renamedApartAnnF renamedApartAnn G (nil, {}) s)[=]
      list_union
      (List.map
         (fun f : params * stmt =>
            (definedVars (snd f) ++ of_list (fst f))%set) s).
Proof.
  eapply snd_renamedApartAnnF'; eauto using snd_renamedApartAnn.
Qed.

Lemma renameApartAnn_decomp s G
: pe (getAnn (renamedApartAnn s G)) (G, snd (getAnn (renamedApartAnn s G))).
Proof.
  destruct s; simpl; try reflexivity.
  - let_pair_case_eq; simpl_pair_eqs; subst; simpl; eauto.
Qed.

Lemma length_fst_renamedApartAnnF G F
: length (fst (renamedApartAnnF renamedApartAnn G (nil, {}) F))
  = length F.
Proof.
  general induction F; simpl; eauto.
Qed.

Lemma ann_R_pe_notOccur G1 G2 G' s
:  disj (occurVars s) G'
   -> G1 [=] G2 \ G'
   -> ann_R (@pe var _)
           (renamedApartAnn s G1)
           (mapAnn (pminus G') (renamedApartAnn s G2)).
Proof.
  revert G1 G2 G'.
  sind s; destruct s; intros; simpl in * |- *; eauto using pe, ann_R with cset;
  try now (econstructor; reflexivity).
  - econstructor.
    + econstructor; eauto.
      repeat rewrite snd_renamedApartAnn; eauto.
    + eapply IH; eauto with cset.
      rewrite H0.
      assert (x ∉ G'). eauto with cset.
      revert H1; clear_all; cset_tac; intuition.
  - econstructor; eauto with cset.
    + repeat rewrite snd_renamedApartAnn; eauto.
      econstructor; eauto.
  - econstructor; eauto with cset. econstructor; eauto.
  - econstructor. econstructor; try rewrite <- H0; clear_all; cset_tac; intuition.
  - econstructor; eauto with cset.
    + econstructor; eauto.
      repeat rewrite snd_renamedApartAnn; eauto.
    + eapply IH; eauto with cset.
      assert (x ∉ G'). eauto with cset.
      rewrite H0. revert H1; clear_all; cset_tac; intuition.
  - intros.
    repeat let_pair_case_eq; subst; simpl.
    econstructor; eauto with cset.
    + repeat rewrite snd_renamedApartAnn.
      unfold pminus. econstructor; eauto.
      eapply union_eq_decomp; eauto.
      repeat rewrite snd_renamedApartAnnF; eauto.
    + rewrite List.map_length; eauto.
      repeat rewrite length_fst_renamedApartAnnF; eauto.
    + intros.
      inv_map H2.
      edestruct get_fst_renamedApartAnnF as [? [? ?]]; dcr; eauto. subst.
      edestruct get_fst_renamedApartAnnF as [? [? ?]]; dcr; try eapply H1; eauto. subst.
      get_functional; subst.
      eapply IH; eauto.
      * eapply disj_1_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union; eauto using map_get_1 with cset.
      * repeat rewrite minus_dist_union.
        rewrite H0.
        eapply union_eq_decomp; eauto.
        eapply disj_eq_minus; eauto.
        eapply disj_1_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto.
        cset_tac; intuition.
Qed.


Lemma freeVars_rename_exp_list ϱ Y
  : list_union (List.map Exp.freeVars (List.map (rename_exp ϱ) Y))[=]
               lookup_set ϱ (list_union (List.map Exp.freeVars Y)).
Proof.
  rewrite lookup_set_list_union; eauto using lookup_set_empty.
  repeat rewrite map_map. eapply fold_left_union_morphism; [|reflexivity].
  clear_all. general induction Y; simpl; eauto using AllInRel.PIR2, freeVars_renameExp.
Qed.

Fixpoint pw_disj X `{OrderedType X} (L:list (set X)) :=
  match L with
    | x::xs => disj x (list_union xs) /\ pw_disj xs
    | nil => True
  end.

Lemma renameApartF_pw_disj G' ϱ F
: pw_disj (List.map
             (fun f : params * stmt =>
                (definedVars (snd f) ++ of_list (fst f))%set)
             (fst (renameApartF renameApart' G' ϱ F (nil, {})))).
Proof.
  rewrite <- renameApartFRight_corr.
  generalize (rev F); intros.
  general induction l; simpl; eauto.
  unfold renameApartFStep. let_pair_case_eq; simpl_pair_eqs; simpl.
  split; eauto. subst.
  rewrite <- (rev_involutive l).
  rewrite renameApartFRight_corr.
  rewrite definedVars_renameApartF.
  rewrite definedVars_renamedApart'.
  symmetry.
  eapply disj_app; split.
  eapply disj_1_incl.
  eapply renameApart'_disj. cset_tac; intuition.
  symmetry. eapply disj_2_incl. eapply fresh_list_spec, fresh_spec.
  eauto. intros. eapply definedVars_renamedApart'.
Qed.

Lemma pw_disj_get X `{OrderedType X} (L:list (set X)) n s
: pw_disj L -> get L n s -> disj s (list_union (drop (S n) L)).
Proof.
  intros. general induction H1; simpl in * |- *; eauto.
Qed.

Lemma pw_disj_pairwise_disj X `{OrderedType X} (L:list (set X))
: pw_disj L -> pairwise_ne disj L.
Proof.
  intros. hnf; intros.
  exploit pw_disj_get; try eapply H2; eauto.
  exploit pw_disj_get; try eapply H3; eauto.
  decide (n < m).
  - eapply disj_2_incl; eauto. eapply incl_list_union.
    eapply drop_get. instantiate (2:=m - S n).
    orewrite (S n + (m - S n) = m); eauto. eauto.
  - symmetry. eapply disj_2_incl; eauto.
    eapply incl_list_union.
    eapply drop_get. instantiate (2:=n - S m).
    orewrite (S m + (n - S m) = n); eauto. eauto.
Qed.

Lemma renameApartF_length G ϱ F
: length (fst (renameApartF renameApart' G ϱ F (nil, {}))) = length F.
Proof.
  rewrite <- renameApartFRight_corr.
  rewrite <- (rev_length F).
  generalize (rev F); intros; clear F.
  general induction l; simpl; eauto.
  unfold renameApartFStep; simpl.
  let_pair_case_eq; simpl_pair_eqs; subst; simpl; eauto.
Qed.

Lemma freeVars_renamedApart' ϱ G s
: lookup_set ϱ (freeVars s) ⊆ G
  -> freeVars (snd (renameApart' ϱ G s)) [=] lookup_set ϱ (freeVars s).
Proof.
  revert G ϱ.
  sind s; destruct s; intros; simpl; repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
          repeat rewrite lookup_set_union; try rewrite freeVars_renameExp; eauto; try reflexivity.
  - rewrite IH; eauto.
    + rewrite lookup_set_update_union_minus; eauto.
      assert (fresh G ∉ lookup_set ϱ (freeVars s \ {{x}})).
      intro. eapply lookup_set_incl in H0; eauto.
      eapply H in H0. eapply fresh_spec; eauto.
      cset_tac; intuition.
      cset_tac; intuition.
    + rewrite lookup_set_update_in_union; eauto.
      rewrite <- H at 3. repeat rewrite lookup_set_union; eauto.
      cset_tac; intuition.
  - repeat rewrite IH; eauto.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto.
  - eapply freeVars_rename_exp_list.
  - rewrite IH; eauto.
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
  - eapply union_eq_decomp; eauto.
    + rewrite lookup_set_list_union; eauto; try reflexivity.
      rewrite map_map.
      intros.
      eapply list_union_indexwise_ext.
      intros.
      rewrite rev_length, renameApartF_length; eauto.
      intros.
      exploit get_range; eauto.
      eapply get_rev in H0.
      rewrite renameApartF_length in H0.

      intros.
      edestruct get_fst_renameApartF as [? [? [? ?]]]; dcr; eauto.
      orewrite (length s - S (length s - S n) = n) in H3. get_functional; subst.

      rewrite H5.
      rewrite IH; eauto.
      * { assert (freeVars (snd x0) [=]
                           (freeVars (snd x0) \ of_list (fst x0))
                           ∪ (of_list (fst x0) ∩ freeVars (snd x0))). {
            clear_all; cset_tac; intuition. simpl in *.
            decide (a ∈ of_list a0); intuition.
          }
          rewrite H1 at 1.
          repeat rewrite lookup_set_union; eauto.
          repeat rewrite minus_dist_union.
          pose proof (update_with_list_agree_inv _ _ _ H8 H7); eauto.
          assert ((freeVars (snd x0) ++ of_list (fst x0)) \ of_list (fst x0) [=]
                                                         freeVars (snd x0) \ of_list (fst x0)). {
            clear_all; cset_tac; intuition.
          }
          rewrite H11 in H2.
          rewrite <- lookup_set_agree; eauto.
          intros. rewrite disj_minus_eq.
          - setoid_rewrite diff_subset_equal at 2. cset_tac; intuition.
            rewrite <- incl_right in H7.
            rewrite meet_incl; [|reflexivity].
            rewrite <- lookup_set_agree; eauto.
            eapply update_with_list_lookup_set_incl; eauto.
          - eapply disj_1_incl; eauto.
            rewrite <- H. eapply lookup_set_incl; eauto.
            eapply incl_union_left. eapply incl_list_union.
            eapply map_get_1; eauto. eauto.
        }
      * assert (freeVars (snd x0) ⊆ (freeVars (snd x0) \ of_list (fst x0)) ∪ of_list (fst x0)). {
          clear_all; cset_tac; intuition.
          decide (a ∈ of_list (fst x0)); eauto.
        }
        rewrite H1. rewrite lookup_set_union; eauto.
        pose proof (update_with_list_agree_inv _ _ _ H8 H7); eauto.
        assert (freeVars (snd x0) \ of_list (fst x0) ⊆ (freeVars (snd x0) ++ of_list (fst x0)) \ of_list (fst x0)). {
          cset_tac; intuition.
        }
        rewrite <- H11 in H2.
        eapply union_subset_3; eauto.
        rewrite <- H4. rewrite <- H.
        rewrite <- lookup_set_agree; eauto.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union.
        eapply map_get_1; eauto. eauto.
        rewrite <- H6.
        rewrite <- incl_right in H7.
        rewrite <- lookup_set_agree; eauto.
        eapply update_with_list_lookup_set_incl; eauto.
    + rewrite IH; eauto. eapply incl_union_left. rewrite <- H.
      eapply lookup_set_incl; eauto.
Qed.



Lemma renameApart'_renamedApart (s:stmt) ϱ G G'
: lookup_set ϱ (freeVars s) ⊆ G
  -> G ⊆ G'
  -> renamedApart (snd (renameApart' ϱ G' s)) (renamedApartAnn (snd (renameApart' ϱ G' s)) G).
Proof.
  revert ϱ G G'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; simpl.
  - subst. econstructor; eauto using renameApartAnn_decomp.
    + rewrite H0. eauto using fresh_spec.
    + simpl in H.
      rewrite rename_exp_freeVars; eauto. etransitivity; eauto.
      eapply lookup_set_incl; eauto.
    + eapply IH; eauto.
      hnf; intros. eapply lookup_set_spec in H1; eauto; dcr.
      lud.
      * rewrite H4. cset_tac. left; eauto.
      * cset_tac; intuition. right. rewrite H4. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.
      * rewrite H0; eauto.
  - subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply renamedApartIf with (Ds := Gs1) (Dt := Gs2).
    + rewrite <- H. rewrite Exp.rename_exp_freeVars; eauto.
    + eapply disj_1_incl; eauto. eapply disj_2_incl.
      eapply (@renameApart'_disj ϱ (G' ∪ Gs1) s2).
      subst; eauto. eauto.
    + repeat rewrite snd_renameApartAnn_fst. subst; reflexivity.
    + subst. eapply (IH s1); eauto.
      etransitivity; eauto. eapply lookup_set_incl; eauto.
    + pose proof (@renameApart'_disj ϱ G' s1). rewrite H2 in H1.
      pose proof (@renameApart'_disj ϱ (G' ++ Gs1) s2). rewrite H3 in H4.
      assert (disj (occurVars (snd (renameApart' ϱ (G' ++ Gs1) s2))) Gs1). {
        rewrite occurVars_freeVars_definedVars.
        rewrite definedVars_renamedApart'.
        symmetry; apply disj_app; split; symmetry.
        - rewrite freeVars_renamedApart'.
          eapply disj_1_incl; eauto. rewrite <- H0.
          rewrite lookup_set_incl; eauto with cset.
          rewrite <- H0.
          rewrite lookup_set_incl; eauto with cset.
        - symmetry. setoid_rewrite incl_right at 1.
          eapply renameApart'_disj.
      }
      eapply @renamedApart_minus; [ eapply disj_2_incl; try reflexivity |eapply (IH s2); eauto |eapply ann_R_pe_notOccur].
      * eapply disj_2_incl; eauto. reflexivity.
      * rewrite <- H; eauto.
      * eauto.
      * rewrite disj_minus_eq; eauto. eauto using disj_1_incl.
    + rewrite renameApartAnn_decomp. rewrite snd_renameApartAnn_fst.
      subst; reflexivity.
    + rewrite renameApartAnn_decomp. rewrite <- H2.
      rewrite snd_renameApartAnn_fst.
      subst. reflexivity.
  - econstructor; [| reflexivity]. simpl in H.
    rewrite <- H.
    rewrite lookup_set_list_union; eauto.
    instantiate (1:={}).
    eapply fold_left_subset_morphism; try reflexivity.
    repeat rewrite map_map.
    eapply map_ext_get; intros.
    rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
    eapply lookup_set_empty; eauto.
  - econstructor; eauto. simpl in H. rewrite <- H.
    rewrite Exp.rename_exp_freeVars; eauto.
  - subst. econstructor; eauto using renameApartAnn_decomp.
    + rewrite H0; eauto using fresh_spec.
    + simpl in H.
      assert  (lookup_set ϱ
        (list_union (List.map Exp.freeVars Y)) [<=]G).
      rewrite <- H.
      eapply lookup_set_incl; eauto.
      rewrite <- H1.
      rewrite lookup_set_list_union; eauto.
      instantiate (1:={}).
      eapply fold_left_subset_morphism; try reflexivity.
      repeat rewrite map_map.
      eapply map_ext_get; intros.
      rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
      eapply lookup_set_empty; eauto.
    + eapply (IH s); eauto. simpl in *.
      hnf; intros. eapply lookup_set_spec in H1; eauto; dcr.
      lud.
      * rewrite H4. cset_tac. left; eauto.
      * cset_tac. right. rewrite H4. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.
      * rewrite H0; eauto.
  - simpl. subst s1.
    let_pair_case_eq. simpl_pair_eqs.
    subst. econstructor; eauto.
    Focus 7.
    rewrite snd_renamedApartAnnF.
    eapply union_eq_decomp.
    Lemma union_defVars_renameApartF_PIR2 G G' ϱ F
          :
             AllInRel.PIR2 Equal (zip defVars (fst (renameApartF renameApart' G' ϱ F (nil, {})))
                   (fst
                      (renamedApartAnnF renamedApartAnn G (nil, {})
                                        (fst (renameApartF renameApart' G' ϱ F (nil, {}))))))
                  (List.map
        (fun f : params * stmt =>
         (definedVars (snd f) ++ of_list (fst f))%set)
        (fst (renameApartF renameApart' G' ϱ F (nil, {})))).
    Proof.
      rewrite <- renameApartFRight_corr.
      remember (rev F). clear Heql F. general induction l; simpl; eauto.
      unfold renameApartFStep. let_pair_case_eq; simpl_pair_eqs.
      simpl. unfold defVars.
      econstructor.
      rewrite snd_renamedApartAnn; eauto. cset_tac; intuition.
      rewrite IHl; eauto.
    Qed.
    rewrite map_rev. rewrite <- list_union_rev.
    Lemma fst_renamedApartAnnF_app G F F'
    : fst (renamedApartAnnF renamedApartAnn G (nil, {}) (F ++ F'))
      = fst (renamedApartAnnF renamedApartAnn G (nil, {}) F)
            ++ fst (renamedApartAnnF renamedApartAnn G (nil, {}) F').
    Proof.
      general induction F; simpl; f_equal; eauto.
    Qed.
    Lemma fst_renamedApartAnnF_rev G F
    : fst (renamedApartAnnF renamedApartAnn G (nil, {}) (rev F))
      = rev (fst (renamedApartAnnF renamedApartAnn G (nil, {}) F)).
    Proof.
      general induction F; simpl; eauto.
      rewrite <- IHF. rewrite fst_renamedApartAnnF_app; simpl; eauto.
    Qed.
    Lemma union_defVars_renameApartF G G' ϱ F
          : list_union
              (zip defVars (fst (renameApartF renameApart' G' ϱ F (nil, {})))
                   (fst
                      (renamedApartAnnF renamedApartAnn G (nil, {})
                                        (fst (renameApartF renameApart' G' ϱ F (nil, {}))))))[=]
              snd (renameApartF renameApart' G' ϱ F (nil, {})).
    Proof.
      rewrite <- renameApartFRight_corr.
      remember (rev F). clear Heql. general induction l; simpl; eauto.
      unfold renameApartFStep. let_pair_case_eq; simpl_pair_eqs.
      simpl.
      rewrite list_union_start_swap. subst.
      rewrite IHl; eauto.
      eapply union_eq_decomp; eauto. unfold defVars. simpl.
      rewrite snd_renamedApartAnn.
      rewrite <- definedVars_renamedApart'. cset_tac; intuition.
    Qed.
    intros. rewrite fst_renamedApartAnnF_rev.
    rewrite zip_rev. rewrite <- list_union_rev.
    pose proof union_defVars_renameApartF.
    rewrite H1.
    pose proof definedVars_renameApartF.
    rewrite H2; eauto.
    eauto using definedVars_renamedApart'.
    rewrite renameApartF_length.
    rewrite length_fst_renamedApartAnnF.
    rewrite renameApartF_length; eauto.
    reflexivity.
    + repeat rewrite rev_length.
      repeat rewrite length_fst_renamedApartAnnF, renameApartF_length, rev_length; eauto.
      rewrite renameApartF_length; eauto.
    + intros.
      edestruct get_fst_renamedApartAnnF; eauto; dcr.
      get_functional; subst.
      assert (n < length s). eapply get_range in H5.
      rewrite rev_length in H5. rewrite renameApartF_length in H5. eauto.
      eapply get_rev in H5.
      rewrite renameApartF_length in H5.
      edestruct get_fst_renameApartF as [? [? []]]; eauto; dcr.
      rewrite H7. eapply IH; eauto with cset.
      assert (freeVars (snd x1) ⊆ (freeVars (snd x1) \ of_list (fst x1)) ∪ of_list (fst x1)).
      clear_all; cset_tac; intuition; simpl.
      decide (a ∈ of_list (fst x1)); eauto.
      rewrite H3. rewrite lookup_set_union; eauto.
      eapply union_subset_3; eauto.
      eapply incl_union_left.
      rewrite <- lookup_set_agree; eauto.
      rewrite <- H.
      eapply lookup_set_incl; eauto.
      eapply incl_union_left.
      eapply incl_list_union.
      eapply map_get_1; eauto. eauto.
      eapply update_with_list_agree_inv; eauto using agree_on_incl with cset.
      rewrite <- incl_right in H9.
      rewrite <- lookup_set_agree; eauto.
      eapply incl_union_right.
      eapply update_with_list_lookup_set_incl; eauto.
      rewrite H8; eauto.
      eapply union_subset_3; eauto. rewrite H0; eauto.
    + hnf; intros. unfold funConstr.
      edestruct get_fst_renamedApartAnnF; eauto; dcr.
      get_functional; subst.
      rewrite fst_renamedApartAnn.
      split. clear_all; cset_tac; intuition.
      eapply get_rev in H5.
      edestruct get_fst_renameApartF as [? [? []]]; eauto; dcr.
      repeat rewrite snd_renamedApartAnn.
      split; eauto.
      split. symmetry in H10. rewrite <- H0 in H10. eauto.
      rewrite definedVars_renamedApart'.
      eapply disj_1_incl. eapply renameApart'_disj.
      rewrite <- definedVars_renameApartF; intros; eauto using definedVars_renamedApart'.
      eapply incl_union_right.
      eapply incl_list_union.
      eapply map_get_1. eauto. cset_tac; intuition.
    + rewrite fst_renamedApartAnnF_rev.
      rewrite zip_rev.
      eapply pairwise_ne_rev.
      eapply pairwise_disj_PIR2.
      Focus 2. symmetry.
      eapply union_defVars_renameApartF_PIR2.
      eapply pw_disj_pairwise_disj.
      eapply renameApartF_pw_disj.
      rewrite length_fst_renamedApartAnnF; eauto.
    + eapply IH; eauto with cset.
      rewrite <- H.
      eapply lookup_set_incl; eauto.
    + eapply renameApartAnn_decomp.
Qed.

Lemma renameApartF_agree G F f g
: (forall n Zs, get F n Zs ->
           forall f g G, agree_on eq (freeVars (snd Zs)) f g
             -> renameApart' f G (snd Zs) = renameApart' g G (snd Zs))
  ->  agree_on eq
        (list_union
           (List.map
              (fun f0 : params * stmt => freeVars (snd f0) \ of_list (fst f0)) F)) f g
  -> renameApartF renameApart' G f F (nil, ∅) = renameApartF renameApart' G g F (nil, ∅).
Proof.
  repeat rewrite <- renameApartFRight_corr.
  remember (rev F); intros.
  assert (forall n Zs, get l n Zs -> exists n, get F n Zs).
  intros. eexists. eapply get_rev. rewrite <- Heql; eauto. clear Heql.
  general induction l; simpl; eauto.
  unfold renameApartFStep; repeat let_pair_case_eq; repeat simpl_pair_eqs; simpl.
  subst.
  erewrite IHl; eauto using get.
  edestruct H1; eauto using get. erewrite H; eauto.
  eapply update_with_list_agree; eauto.
  eapply agree_on_incl; eauto. eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
Qed.

Lemma renameApart'_agree G s f g
: agree_on eq (freeVars s) f g
  -> renameApart' f G s = renameApart' g G s.
Proof.
  revert G f g.
  sind s; destruct s; simpl in * |- *; intros; repeat let_pair_case_eq; try simpl_pair_eqs; subst.
  - erewrite (IH s); eauto. erewrite rename_exp_agree; eauto using agree_on_incl with cset.
    eapply agree_on_update_same; eauto with cset.
  - erewrite (IH s1); eauto using agree_on_incl with cset.
    erewrite (IH s2); eauto using agree_on_incl with cset.
    erewrite rename_exp_agree; eauto using agree_on_incl with cset.
  - do 2 f_equal. eapply map_ext_get_eq2; intros. eapply rename_exp_agree.
    eapply agree_on_incl; eauto. eapply incl_list_union. eapply map_get_1; eauto. eauto.
  - erewrite rename_exp_agree; eauto with cset.
  - erewrite map_ext_get_eq2; intros.
    erewrite (IH s); eauto using agree_on_incl, agree_on_update_same with cset.
    eapply rename_exp_agree.
    eapply agree_on_incl; eauto. eapply incl_union_right.
    eapply incl_list_union. eapply map_get_1; eauto. eauto.
  - erewrite (IH s0); eauto with cset.
    erewrite renameApartF_agree; eauto.
    eapply agree_on_incl; eauto with cset.
Qed.




Lemma rename_apart_alpha' G ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ G
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (renameApart' ϱ G s)) s.
Proof.
  revert G ϱ ϱ'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; subst;
  simpl in * |- *; eauto using alpha.

  - econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto with cset. eauto with cset.
    eapply IH; eauto.
    + rewrite <- H at 3. rewrite lookup_set_update_in_union; intuition.
    + eapply inverse_on_update_inverse. intuition.
      eapply inverse_on_incl; eauto. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                         lookup_set ϱ (freeVars s \ {{x}} ∪ Exp.freeVars e)).
      rewrite lookup_set_union; cset_tac; intuition.
      rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor; eauto.
    + eapply alpha_exp_sym. eapply Exp.alpha_exp_rename_injective.
      eapply inverse_on_incl; eauto. eapply incl_right.
    + eapply IH; eauto.
      * eapply Subset_trans; eauto. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_right.
      * eapply inverse_on_incl; eauto. rewrite union_assoc, union_comm. eapply incl_right.
    + eapply IH; eauto.
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
    + eapply IH; eauto.
      * rewrite <- H at 3. rewrite lookup_set_update_in_union; intuition.
      * eapply inverse_on_update_inverse. intuition.
        eapply inverse_on_incl; eauto. cset_tac; eauto.
        assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                           lookup_set ϱ (freeVars s \ {{x}} ∪ list_union (List.map Exp.freeVars Y))).
        rewrite lookup_set_union; cset_tac; intuition.
        rewrite H1, H. eapply fresh_spec; eauto.
  - econstructor.
    + rewrite rev_length, renameApartF_length; eauto.
    + intros. eapply get_rev in H1.
      rewrite renameApartF_length in H1.
      edestruct get_fst_renameApartF as [? [? [? ]]]; dcr; eauto.
      exploit (get_range H2).
      orewrite (length s - S (length s - S n) = n) in H4. get_functional; subst.
      eauto.
    + intros.
      eapply get_rev in H1.
      rewrite renameApartF_length in H1.
      edestruct get_fst_renameApartF as [? [? [? ]]]; dcr; eauto.
      exploit (get_range H2).
      orewrite (length s - S (length s - S n) = n) in H4. get_functional; subst.
      rewrite H6.
      erewrite renameApart'_agree. eapply IH; eauto.
      * rewrite lookup_set_update_with_list_in_union_length; eauto.
        eapply union_subset_3; eauto.
        rewrite <- H5.
        rewrite <- H.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      * eapply inverse_on_update_fresh; eauto.
        eapply inverse_on_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
        symmetry. eapply disj_1_incl; eauto.
        rewrite <- H. eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union. eapply map_get_1; eauto. reflexivity.
      * symmetry. eapply agree_on_incl; eauto with cset.
    + eapply IH; eauto.
      * rewrite <- H at 1.
        rewrite lookup_set_union; eauto.
      * eapply inverse_on_incl; eauto. eapply incl_right.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)
Definition rename_apart s := snd (renameApart' id (freeVars s) s).

Lemma rename_apart_renamedApart (s:stmt)
: renamedApart (rename_apart s)
               (renamedApartAnn (snd (renameApart' id (freeVars s) s)) (freeVars s)).
  eapply renameApart'_renamedApart; eauto. eapply lookup_set_on_id; eauto.
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
