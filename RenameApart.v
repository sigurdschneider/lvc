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
     (G' ∪ G'', stmtFun F'  s2')
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
                        let ans := renameApartAnn (snd Zs) (G ∪ snd anFG ∪ of_list (fst Zs)) in
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

Lemma list_union_indexwise_ext X `{OrderedType X} Y (f:Y->set X) Z (g:Z -> set X) L L'
: length L = length L'
  -> (forall n y z, get L n y -> get L' n z -> f y [=] g z)
  -> list_union (List.map f L) [=] list_union (List.map g L').
Proof.
  intros. length_equify.
  general induction H0; simpl; eauto.
  unfold list_union; simpl.
  repeat rewrite list_union_start_swap.
  rewrite IHlength_eq, H1; eauto using get; reflexivity.
Qed.

Lemma union_eq_decomp X `{OrderedType X} s s' t t'
: s [=] s' -> t [=] t' -> s ++ t [=] s' ++ t'.
Proof.
  cset_tac; intros; firstorder.
Qed.

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
      admit.
    + admit.
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

Lemma get_rev X (L:list X) n x
: get (rev L) n x ->
  get L (length L - S n) x.
Proof.
  intros.
  general induction L; simpl in *; isabsurd.
  edestruct get_app_cases; eauto; dcr.
  - exploit @get_length; eauto.
    rewrite rev_length in X0; simpl in *.
    orewrite (length L - n = S (length L - S n)).
    eauto using get.
  - rewrite rev_length in H2. orewrite (length L - n = 0).
    inv H1; isabsurd; eauto using get.
Qed.

Lemma snd_renameApartAnn_fst s G ϱ G'
: snd (getAnn (renamedApartAnn (snd (renameApart' ϱ G s)) G')) = fst (renameApart' ϱ G s).
Proof.
  revert G ϱ G'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; simpl; eauto.
  - subst. rewrite (IH s); eauto.
  - subst. rewrite (IH s1); eauto. rewrite (IH s2); eauto.
  - subst. rewrite (IH s); eauto.
  - subst. rewrite (IH s0); eauto.
    let_pair_case_eq; simpl_pair_eqs; subst; simpl.
    f_equal.
    rewrite <- renameApartFRight_corr.
    erewrite snd_renamedApartAnnF_fst; eauto.
    intros. eapply get_rev in H. eauto.
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
  - rewrite H; eauto using get. unfold list_union. simpl.
    rewrite list_union_start_swap. rewrite IHs; intros; eauto using get.
    cset_tac; intuition.
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

Hint Resolve prod_eq_intro : cset.

Lemma disj_not_in X `{OrderedType X} x s
: disj {x} s
  -> x ∉ s.
Proof.
  unfold disj; cset_tac.
  intro.
  eapply H0; eauto; intuition.
Qed.

Hint Resolve disj_not_in incl_singleton: cset.

Lemma length_fst_renamedApartAnnF G F
: length (fst (renamedApartAnnF renamedApartAnn G (nil, {}) F))
  = length F.
Proof.
  general induction F; simpl; eauto.
Qed.

Lemma get_fst_renamedApartAnnF G F n ans
:  get (fst (renamedApartAnnF renamedApartAnn G (nil, {}) F)) n ans
   -> exists Zs G', get F n Zs
              /\ ans = renamedApartAnn (snd Zs) G'
              /\ G' [=] G
                   ∪ list_union (List.map (fun f => (definedVars (snd f) ∪ of_list (fst f)))
                                          (drop (S n) F))
                   ∪ of_list (fst Zs).
Proof.
  general induction F; simpl in * |- *; isabsurd. inv H.
  - do 2 eexists; split; eauto using get.
    split; eauto.
    rewrite snd_renamedApartAnnF. simpl.
    clear_all; cset_tac; intuition.
  - edestruct IHF as [? [? [? [? ?]]]]; eauto.
    do 2 eexists; split; eauto using get.
Qed.

Lemma disj_eq_minus X `{OrderedType X} (s t u: set X)
: s [=] t
  -> disj t u
  -> s [=] t \ u.
Proof.
  unfold disj.
  cset_tac; intuition; eauto.
  - eapply H0; eauto.
  - eapply H1; intuition; eauto. eapply H0; eauto.
  - eapply H0; eauto.
Qed.

Lemma union_incl_split X `{OrderedType X} s t u
: s ⊆ u -> t ⊆ u -> s ∪ t ⊆ u.
Proof.
  cset_tac; intuition.
Qed.

Lemma list_union_drop_incl X `{OrderedType X} (L L':list (set X)) n
: list_union (drop n L) ⊆ list_union (drop n L')
  -> list_union (drop n L) ⊆ list_union L'.
Proof.
  intros; hnf; intros.
  eapply H0 in H1.
  edestruct list_union_get; eauto; dcr.
  eapply incl_list_union; eauto using get_drop; reflexivity.
  cset_tac; intuition.
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
      * eapply disj_1_incl; eauto. unfold list_union.
        eapply incl_union_left.
        eapply incl_list_union; eauto using map_get_1 with cset.
      * rewrite H11, H9.
        repeat rewrite minus_dist_union.
        setoid_rewrite union_assoc at 2.
        setoid_rewrite <- minus_dist_union.
        rewrite union_assoc.
        eapply union_eq_decomp; eauto.
        eapply disj_eq_minus; eauto.
        eapply disj_1_incl; eauto.
        eapply incl_union_left.
        eapply union_incl_split.
        rewrite drop_map.
        eapply list_union_drop_incl.
        repeat rewrite <- drop_map.
        eapply list_union_f_incl; intros.
        rewrite occurVars_freeVars_definedVars. cset_tac; intuition.
        eapply incl_list_union. eapply map_get_1; eauto.
        cset_tac; intuition.
Qed.


Lemma freeVars_rename_exp_list ϱ Y
  : list_union (List.map Exp.freeVars (List.map (rename_exp ϱ) Y))[=]
               lookup_set ϱ (list_union (List.map Exp.freeVars Y)).
Proof.
  unfold list_union. rewrite lookup_set_list_union; eauto using lookup_set_empty.
  repeat rewrite map_map. eapply fold_left_union_morphism; [|reflexivity].
  clear_all. general induction Y; simpl; eauto using AllInRel.PIR2, freeVars_renameExp.
Qed.

Lemma definedVars_renamedApart' ϱ G s
: definedVars (snd (renameApart' ϱ G s)) [=] fst (renameApart' ϱ G s).
Proof.
  revert ϱ G.
  sind s; destruct s; intros; simpl; repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
  repeat rewrite lookup_set_union; try rewrite freeVars_renameExp; eauto;
  repeat rewrite IH; eauto; try reflexivity.
  eapply union_eq_decomp; eauto.
  rewrite <- renameApartFRight_corr.
  remember (rev s).
  assert (forall n Zs, get l n Zs -> exists n', get s n' Zs).
  intros. subst. eapply get_rev in H. eauto. clear Heql.
  general induction l.
  - reflexivity.
  - simpl.
    unfold renameApartFStep. let_pair_case_eq.
    simpl_pair_eqs. subst. simpl.
    unfold list_union. simpl. rewrite list_union_start_swap.
    simpl.
    eapply union_eq_decomp; eauto.
    + edestruct H; eauto using get.
      rewrite IH; eauto. cset_tac; intuition.
    + eapply IHl; eauto using get.
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
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto. cset_tac; intuition.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto. cset_tac; intuition.
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
    + unfold list_union.
      rewrite lookup_set_list_union; eauto; try reflexivity.
      rewrite map_map.
      Lemma list_union_rev X `{OrderedType X} (L:list (set X)) s
      : fold_left union L s [=] fold_left union (rev L) s.
      Proof.
        general induction L; simpl; eauto.
        rewrite list_union_app.
        unfold list_union. simpl.
        rewrite IHL.
        repeat rewrite list_union_start_swap.
        cset_tac; intuition.
      Qed.
      intros. setoid_rewrite list_union_rev at 2.
      rewrite <- map_rev.
      eapply list_union_indexwise_ext.
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
      rewrite renameApartF_length; eauto.
      intros.
      (*
    rewrite IHs1, IHs2.
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
      rewrite fresh_list_length; eauto.*)
      intros.
Lemma get_fst_renameApartF G ϱ F n ans
:  get (fst (renameApartF renameApart' G ϱ F (nil, {}))) n ans
   -> exists ϱ' Zs G', get F (length F - S n) Zs
                 /\ snd ans = snd (renameApart' ϱ' G' (snd Zs))
                 /\ G ⊆ G'
                 /\ lookup_set ϱ' (of_list (fst Zs)) ⊆ of_list (fst ans)
                 /\ of_list (fst ans) ⊆ G'
                 /\ agree_on eq (freeVars (snd Zs) \ of_list (fst Zs)) ϱ ϱ'
                 /\ disj G (of_list (fst ans)).
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
      Lemma update_with_list_lookup_list_incl {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} Z Z'
: length Z = length Z'
  -> lookup_set (f [ Z <-- Z' ]) (of_list Z) ⊆ of_list Z'.
      Proof.
        intros. hnf; intros.
        eapply lookup_set_spec in H3; eauto; dcr.
        rewrite H6.
        eapply update_with_list_lookup_in; eauto.
      Qed.
      split.
      rewrite update_with_list_lookup_list_incl; eauto.
      rewrite fresh_list_length; eauto.
      split. eauto.
      split.
      symmetry.
      eapply update_with_list_agree_minus; eauto.
      rewrite fresh_list_length; eauto.
      Lemma lookup_set_update_disj {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
            `{Proper _ (_eq ==> _eq) f} Z Z' G
      : disj (of_list Z) G
        -> lookup_set (f [ Z <-- Z' ]) G [=] lookup_set f G.
      Proof.
        intros. hnf; intros.
        rewrite lookup_set_spec; eauto.
        split; intuition; dcr. rewrite H6.
        - rewrite lookup_set_update_not_in_Z; eauto.
          eapply lookup_set_spec; eauto.
        - eapply lookup_set_spec in H3; eauto; dcr.
          eexists x.
          rewrite lookup_set_update_not_in_Z; eauto.
      Qed.
      intros.
      symmetry. eapply disj_2_incl.
      eapply fresh_list_spec. eapply fresh_spec. eauto.
    + edestruct IHl as [? [? [? [? ?]]]]; eauto.
      instantiate (1:=rev (tl (rev F))). rewrite <- Heql. simpl. rewrite rev_involutive; eauto.
      rewrite <- Heql in *. simpl in *.
      assert (S (length (rev l)) = length (rev F)).
      rewrite <- Heql. simpl. rewrite rev_length; eauto.
      do 3 eexists; split; eauto using get.
      assert (length F = S (length (rev l))).
      rewrite rev_length.
      rewrite <- rev_length. rewrite <- Heql. eauto.
      Lemma rev_swap X (L L':list X)
      : rev L = L'
        -> L = rev L'.
      Proof.
        intros. subst. rewrite rev_involutive; eauto.
      Qed.
      exploit rev_swap. symmetry; eauto. simpl in *.
      rewrite X at 1. eapply get_app.
      rewrite H3. simpl. eauto.
Qed.
rewrite rev_length; eauto.
intros.
edestruct get_fst_renameApartF as [? [? [? ?]]]; dcr; eauto.
eapply get_rev in H1. get_functional; subst.
rewrite H5.
rewrite IH; eauto.
      * assert (freeVars (snd x0) [=] (freeVars (snd x0) \ of_list (fst x0)) ∪ (of_list (fst x0) ∩ freeVars (snd x0))).
        clear_all; cset_tac; intuition. simpl in *.
        decide (a ∈ of_list a0); intuition.
        rewrite H1 at 1. repeat rewrite lookup_set_union; eauto.
        repeat rewrite minus_dist_union.
        rewrite <- lookup_set_agree; eauto.
        Lemma disj_minus_eq X `{OrderedType X} (s t:set X)
        : disj s t
          -> s \ t [=] s.
        Proof.
          unfold disj; cset_tac; intuition; eauto.
        Qed.
        intros. rewrite disj_minus_eq.
        setoid_rewrite diff_subset_equal at 2. cset_tac; intuition.
        rewrite meet_incl; eauto.
        eapply disj_1_incl; eauto.
        rewrite <- H. eapply lookup_set_incl; eauto.
        eapply incl_union_left. eapply incl_list_union; eauto.
        eapply map_get_1; eauto. eauto.
      * assert (freeVars (snd x0) ⊆ (freeVars (snd x0) \ of_list (fst x0)) ∪ of_list (fst x0)).
        clear_all; cset_tac; intuition.
        decide (a ∈ of_list (fst x0)); eauto.
        rewrite H1. rewrite lookup_set_union; eauto. rewrite H6.
        eapply union_subset_3; eauto.
        rewrite <- H4. rewrite <- H.
        rewrite <- lookup_set_agree; eauto.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union; eauto.
        eapply map_get_1; eauto. eauto.
    + rewrite IH; eauto. eapply incl_union_left. rewrite <- H.
      eapply lookup_set_incl; eauto.
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
      assert (disj (occurVars (snd (renameApart' ϱ (G ++ Gs1) s2))) Gs1). {
        rewrite occurVars_freeVars_definedVars.
        rewrite definedVars_renamedApart'.
        symmetry; apply disj_app; split; symmetry.
        rewrite freeVars_renamedApart'.
        eapply disj_1_incl; eauto.
        rewrite lookup_set_incl; eauto with cset.
        rewrite lookup_set_incl; eauto with cset.
        symmetry. setoid_rewrite incl_right at 1.
        eapply renameApart'_disj.
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
  - econstructor; eauto. simpl in H. rewrite <- H.
    rewrite Exp.rename_exp_freeVars; eauto.
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
      eapply lookup_set_incl; eauto. intuition.
      rewrite fresh_list_length; eauto.
    + rewrite renameApartAnn_decomp.
      econstructor. rewrite union_comm. reflexivity.
      rewrite snd_renameApartAnn. subst; reflexivity.
    + pose proof (renameApart'_disj (ϱ [Z <-- fresh_list fresh G (length Z)])
                                    (G ++ of_list (fresh_list fresh G (length Z))) s1).
      rewrite H1 in H0.
      pose proof (renameApart'_disj ϱ (G ++ Gs1 ++ of_list (fresh_list fresh G (length Z))) s2).
      rewrite H2 in H3.
      assert (disj
     (occurVars
        (snd
           (renameApart' ϱ
              (G ++ Gs1 ++ of_list (fresh_list fresh G (length Z))) s2)))
     (Gs1 ++ of_list (fresh_list fresh G (length Z)))). {
        rewrite occurVars_freeVars_definedVars, disj_app.
        rewrite freeVars_renamedApart'. split.
        rewrite lookup_set_incl; eauto.
        rewrite H. symmetry. rewrite disj_app; split.
        symmetry. eauto with cset.
        rewrite definedVars_renamedApart'.
        eapply disj_1_incl. eapply renameApart'_disj.
        eauto with cset. eauto with cset.
        rewrite definedVars_renamedApart'.
        symmetry. rewrite disj_app; split.
        eapply disj_2_incl. eapply fresh_list_spec, fresh_spec.
        rewrite lookup_set_incl; eauto with cset.
        eapply disj_1_incl. eapply renameApart'_disj. eauto with cset.
        rewrite lookup_set_incl; eauto with cset.
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
