Require Import CSet Le.

Require Import Plus Util Map.
Require Import Env EnvTy IL Liveness Coherence Alpha Fresh Annotation.

Set Implicit Arguments.

Lemma lookup_set_list_union X `{OrderedType X } ϱ Y s s'
: lookup_set ϱ s[=]s' ->
  lookup_set ϱ (fold_left union (List.map Exp.freeVars Y) s)
             [=]  fold_left union (List.map (lookup_set ϱ) (List.map Exp.freeVars Y)) s'.
Proof.
  general induction Y; simpl; eauto.
  eapply IHY; eauto. rewrite lookup_set_union; eauto.
  rewrite H0. reflexivity. intuition.
Qed.

Instance fold_left_subset_morphism X `{OrderedType X}:
  Proper (list_eq Subset ==> Subset ==> Subset) (fold_left union).
Proof.
  unfold Proper, respectful; intros.
  general induction H0; simpl; eauto.
  - rewrite IHlist_eq; eauto. reflexivity.
    rewrite H0, H2. reflexivity.
Qed.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Fixpoint rename_apart' (ϱ:env var) (G:set var) (s:stmt) : set var * stmt:=
match s with
   | stmtExp x e s0 =>
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in
     let (G', s') := rename_apart' ϱ' (G ∪ {{y}}) s0 in
       (G', stmtExp y (rename_exp ϱ e) s')
   | stmtIf e s1 s2 =>
     let (G', s1') := rename_apart' ϱ G s1 in
     let (G'', s2') := rename_apart' ϱ G' s2 in
      (G'', stmtIf (rename_exp ϱ e) s1' s2')
   | stmtGoto l Y => (G, stmtGoto l (List.map (rename_exp ϱ) Y))
   | stmtReturn e => (G, stmtReturn (rename_exp ϱ e))
   | stmtExtern x f Y s =>
     let y := fresh G in
     let ϱ' := ϱ[x <- y] in
     let (G', s') := rename_apart' ϱ' (G ∪ {{y}}) s in
       (G', stmtExtern y f (List.map (rename_exp ϱ) Y) s')
   | stmtLet Z s1 s2 =>
     let Y := fresh_list fresh G (length Z) in
     let ϱZ := ϱ [ Z <-- Y ] in
     let (G', s1') := rename_apart' ϱZ (G ∪ of_list Y) s1 in
     let (G'', s2') := rename_apart' ϱ G' s2 in
     (G'', stmtLet Y s1'  s2')
   end.

Fixpoint rename_apart_rho (ϱ:env var) (s:stmt) : env var :=
match s with
   | stmtExp x e s0 =>
     let y := fresh (freeVars s0 \ {{x}}) in
     let ϱ' := ϱ[y <- x] in rename_apart_rho ϱ' s0
   | stmtIf x s1 s2 =>
     let ϱ' := rename_apart_rho ϱ s1 in rename_apart_rho ϱ' s2
   | stmtGoto l Y => ϱ
   | stmtReturn x => ϱ
   | stmtExtern x f Y s =>
     let y := fresh (freeVars s \ {{x}}) in
     let ϱ' := ϱ[x <- y] in
     rename_apart_rho ϱ' s
   | stmtLet Z s1 s2 =>
     let Y := fresh_list fresh (freeVars s1) (length Z) in
     let ϱZ := ϱ [ Z <-- Y ]  in
     let ϱ' := rename_apart_rho ϱZ s1 in rename_apart_rho ϱ' s2
   end.


Lemma rename_apart_incl ϱ G G' s
  : G ⊆ G' -> G ⊆ fst (rename_apart' ϱ G' s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - eapply IHs. cset_tac. left; eauto.
  - eapply IHs. cset_tac. left; eauto.
  - eapply IHs2. eapply IHs1. cset_tac. left; eauto.
Qed.

Lemma rename_apart_incl_eq ϱ G G' s G''
  : G ⊆ G' -> G'' = fst (rename_apart' ϱ G' s) -> G ⊆ G''.
Proof.
  intros; subst; eauto using rename_apart_incl.
Qed.

Lemma rename_apart_notOccur G G' ϱ s
  : G ⊆ G'
  -> lookup_set ϱ (freeVars s) ⊆ G'
  -> notOccur (G \ lookup_set ϱ (freeVars s)) (snd (rename_apart' ϱ G' s)).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; eauto using notOccur; subst; eauto.

  - econstructor; simpl in *.
    + intro. eapply fresh_spec. eapply H, minus_incl; eauto.
    + eapply notOccur_incl. Focus 2. eapply IHs. eapply Subset_refl.
      hnf; intros. eapply lookup_set_spec in H1. destruct H1; dcr.
      lud. cset_tac; eauto. eapply union_2. eapply H0. eapply lookup_set_spec. intuition.
      eexists x0; cset_tac; intuition. intuition.
      hnf; intros. cset_tac. left; eauto. intro.
      eapply H3. eapply lookup_set_spec. intuition.
      eapply lookup_set_spec in H1. destruct H1; dcr; eauto. lud.
      rewrite H5 in H2. exfalso. eapply fresh_spec; eauto.
      exists x0. cset_tac; intuition. intuition.
    + eapply notOccur_freeVars.
      cset_tac; intuition. eapply rename_exp_freeVars in H3.
      eapply H4. eapply lookup_set_incl; eauto; intuition. intuition.

  - econstructor.
    eapply Exp.notOccur_freeVars. cset_tac; intuition.
    eapply rename_exp_freeVars in H3; eauto.
    eapply H4. eapply lookup_set_spec; eauto. eapply lookup_set_spec in H3; eauto.
    destruct H3. eexists x. cset_tac; intuition; eauto.

    eapply notOccur_incl,IHs1.
    eapply incl_minus_lr; eauto. eapply lookup_set_incl. intuition.
    eapply union_incl_left, incl_left. reflexivity.

    simpl in *; eauto. rewrite <- H0. eapply lookup_set_incl; eauto.
    eapply union_incl_left, incl_left.

    eapply notOccur_incl, IHs2.
    eapply incl_minus_lr; eauto. eapply lookup_set_incl. intuition.
    eapply union_incl_left, incl_right.
    apply rename_apart_incl. reflexivity.
    apply rename_apart_incl.
    simpl in *. eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
    cset_tac; intuition.
  - econstructor. intros.
    edestruct map_get_4; eauto; dcr; subst.
    eapply Exp.notOccur_freeVars. cset_tac; intuition.
    eapply rename_exp_freeVars in H5; eauto.
    eapply H6. eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H5; eauto.
    destruct H5; dcr. eexists x0; intuition.
    eapply incl_list_union.
    eapply map_get_1; eauto. reflexivity. eauto.
  - econstructor.
    eapply Exp.notOccur_freeVars. cset_tac; intuition.
    eapply rename_exp_freeVars in H3; eauto.
  - econstructor; eauto.
    + intros.
      edestruct map_get_4; eauto; dcr; subst.
      eapply Exp.notOccur_freeVars. cset_tac; intuition.
      eapply rename_exp_freeVars in H5; eauto.
      eapply H6. eapply lookup_set_spec; eauto.
      eapply lookup_set_spec in H5; eauto.
      destruct H5; dcr. eexists x1; intuition.
      eapply incl_right. eapply incl_list_union.
      eapply map_get_1; eauto. reflexivity. eauto.
    + intro. eapply fresh_spec. eapply H, minus_incl; eauto.
    + eapply notOccur_incl.
      Focus 2.
      eapply IHs; try reflexivity.
      hnf; intros. eapply lookup_set_spec in H1; eauto. destruct H1; dcr.
      lud. cset_tac; eauto. eapply union_2. eapply H0.
      eapply lookup_set_spec; eauto. intuition.
      eexists x0; cset_tac; intuition. simpl.
      eapply incl_left. cset_tac; intuition.
      hnf; intros. cset_tac. left; eauto. intro.
      eapply H3. eapply lookup_set_spec. intuition.
      eapply lookup_set_spec in H1; eauto. destruct H1; dcr; eauto. lud.
      rewrite H5 in H2. exfalso. eapply fresh_spec; eauto.
      exists x0. cset_tac; intuition.
  - econstructor.
    + cset_tac; intuition. rewrite H in H1.
      eapply (not_in_empty a). rewrite <- (fresh_set_spec fresh fresh_spec G' (length Z)).
      cset_tac; eauto.
    + eapply notOccur_incl. Focus 2. eapply IHs1. reflexivity.
      rewrite lookup_set_update_with_list_in_union_length.
      eapply incl_union_lr. simpl in *. eapply Subset_trans;try eassumption.
      eapply lookup_set_incl. intuition.  cset_tac; eauto. reflexivity. intuition.
      rewrite fresh_list_length; eauto.

      hnf; intros. cset_tac. left; eauto. intro.
      eapply lookup_set_spec in H1.
      destruct H1; dcr. decide(x ∈ of_list Z).
      eapply (update_with_list_lookup_in ϱ) with (Z':=fresh_list fresh G' (length Z)) in i; eauto.
      rewrite <- H5 in i. apply (not_in_empty a).
      eapply fresh_set_spec. eapply fresh_spec. cset_tac; eauto.
      rewrite fresh_list_length; eauto.
      eapply H3. eapply lookup_set_spec. intuition.
      erewrite update_with_list_no_update in H5; eauto. eexists x.
      split; eauto. cset_tac; eauto.
      eapply update_with_list_proper.
    + eapply notOccur_incl. Focus 2. eapply IHs2. reflexivity.
      eapply Subset_trans. Focus 2. eapply rename_apart_incl. reflexivity.
      eapply Subset_trans. Focus 2. eapply union_subset_1.
      simpl in H0. rewrite <- H0. eapply lookup_set_incl. intuition. cset_tac.
      intuition.
      simpl in *. eapply Subset_trans. Focus 2. rewrite <- rename_apart_incl.
      Focus 2. reflexivity. reflexivity.
      eapply incl_minus_lr. cset_tac; intuition.
      eapply lookup_set_incl; cset_tac; intuition.
Qed.

Opaque to_list.

Fixpoint ssa_ann (s:stmt) (G:set var) : ann (set var * set var) :=
  match s with
    | stmtExp x e s =>
      let an := ssa_ann s (G ∪ {{x}}) in
      ann1 (G,snd (getAnn an)) an
    | stmtIf e s t =>
      let ans := ssa_ann s G in
      let ant := ssa_ann t G in
      ann2 (G, snd (getAnn ans) ∪ snd (getAnn ant)) ans ant
    | stmtReturn e =>
      ann0 (G, G)
    | stmtGoto f Y =>
      ann0 (G, G)
    | stmtExtern x f Y s =>
      let an := ssa_ann s (G ∪ {{x}}) in
      ann1 (G,snd (getAnn an)) an
    | stmtLet Z s t =>
      let ans := ssa_ann s (G ∪ of_list Z) in
      let ant := ssa_ann t G in
      ann2 (G, snd (getAnn ans) ∪ snd (getAnn ant)) ans ant
  end.

Instance pe_trans X `{OrderedType X} : Transitive (@pe _ _).
Proof.
  hnf; intros ? ? ? B C.
  eapply prod_Equivalence_obligation_3; eauto using Equal_ST.
Qed.

Instance getAnn_ann_R_morphism A (R:A->A->Prop)
: Proper (ann_R R ==> R) (getAnn).
Proof.
  unfold Proper, respectful; intros.
  inv H; simpl; eauto.
Qed.

Instance ssa_ann_morph
: Proper (eq ==> Equal ==> ann_R (@pe _ _ )) ssa_ann.
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

Lemma ssa_ann_decomp s G
: pe (getAnn (ssa_ann s G)) (G, snd (getAnn (ssa_ann s G))).
Proof.
  destruct s; simpl; try reflexivity.
Qed.

Lemma ssa_ann_app_incl s G G' G''
: G' ∪ G'' [=] G
  -> snd (getAnn (ssa_ann s G)) [=] G' ++ snd (getAnn (ssa_ann s G'')).
Proof.
  intros. general induction s; simpl.
  - rewrite IHs. reflexivity. rewrite <- H. rewrite union_assoc. reflexivity.
  - rewrite (IHs1 _ _ _ H) at 1.
    erewrite (IHs2 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    symmetry.
    erewrite (IHs2 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    (* rewrite (IHs1 _ _ _ H) at 1. *)
    rewrite <- H.
    clear_all; cset_tac; intuition.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - rewrite IHs. reflexivity. rewrite <- H. rewrite union_assoc. reflexivity.
  - erewrite (IHs2 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    erewrite (IHs1 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    symmetry.
    erewrite (IHs2 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    erewrite (IHs1 _ _ {}); [|rewrite union_comm, empty_neutral_union; reflexivity].
    rewrite <- H. clear_all; cset_tac; intuition.
Qed.

Lemma rename_apart_fst_incl ϱ s G
: G ⊆ fst (rename_apart' ϱ G s).
Proof.
  intros.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto; try reflexivity; try now (rewrite <- IHs; cset_tac; intuition).
  - rewrite <- IHs2, <- IHs1; reflexivity.
  - rewrite <- IHs2, <- IHs1. cset_tac; intuition.
Qed.

Lemma rename_apart_fst_incl_app ϱ s G
: fst (rename_apart' ϱ G s) [=] fst (rename_apart' ϱ G s) ∪ G.
Proof.
  pose proof (@rename_apart_fst_incl ϱ s G).
  cset_tac; intuition.
Qed.

Lemma ssa_ann_rename_apart s G ϱ
: snd (getAnn (ssa_ann (snd (rename_apart' ϱ G s)) G)) [=] fst (rename_apart' ϱ G s).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto; try reflexivity.
  - rewrite IHs1 at 1. rewrite <- IHs2. rewrite <- ssa_ann_app_incl. reflexivity.
    rewrite rename_apart_fst_incl_app. cset_tac; intuition.
  - rewrite <- IHs2. rewrite IHs1 at 1.
    rewrite <- ssa_ann_app_incl. reflexivity.
    symmetry.
    rewrite rename_apart_fst_incl_app.
    cset_tac; intuition.
Qed.



Lemma ssa_ann_rename_apart' s G G' ϱ
: G ⊆ G'
  -> snd (getAnn (ssa_ann (snd (rename_apart' ϱ G' s)) G)) [=] fst (rename_apart' ϱ G' s) \ (G' \ G).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl; subst; eauto; try reflexivity.
  - rewrite IHs at 1. cset_tac; intuition.
    eapply H0; intros. intuition.
    eapply fresh_spec. instantiate (1:=G'). rewrite H2. eauto.
    rewrite H. reflexivity.
  - rewrite IHs1. rewrite IHs2.
    rewrite rename_apart_fst_incl_app at 3.
    cset_tac; intuition.
    eapply rename_apart_fst_incl; eauto.
    decide ( a \In fst (rename_apart' ϱ G' s1)); intuition.
    rewrite H. eapply rename_apart_fst_incl; eauto. eauto.
  - cset_tac; intuition. decide (a ∈ G); intuition.
  - cset_tac; intuition. decide (a ∈ G); intuition.
  - rewrite IHs; try reflexivity. cset_tac; intuition.
    eapply H0; intros; intuition.
    eapply fresh_spec. instantiate (1:=G'). rewrite H2. eauto.
    rewrite H. reflexivity.
  - rewrite IHs2. rewrite IHs1.
    cset_tac; intuition.
    + eapply rename_apart_fst_incl; eauto.
    + eapply H1; intros. destruct H3; eauto; split; eauto.
      exploit (fresh_list_spec fresh fresh_spec G' (length Z) a); dcr. cset_tac; intuition.
    + eapply H1; intros.
      eapply rename_apart_fst_incl; eauto. cset_tac; intuition. eauto.
    + decide ( a \In
                 fst
                 (rename_apart' (ϱ [Z <-- fresh_list fresh G' (length Z)])
                                (G' ++ of_list (fresh_list fresh G' (length Z))) s1)); intuition.
    + rewrite H. reflexivity.
    + rewrite <- rename_apart_fst_incl. rewrite H. eapply incl_left.
Qed.

Instance ann_R_trans A R `{Transitive A R} : Transitive (ann_R R).
Proof.
  hnf; intros ? ? ? B C.
  general induction B; inv C; econstructor; eauto.
Qed.

Instance ann_R_ann1_pe_morphism X `{OrderedType X}
: Proper (@pe X _ ==> ann_R (@pe X _) ==> ann_R (@pe X _)) (@ann1 _).
Proof.
  unfold Proper, respectful; intros.
  econstructor; eauto.
Qed.

Instance pminus_morphism
: Proper (Equal ==> (@pe _ _) ==> (@pe _ _) ) pminus.
Proof.
  unfold Proper, respectful; intros.
  inv H0; simpl; econstructor. rewrite H1, <- H. reflexivity.
  rewrite H2, H. reflexivity.
Qed.

Instance mapAnn_pminus_morphism G'
  : Proper (ann_R (@pe _ _) ==> ann_R (@pe _ _)) (mapAnn (pminus G')).
Proof.
  unfold Proper, respectful; intros.
  general induction H; simpl.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
  - econstructor; eauto.
    + rewrite H. reflexivity.
Qed.

Lemma ann_R_pe_notOccur G G' s
:  notOccur G' s
   -> G \ G' [=] G
   -> ann_R (@pe var _)
           (ssa_ann s G)
                     (mapAnn (pminus G') (ssa_ann s (G ∪ G'))).
Proof.
  intros. general induction H; simpl; try now (econstructor; reflexivity).
  - assert ((G ++ G') ++ {x; {}} [=] (G ++ {{ x }}) ++ G'). {
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
      eapply H; cset_tac; eauto.
    + rewrite H3.
      eapply IHnotOccur.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition.
      eapply H. cset_tac; eauto.
  - econstructor; eauto.
    rewrite IHnotOccur1, IHnotOccur2; eauto.
    repeat rewrite getAnn_mapAnn.
    unfold pminus.
    repeat let_pair_case_eq; simpl; eauto.
    econstructor; try reflexivity.
    rewrite <- H2. clear_all; cset_tac; intuition.
    rewrite minus_dist_union. reflexivity.
  - econstructor. econstructor; rewrite <- H0; clear_all; cset_tac; intuition.
  - econstructor. econstructor; rewrite <- H0; clear_all; cset_tac; intuition.
  - assert ((G ++ G') ++ {x; {}} [=] (G ++ {{ x }}) ++ G'). {
      cset_tac; intuition.
    }
    econstructor.
    + rewrite H3. rewrite IHnotOccur.
      rewrite getAnn_mapAnn. unfold pminus.
      let_pair_case_eq; simpl.
      econstructor; try reflexivity.
      rewrite <- H2; clear_all; cset_tac; intuition.
      rewrite <- H2; revert H0; clear_all; cset_tac; intuition.
      eapply H0; cset_tac; eauto.
    + rewrite H3.
      eapply IHnotOccur.
      rewrite <- H2; revert H0; clear_all; cset_tac; intuition.
      eapply H0; cset_tac; eauto.
  - assert ((G ++ G') ++ of_list Z [=] (G ++ of_list Z) ++ G'). {
      cset_tac; intuition.
    }
    econstructor; eauto.
    + rewrite H3. rewrite IHnotOccur1.
      rewrite getAnn_mapAnn. unfold pminus.
      let_pair_case_eq; simpl.
      econstructor. rewrite <- H2; clear_all; cset_tac; intuition.
      rewrite IHnotOccur2, getAnn_mapAnn.
      unfold pminus. let_pair_case_eq; simpl.
      rewrite minus_dist_union. reflexivity.
      eauto.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition; eauto.
    + rewrite H3.
      eapply IHnotOccur1.
      rewrite <- H2. revert H; clear_all; cset_tac; intuition; eauto.
Qed.


Lemma rename_apart_ssa' (s:stmt) ϱ G
  : lookup_set ϱ (freeVars s) ⊆ G
  -> ssa (snd (rename_apart' ϱ G s)) (ssa_ann (snd (rename_apart' ϱ G s)) G).
Proof.
  general induction s; simpl; repeat let_pair_case_eq; simpl.
  - subst. econstructor; eauto using fresh_spec, ssa_ann_decomp.
    + simpl in H.
      rewrite rename_exp_freeVars; eauto. etransitivity; eauto.
      eapply lookup_set_incl; eauto.
    + eapply IHs. simpl in *.
      hnf; intros. eapply lookup_set_spec in H0; eauto; dcr.
      lud.
      * rewrite H3. cset_tac. right; eauto.
      * rewrite union_comm. eapply incl_right. rewrite H3. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.
  - subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply ssaIf with (Ds := Gs1) (Dt := (Gs2 \ (Gs1 \ G))).
    + rewrite <- H. rewrite Exp.rename_exp_freeVars; eauto.
      eapply lookup_set_incl; eauto.
    + eapply minus_incl_meet_special. subst; eapply rename_apart_incl. reflexivity.
      subst. eapply rename_apart_incl; reflexivity.
    + rewrite minus_incl_special. subst.
      * rewrite <- ssa_ann_rename_apart.
        rewrite ssa_ann_app_incl; try reflexivity.
        rewrite <- ssa_ann_rename_apart.
        rewrite ssa_ann_rename_apart.
        rewrite rename_apart_fst_incl_app at 2. reflexivity.
      * subst. eapply rename_apart_incl. reflexivity.
    + subst. eapply IHs1. etransitivity; eauto. eapply lookup_set_incl; eauto.
      eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_1.
    + {
        assert (G [=] (G \ (Gs1 \ G))) by eapply minus_minus_eq.
        assert (Gs2 \ (Gs1 \ G) [=] (Gs2 \ (Gs1 \ G)) \ (Gs1 \ G))
          by eapply minus_idem.
        rewrite H0.
        eapply ssa_minus. instantiate (1:=Gs1\G).
        -  eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
          + eapply Subset_trans.
            * rewrite minus_idem. reflexivity.
            * eapply incl_minus_lr; try reflexivity.
              eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
              eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
          + eapply incl_minus.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
              eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
            * subst. eapply rename_apart_incl. reflexivity.
        - eapply IHs2.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
              eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
            * subst. eapply rename_apart_incl. reflexivity.
        -
          intros. rewrite <- H0.
          assert (G [=] (Gs1 \ (Gs1 \ G))). {
          pose proof (@rename_apart_fst_incl ϱ s1 G). rewrite H1 in H4.
          revert H4; clear_all; cset_tac; intuition.
          decide (a ∈ G); eauto. exfalso. eauto.
          }
          assert (Gs1 [=] ((Gs1 \ (Gs1 \ G)) ++ (Gs1 \ G))). {
          pose proof (@rename_apart_fst_incl ϱ s1 G). rewrite H1 in H5.
          revert H4; clear_all; cset_tac; intuition.
          decide (a ∈ G); intuition.
          }
          rewrite H4 at 1. rewrite H5 at 6. eapply ann_R_pe_notOccur.
          eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
          + eapply Subset_trans.
            * rewrite minus_idem. reflexivity.
            * eapply incl_minus_lr; try reflexivity.
              eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
              eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
          + eapply incl_minus.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
              eapply Subset_trans; [| eapply union_subset_1]. eapply union_subset_2.
            * subst. eapply rename_apart_incl. reflexivity.
          + rewrite <- minus_idem. reflexivity.
      }
    + rewrite ssa_ann_decomp. rewrite ssa_ann_rename_apart.
      subst; reflexivity.
    + rewrite ssa_ann_decomp. rewrite <- H2.
      rewrite ssa_ann_rename_apart'. reflexivity.
      subst. eapply rename_apart_fst_incl.

  - econstructor. simpl in H.
    rewrite <- H.
    unfold list_union. rewrite lookup_set_list_union.
    instantiate (1:={}).
    eapply fold_left_subset_morphism; try reflexivity.
    repeat rewrite map_map.
    eapply map_ext_get; intros.
    rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
    hnf; intros. rewrite map_spec; eauto. cset_tac; intuition.
    destruct H0; cset_tac; eauto. reflexivity.
  - econstructor. simpl in H. rewrite <- H.
    rewrite Exp.rename_exp_freeVars; eauto.
    eapply lookup_set_incl; eauto.
    reflexivity. reflexivity.
  - subst. econstructor; eauto using fresh_spec, ssa_ann_decomp.
    + simpl in H.
      assert  (lookup_set ϱ
        (list_union (List.map Exp.freeVars Y)) [<=]G).
      rewrite <- H.
      eapply lookup_set_incl; eauto.
      rewrite <- H0.
      unfold list_union. rewrite lookup_set_list_union.
      instantiate (1:={}).
      eapply fold_left_subset_morphism; try reflexivity.
      repeat rewrite map_map.
      eapply map_ext_get; intros.
      rewrite <- Exp.rename_exp_freeVars; eauto; reflexivity.
      hnf; intros. rewrite map_spec; eauto. cset_tac; intuition.
      destruct H1; cset_tac; eauto.
    + eapply IHs. simpl in *.
      hnf; intros. eapply lookup_set_spec in H0; eauto; dcr.
      lud.
      * rewrite H3. cset_tac. right; eauto.
      * rewrite union_comm. eapply incl_right. rewrite H3. eapply H.
        eapply lookup_set_spec; eauto. eexists x0. split; eauto.
        eapply union_2. eapply in_in_minus; eauto. cset_tac; intuition.

  - simpl. subst s0 s4. simpl in H. simpl. rename s3 into Gs2. rename s into Gs1.
    eapply ssaLet with (Ds:=Gs1) (Dt:=Gs2 \ (Gs1 \ G)).
    + eapply fresh_set_spec. eapply fresh_spec.
    + eapply  minus_incl_meet_special; eauto using rename_apart_incl_eq, incl_refl.
      subst. eapply rename_apart_incl. eapply incl_left.
      subst. eapply rename_apart_incl. eapply Subset_refl.
    + rewrite ssa_ann_rename_apart; try reflexivity.
      rewrite H1.
      rewrite ssa_ann_rename_apart'. rewrite H2. reflexivity.
      subst Gs1.
      rewrite <- rename_apart_fst_incl. eapply incl_left.
    + eapply IHs1.
      rewrite lookup_set_update_with_list_in_union_length; eauto.
      eapply incl_union_lr; eauto. rewrite <- H.
      eapply lookup_set_incl; eauto. intuition. reflexivity.
      rewrite fresh_list_length; eauto.
    + rewrite ssa_ann_decomp.
      econstructor. rewrite union_comm. reflexivity.
      rewrite ssa_ann_rename_apart. subst; reflexivity.
    +  {
        assert (G [=] (G \ (Gs1 \ G))) by eapply minus_minus_eq.
        assert (Gs2 \ (Gs1 \ G) [=] (Gs2 \ (Gs1 \ G)) \ (Gs1 \ G))
          by eapply minus_idem.
        rewrite H0.
        eapply ssa_minus. instantiate (1:=Gs1\G).
        -  eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
          + eapply Subset_trans.
            * rewrite minus_idem. reflexivity.
            * eapply incl_minus_lr; try reflexivity.
              eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
          + eapply incl_minus.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
            * subst. eapply rename_apart_incl. eapply incl_left.
        - eapply IHs2.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
            * subst. eapply rename_apart_incl. eapply incl_left.
        -
          intros. rewrite <- H0.
          assert (G [=] (Gs1 \ (Gs1 \ G))). {
            assert (G ⊆ Gs1). rewrite <- H1.
            rewrite <- rename_apart_fst_incl. eapply incl_left.
            revert H4; clear_all; cset_tac; intuition.
            decide (a ∈ G); eauto. exfalso. eauto.
          }
          assert (Gs1 [=] ((Gs1 \ (Gs1 \ G)) ++ (Gs1 \ G))). {
            assert (G ⊆ Gs1). rewrite <- H1.
            rewrite <- rename_apart_fst_incl. eapply incl_left.
            revert H5; clear_all; cset_tac; intuition.
            decide (a ∈ G); intuition.
          }
          rewrite H4 at 1. rewrite H5 at 6. eapply ann_R_pe_notOccur.
          eapply notOccur_incl; try eapply rename_apart_notOccur with (G:=Gs1 \ G).
          + eapply Subset_trans.
            * rewrite minus_idem. reflexivity.
            * eapply incl_minus_lr; try reflexivity.
              eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
          + eapply incl_minus.
          + eapply Subset_trans.
            * eapply Subset_trans; eauto. eapply lookup_set_incl; eauto.
            * subst. eapply rename_apart_incl. eapply incl_left.
          + rewrite <- minus_idem. reflexivity.
      }
    + rewrite ssa_ann_decomp. econstructor. reflexivity.
      rewrite ssa_ann_rename_apart'. rewrite H2. reflexivity.
      rewrite <- H1. rewrite <- rename_apart_fst_incl.
      eapply incl_left.
    + eapply fresh_list_unique. eapply fresh_spec.
Qed.

Lemma rename_apart_alpha' G ϱ ϱ' s
  : lookup_set ϱ (freeVars s) ⊆ G
  -> inverse_on (freeVars s) ϱ ϱ'
  -> alpha ϱ' ϱ (snd (rename_apart' ϱ G s)) s.
Proof.
  general induction s; simpl; repeat let_pair_case_eq; subst; simpl in * |- *; eauto using alpha.

  - econstructor. eapply alpha_exp_sym. eapply alpha_exp_rename_injective.
    eapply inverse_on_incl; eauto. cset_tac; eauto.
    eapply IHs.
    + rewrite lookup_set_update_in_union.
      eapply incl_union_lr; try reflexivity. rewrite <- H.
      eapply lookup_set_incl. intuition. cset_tac; eauto. intuition.
    + eapply inverse_on_update_inverse. intuition.
      eapply inverse_on_incl; eauto. cset_tac; eauto.
      assert (lookup_set ϱ (freeVars s \ {{x}}) ⊆
                         lookup_set ϱ (freeVars s \ {{x}} ∪ Exp.freeVars e)).
      eapply lookup_set_incl. intuition. cset_tac; eauto.
      intro. eapply H1 in H2. eapply H in H2.
      eapply fresh_spec in H2. eauto.
  - econstructor; eauto.
    + eapply alpha_exp_sym. eapply Exp.alpha_exp_rename_injective.
      eapply inverse_on_incl; eauto. eapply incl_right.
    + eapply IHs1.
      * eapply Subset_trans; eauto. eapply lookup_set_incl; [intuition|].
        rewrite union_assoc, union_comm. eapply incl_right.
      * eapply inverse_on_incl; eauto. rewrite union_assoc, union_comm. eapply incl_right.
    + eapply IHs2; eauto.
      * eapply Subset_trans; eauto using rename_apart_incl. eapply lookup_set_incl; [intuition|].
        rewrite union_comm at 1. rewrite <- union_assoc. eapply incl_right.
      * eapply inverse_on_incl; eauto.
        rewrite union_comm at 1. rewrite <- union_assoc. eapply incl_right.
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
      * rewrite lookup_set_update_in_union.
        eapply incl_union_lr; try reflexivity. rewrite <- H.
        eapply lookup_set_incl. intuition. cset_tac; eauto. intuition.
      * eapply inverse_on_update_inverse. intuition.
        eapply inverse_on_incl; eauto. cset_tac; eauto.
        rewrite lookup_set_incl; [ | eauto | eapply incl_left; eauto].
        erewrite H.
        eapply fresh_spec.
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
        hnf; intros. intro. eapply lookup_set_spec in H2.
        destruct H2; dcr; cset_tac.
        pose proof (fresh_list_spec fresh fresh_spec G (length Z)).
        assert (x ∈ G). rewrite <- H.
        eapply lookup_set_spec. intuition.
        eexists x0. cset_tac; intuition.
        eapply (not_in_empty x).
        eapply fresh_list_spec. eapply fresh_spec. cset_tac; eauto. intuition.
    + eapply IHs2.
      * eapply rename_apart_incl. eapply Subset_trans; [| eapply  union_subset_1].
        eapply Subset_trans; eauto. eapply lookup_set_incl;[intuition| eapply incl_right].
      * eapply inverse_on_incl; eauto. eapply incl_right.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)
Definition rename_apart s := snd (rename_apart' id (freeVars s) s).

Lemma rename_apart_ssa (s:stmt)
  : ssa (rename_apart s) (ssa_ann (snd (rename_apart' id (freeVars s) s)) (freeVars s)).
  eapply rename_apart_ssa'. eapply lookup_set_on_id. reflexivity.
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
