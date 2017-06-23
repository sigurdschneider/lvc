Require Import CSet Util Map.
Require Import Env IL Alpha StableFresh Annotation RenamedApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint AppExpFree.
Require Import RenamedApart RenamedApartAnn.
Require Import Infra.PartialOrder CSetPartialOrder AnnotationLattice FreshGen.

Export RenamedApart.

Set Implicit Arguments.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Definition renameApartFStep {Fi} (FG:FreshGen Fi)
           (renameApart': FreshGen Fi -> Fi -> env var -> stmt -> Fi * stmt)
           ϱ :=
  (fun YLfresh (Zs:params*stmt) =>
     let '(YL, fi) := YLfresh in
     let (Y, fi) := fresh_list FG fi (fst Zs) in
     let ϱZ := ϱ [ fst Zs <-- Y ] in
     let '(fresh, s1') := renameApart' FG fi ϱZ (snd Zs) in
     ((Y, s1')::YL,
      fresh)).

Definition renameApartF Fi (FG:FreshGen Fi)
           renameApart'
           ϱ
           := fold_left (renameApartFStep FG renameApart' ϱ).

Definition renameApartFRight  Fi (FG:FreshGen Fi)
           renameApart' ϱ
           := fold_right (fun x y => renameApartFStep FG renameApart' ϱ y x).

Lemma renameApartFRight_corr  Fi (FG:FreshGen Fi)
      renameApart' ϱ s F
: renameApartFRight FG renameApart' ϱ s (rev F) =
  renameApartF FG renameApart' ϱ F s.
Proof.
  unfold renameApartF, renameApartFRight.
  erewrite <- fold_left_rev_right; eauto.
Qed.

Fixpoint renameApart {Fi} (FG:FreshGen Fi) (fi:Fi) (ϱ:env var) (s:stmt) : Fi * stmt:=
match s with
   | stmtLet x e s0 =>
     let (y, fi) := fresh FG fi x in
     let ϱ' := ϱ[x <- y] in
     let '(fi, s') := renameApart FG fi ϱ' s0 in
       (fi, stmtLet y (rename_exp ϱ e) s')
   | stmtIf e s1 s2 =>
     let '(fi, s1') := renameApart FG fi ϱ s1 in
     let '(fi, s2') := renameApart FG fi ϱ s2 in
      (fi, stmtIf (rename_op ϱ e) s1' s2')
   | stmtApp l Y => (fi, stmtApp l (List.map (rename_op ϱ) Y))
   | stmtReturn e => (fi, stmtReturn (rename_op ϱ e))
   | stmtFun F s2 =>
     let '(F', fi) := renameApartF FG (@renameApart _) ϱ F (nil,fi) in
     let '(fi, s2') := renameApart FG fi ϱ s2 in
     (fi, stmtFun (rev F')  s2')
   end.

Lemma get_rev_1 (X : Type) (L : 〔X〕) (n : nat) (x : X)
  : n < ❬L❭
    -> get L (❬L❭ - S n) x -> get (rev L) n x.
Proof.
  intros. general induction L; simpl in *.
  invt get.
  - assert (❬L❭ = n) by omega; subst.
    eapply get_app_ge; eauto using get with len.
    len_simpl. rewrite <- H4. econstructor.
  - eapply get_app. eapply IHL; eauto. omega.
    eqassumption. omega.
Qed.

Lemma domain_renameApartFRight' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
      (IH:forall (n : nat) (Zs : params * stmt),
          get F n Zs ->
          forall (ϱ : env nat) (fi : Fi),
            domain FG fi ∪ definedVars (snd (renameApart FG fi ϱ (snd Zs)))
                   ⊆ domain FG (fst (renameApart FG fi ϱ (snd Zs))))
  : domain FG fi ∪ definedVarsF definedVars (fst (renameApartFRight FG renameApart ϱ (nil, fi) F)) ⊆ domain FG (snd (renameApartFRight FG renameApart ϱ (nil, fi) F)).
Proof.
  general induction F; simpl; eauto.
  - cbn. cset_tac.
  - simpl.
    unfold renameApartFStep; repeat let_pair_case_eq; subst; simpl.
    rewrite <- IH; eauto using get.
    rewrite <- !fresh_list_domain_spec; eauto.
    rewrite <- IHF; eauto using get. unfold definedVarsF. simpl.
    norm_lunion. unfold defVarsZs at 1. simpl. clear. cset_tac.
Qed.

Lemma domain_renameApartF' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
      (IH:forall (n : nat) (Zs : params * stmt),
          get F n Zs ->
          forall (ϱ : env nat) (fi : Fi),
            domain FG fi ∪ definedVars (snd (renameApart FG fi ϱ (snd Zs)))
                   ⊆ domain FG (fst (renameApart FG fi ϱ (snd Zs))))
  : domain FG fi ∪ definedVarsF definedVars (fst (renameApartF FG renameApart ϱ F (nil, fi))) ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  rewrite <- renameApartFRight_corr. simpl.
  rewrite domain_renameApartFRight'; eauto.
  intros; inv_get; eauto.
Qed.

Lemma definedVarsF_rev F
  : definedVarsF definedVars (rev F) [=] definedVarsF definedVars F.
Proof.
  unfold definedVarsF. rewrite map_rev, <- list_union_rev. reflexivity.
Qed.

Lemma domain_renameApart {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ s
  : domain FG fi ∪ definedVars (snd (renameApart FG fi ϱ s))
           ⊆ domain FG (fst (renameApart FG fi ϱ s)).
Proof.
  revert ϱ fi.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; subst; simpl.
  - rewrite <- IHs. rewrite <- fresh_domain_spec; eauto.
    clear.
    cset_tac.
  - rewrite <- IHs2. rewrite <- IHs1. clear. cset_tac.
  - cset_tac.
  - cset_tac.
  - rewrite <- IHs.
    rewrite <- domain_renameApartF'; eauto.
    rewrite definedVarsF_rev. rewrite union_assoc. reflexivity.
Qed.

Lemma domain_renameApartFRight {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
  : domain FG fi ∪ definedVarsF definedVars (fst (renameApartFRight FG renameApart ϱ (nil, fi) F)) ⊆ domain FG (snd (renameApartFRight FG renameApart ϱ (nil, fi) F)).
Proof.
  eapply domain_renameApartFRight'; eauto using domain_renameApart.
Qed.

Lemma domain_renameApartF {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
  : domain FG fi ∪ definedVarsF definedVars (fst (renameApartF FG renameApart ϱ F (nil, fi)))
           ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  eapply domain_renameApartF'; eauto using domain_renameApart.
Qed.

Lemma domain_incl_renameApartFRight' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
      (IH:forall (n : nat) (Zs : params * stmt),
          get F n Zs ->
          forall (ϱ : env nat) (fi : Fi),
            domain FG fi ⊆ domain FG (fst (renameApart FG fi ϱ (snd Zs))))
  : domain FG fi ⊆ domain FG (snd (renameApartFRight FG renameApart ϱ (nil, fi) F)).
Proof.
  general induction F; simpl; eauto.
  unfold renameApartFStep; repeat let_pair_case_eq; subst; simpl.
  rewrite <- IH; eauto using get.
  rewrite <- !fresh_list_domain_spec; eauto.
  rewrite IHF; eauto using get. cset_tac.
Qed.

Lemma domain_incl_renameApartF' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
      (IH:forall (n : nat) (Zs : params * stmt),
          get F n Zs ->
          forall (ϱ : env nat) (fi : Fi),
            domain FG fi ⊆ domain FG (fst (renameApart FG fi ϱ (snd Zs))))
  : domain FG fi ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  rewrite <- renameApartFRight_corr.
  rewrite <- domain_incl_renameApartFRight'; eauto.
  intros; inv_get; eauto.
Qed.

Lemma domain_incl_renameApart {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ s
  : domain FG fi ⊆ domain FG (fst (renameApart FG fi ϱ s)).
Proof.
  revert ϱ fi.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; subst; simpl.
  - rewrite <- IHs. rewrite <- fresh_domain_spec; eauto.
    clear.
    cset_tac.
  - rewrite <- IHs2. rewrite <- IHs1. clear. cset_tac.
  - cset_tac.
  - cset_tac.
  - rewrite <- IHs.
    rewrite <- domain_incl_renameApartF'; eauto.
Qed.

Lemma domain_incl_renameApartF {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
  : domain FG fi
           ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  rewrite <- renameApartFRight_corr.
  rewrite <- domain_incl_renameApartFRight'; eauto.
  intros; inv_get; eauto using domain_incl_renameApart.
Qed.

Lemma domain_incl_renameApartFRight {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ F
  : domain FG fi
           ⊆ domain FG (snd (renameApartFRight FG renameApart ϱ (nil, fi) F)).
Proof.
  rewrite <- domain_incl_renameApartFRight'; eauto.
  intros; inv_get; eauto using domain_incl_renameApart.
Qed.

Lemma renameApartF_length'  {Fi} (FG:FreshGen Fi)
      ϱ F x
: length (fst (renameApartF FG renameApart ϱ F x)) = length (fst x) + length F.
Proof.
  general induction F; simpl; eauto.
  unfold renameApartFStep. simpl.
  repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
  rewrite IHF.
  simpl. omega.
Qed.

Lemma renameApartF_length  {Fi} (FG:FreshGen Fi)
      ϱ F fresh
  : length (fst (renameApartF FG renameApart ϱ F (nil, fresh))) = length F.
Proof.
  rewrite renameApartF_length'. eauto.
Qed.

Ltac renameApartF_len_simpl :=
  match goal with
  | [ H : context [ ❬fst (@renameApartF ?Fi ?FG ?f ?ϱ ?F _)❭ ] |- _ ] =>
    rewrite (@renameApartF_length Fi FG ϱ F) in H
  | [ |- context [ ❬fst (@renameApartF ?Fi ?FG ?f ?ϱ ?F _)❭ ] ] =>
    rewrite (@renameApartF_length Fi FG ϱ F)
  end.

Smpl Add renameApartF_len_simpl : len.

Lemma get_fst_renameApartF Fi (FG:FreshGen Fi) (FGS:FreshGenSpec FG) ϱ F n ans fi
:  get (fst (renameApartF FG renameApart ϱ F (nil, fi))) n ans
   -> exists ϱ' Zs FL, get F (length F - S n) Zs
                 /\ snd ans = snd (renameApart FG (snd FL) ϱ' (snd Zs))
                 /\ ϱ' = ϱ [fst Zs <-- fst ans]
                 /\ fst ans = fst FL
                 /\ FL = fresh_list FG (snd (renameApartFRight FG renameApart ϱ (nil, fi) (drop (S n) (rev F)))) (fst Zs)
                 /\ of_list (fst FL)
                           ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi)))
                 /\ definedVars (snd ans)
                               ⊆ domain FG (snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  intros.
  assert (n < ❬F❭). {
    eapply Get.get_range in H. len_simpl. eauto.
  }
  revert H H0.
  rewrite <- renameApartFRight_corr.
  remember (rev F).
  general induction l; simpl in * |- *; [ isabsurd |].
  - unfold renameApartFStep in *.
    revert H; repeat let_pair_case_eq; repeat simpl_pair_eqs. subst.
    intros. simpl in *.
    inv H; subst.
    + do 3 eexists; eauto using get. split.
      * eapply get_rev. rewrite <- Heql. econstructor.
      * inv_get. simpl. split. reflexivity.
        split. reflexivity. split. reflexivity.
        split. reflexivity.
        rewrite <- domain_renameApart; eauto.
        rewrite <- fresh_list_domain_spec; eauto.
        eauto with cset.
    + edestruct IHl as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]; try eapply H5.
      * eauto.
      * instantiate (1:=rev (tl (rev F))).
        rewrite <- Heql. simpl. rewrite rev_involutive; eauto.
      * len_simpl. rewrite <- Heql. simpl.
        assert (❬F❭ = ❬a::l❭). rewrite Heql. eauto with len. simpl in *. omega.
      * subst. symmetry in Heql. eapply rev_swap in Heql. subst.
        simpl in *. len_simpl. rewrite rev_app_distr in *.
        rewrite rev_rev in *. simpl in *. inv_get.
        assert (n0 < ❬l❭). omega. inv_get. rewrite plus_comm. simpl.
        do 3 eexists; split.
        -- eapply get_app. eapply get_rev_1. omega.
           orewrite (❬l❭ - S (❬l❭ - S n0) = n0). eauto.
        -- split; eauto. split; eauto. split; eauto.
           split; eauto. split.
           ++ rewrite H7.
             rewrite <- domain_renameApart; eauto.
             rewrite <- fresh_list_domain_spec; eauto.
             clear. cset_tac.
           ++ rewrite H8.
             rewrite <- domain_renameApart; eauto.
             rewrite <- fresh_list_domain_spec; eauto.
             clear. cset_tac.
Qed.

Smpl Add 150
     match goal with
     | [ H : get (fst (renameApartF ?FG renameApart ?ϱ ?F (nil, ?fi)))
                 (❬fst (renameApartF ?FG renameApart ?ϱ ?F (nil, ?fi))❭ - S ?n) ?a,
         FGS : FreshGenSpec ?FG |- _ ] =>
       let a1 := fresh a in let a2 := fresh a in
                           try (is_var a; destruct a as [a1 a2]);
                             eapply get_fst_renameApartF in H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]; eauto;
                               change (fst (a1,a2)) with a1 in *;
                               change (snd (a1,a2)) with a2 in *; subst
     end
     : inv_get.



Lemma freeVars_renamedApart' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi ϱ s
: lookup_set ϱ (freeVars s) ⊆ domain FG fi
  -> freeVars (snd (renameApart FG fi ϱ s)) [=] lookup_set ϱ (freeVars s).
Proof.
  revert fi ϱ.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
      repeat rewrite lookup_set_union; try rewrite freeVars_renameExp;
      try rewrite freeVars_renameOp; eauto; try reflexivity.
  - rewrite IHs; eauto.
    + rewrite lookup_set_update_union_minus_single; eauto.
      assert (fst (FG fi x) ∉ lookup_set ϱ (freeVars s \ singleton x)). {
        intro. eapply lookup_set_incl in H0; eauto.
        eapply H in H0. eapply fresh_spec; eauto.
        cset_tac.
      }
      cset_tac.
    + rewrite lookup_set_update_in_union; eauto.
      rewrite <- fresh_domain_spec; eauto.
      rewrite <- H. rewrite !lookup_set_union; eauto.
      clear. cset_tac.
  - rewrite IHs1; eauto. rewrite IHs2; eauto.
    + rewrite <- domain_incl_renameApart; eauto.
      rewrite <- H. repeat rewrite lookup_set_union; eauto.
      clear. cset_tac.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto.
      clear. cset_tac.
  - eapply freeVars_rename_op_list.
  - eapply union_eq_decomp; eauto.
    + rewrite lookup_set_list_union; eauto; try reflexivity.
      rewrite map_map.
      eapply list_union_indexwise_ext; only 1: eauto with len.
      intros. inv_get. len_simpl.
      orewrite (length F - S (length F - S n) = n) in H1. get_functional.
      rewrite H; eauto.
      * rewrite lookup_set_update_union_minus_list; eauto with len.
        -- rewrite <- disj_eq_minus; try reflexivity.
           eapply disj_1_incl.
           eapply fresh_list_disj; eauto.
           rewrite <- domain_incl_renameApartFRight; eauto.
           rewrite <- H0. eapply lookup_set_incl; eauto.
           eapply union_incl_left.
           eapply incl_list_union; eauto.
        -- rewrite fresh_list_len; eauto.
      * rewrite lookup_set_update_with_list_in_union_length; eauto with len.
        rewrite <- fresh_list_domain_spec; eauto.
        rewrite union_comm. eapply union_incl_split;[eauto with cset|].
        rewrite <- domain_incl_renameApartFRight; eauto.
        rewrite <- H0.
        eapply incl_union_right.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union; eauto.
        rewrite fresh_list_len; eauto.
    + rewrite IHs; eauto.
      rewrite <- domain_incl_renameApartF; eauto.
      rewrite <- H0. eauto with cset.
Qed.

Lemma renameApartFRight_disj' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi F ϱ
  (IH : forall (n : nat) (Zs : params * stmt),
      get F n Zs ->
      forall (ϱ : env nat) (fi : Fi),
        disj (domain FG fi) (definedVars (snd (renameApart FG fi ϱ (snd Zs)))))
  : disj (domain FG fi)
         (definedVarsF definedVars (fst (renameApartFRight FG renameApart ϱ (nil, fi) F))).
Proof.
  general induction F; simpl.
  - cbn. cset_tac.
  - unfold definedVarsF.
    unfold renameApartFStep.
    repeat let_pair_case_eq; simpl; subst; eauto.
    unfold defVarsZs at 2; simpl.
    norm_lunion.
    repeat eapply disj_union_right; eauto using get.
    + eapply disj_1_incl; eauto using fresh_list_disj.
      rewrite <- domain_incl_renameApartFRight; eauto.
    + eapply disj_1_incl. eapply IH; eauto using get.
      rewrite <- fresh_list_domain_spec; eauto.
      rewrite <- domain_incl_renameApartFRight; eauto.
Qed.

Lemma renameApartF_disj' {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi F ϱ
  (IH : forall (n : nat) (Zs : params * stmt),
      get F n Zs ->
      forall (ϱ : env nat) (fi : Fi),
        disj (domain FG fi) (definedVars (snd (renameApart FG fi ϱ (snd Zs)))))
  : disj (domain FG fi)
         (definedVarsF definedVars (fst (renameApartF FG renameApart ϱ F (nil, fi)))).
Proof.
  rewrite <- renameApartFRight_corr.
  eapply renameApartFRight_disj'; eauto.
  intros; inv_get; eauto.
Qed.

Lemma renameApart_disj {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) (fi:Fi) ϱ s
  : disj (domain FG fi) (definedVars (snd (renameApart FG fi ϱ s))).
Proof.
  revert ϱ fi.
  induction s using stmt_ind'; simpl; intros; repeat let_pair_case_eq;
    simpl; subst; eauto.
  - rewrite disj_add; split; eauto.
    + eapply fresh_spec; eauto.
    + eapply disj_1_incl; eauto.
      rewrite <- fresh_domain_spec; eauto. cset_tac.
  - rewrite disj_app; split; eauto.
    + eapply disj_1_incl; eauto.
      rewrite <- domain_incl_renameApart; eauto.
  - repeat (rewrite disj_app; split); eauto.
    + rewrite definedVarsF_rev.
      eapply renameApartF_disj'; eauto.
    + eapply disj_1_incl; eauto.
      rewrite <- domain_incl_renameApartF; eauto.
Qed.

Lemma poEq_ann_R_pe X `{OrderedType X} x y
  : poEq x y -> ann_R (pe (X:=X)) x y.
Proof.
  intros. general induction H0; econstructor; eauto;
            destruct a, b; inv H0; simpl in *; econstructor; eauto.
Qed.

Lemma renamedApartAnnF_snd_getAnn F G G'
  : list_union (snd ⊝ getAnn ⊝ fst (renamedApartAnnF renamedApartAnn G F (nil, G')))
               [=] list_union (definedVars ⊝ snd ⊝ F).
Proof.
  general induction F; simpl; eauto.
  norm_lunion.
  rewrite fst_renamedApartAnnF_swap. rewrite !List.map_app. simpl.
  rewrite list_union_app.
  rewrite IHF. rewrite snd_renamedApartAnn. simpl. cset_tac.
Qed.


Lemma list_union_definedVarsF_decomp F
  : list_union (defVarsZs definedVars ⊝ F)
               [=] list_union (of_list ⊝ fst ⊝ F) ∪ list_union (definedVars ⊝ snd ⊝ F).
Proof.
  general induction F; simpl.
  - cset_tac.
  - norm_lunion. rewrite IHF.
    unfold defVarsZs at 1. clear.
    cset_tac.
Qed.

Definition pairwise_ne' {X} (P:X->X->Prop) (L:list X) :=
  forall n m a b, n < m -> get L n a -> get L m b -> P a b.

Lemma pairwise_ne_sym_ne' (X : Type) (P : relation X) (L : 〔X〕)
      `{Symmetric _ P}
  : pairwise_ne' P L -> pairwise_ne P L.
Proof.
  unfold pairwise_ne, pairwise_ne'; intros.
  decide (n < m); eauto.
  exploit (H0 m n); eauto. omega.
Qed.

Lemma renameApartF_swap {Fi} (FG:FreshGen Fi) (fi:Fi) ϱ F L
  : renameApartF FG renameApart ϱ F (L, fi)
= (fst (renameApartF FG renameApart ϱ F (nil, fi)) ++ L,
   snd (renameApartF FG renameApart ϱ F (nil, fi))).
Proof.
  general induction F; simpl;
    repeat let_pair_case_eq; subst; eauto; simpl.
  setoid_rewrite IHF at 1.
  setoid_rewrite IHF at 3. simpl.
  rewrite <- !app_assoc.
  rewrite <- cons_app. f_equal.
  rewrite IHF. simpl.
  setoid_rewrite IHF at 2. simpl. reflexivity.
Qed.

Ltac renameApartF_swap_normal :=
  repeat match goal with
           [ |- context [ @renameApartF _ ?FG ?f ?ϱ ?F (?L, ?fi) ] ] =>
           match L with
           | nil => fail 1
           | _ => rewrite (renameApartF_swap FG fi ϱ F L)
           end
         end.

Lemma renameApartF_app {Fi} (FG:FreshGen Fi) (fi:Fi) ϱ F F' L
  : renameApartF FG renameApart ϱ (F ++ F') (L, fi)
    = (fst (renameApartF FG renameApart ϱ F' (nil, snd ((renameApartF FG renameApart ϱ F (nil, fi)))))
           ++ fst (renameApartF FG renameApart ϱ F (L, fi)),
       snd (renameApartF FG renameApart ϱ F' (nil, snd ((renameApartF FG renameApart ϱ F (nil, fi)))))).
Proof.
  general induction F; simpl; eauto.
  - rewrite renameApartF_swap. reflexivity.
  - repeat let_pair_case_eq; subst; simpl.
    renameApartF_swap_normal.
    rewrite IHF. simpl. f_equal.
    rewrite <- !app_assoc. f_equal.
Qed.

Lemma fst_renamedApartAnnF_rev G F
  : fst (renamedApartAnnF renamedApartAnn G (rev F) (nil, G))
    = rev (fst (renamedApartAnnF renamedApartAnn G F (nil, G))).
Proof.
  induction F; simpl; eauto.
  renamedApartAnnF_swap_normal.
  rewrite !fst_renamedApartAnnF_app; simpl.
  rewrite rev_app_distr; simpl.
  f_equal. rewrite IHF.
  erewrite fst_renamedApartAnnF_eq; eauto.
Qed.

Lemma renameApart'_renamedApart G {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi
      (s:stmt) ϱ
  : lookup_set ϱ (freeVars s) ⊆ G
    -> G ⊆ domain FG fi
  -> renamedApart (snd (renameApart FG fi ϱ s))
                 (renamedApartAnn (snd (renameApart FG fi ϱ s)) G).
Proof.
  revert G ϱ fi.
  induction s using stmt_ind'; simpl; intros; simpl;
    repeat let_pair_case_eq; simpl; repeat let_pair_case_eq; subst; simpl.
  - econstructor; eauto.
    + rewrite H0. eapply fresh_spec; eauto.
    + rewrite <- H. rewrite rename_exp_freeVars; eauto.
      eapply lookup_set_incl; eauto.
    + eapply renamedApart_ext; only 2: eapply (IHs {fst (FG fi x); G}); eauto with cset.
      * rewrite lookup_set_update_in_union; eauto.
        rewrite <- H. rewrite lookup_set_union; eauto.
        clear. cset_tac.
      * rewrite <- fresh_domain_spec; eauto. rewrite H0. reflexivity.
    + reflexivity.
    + rewrite renamedApartAnn_decomp; reflexivity.
  - rewrite !snd_renamedApartAnn.
    econstructor; try reflexivity;
      only 3: (eapply IHs1; eauto with cset);
      only 3: (eapply IHs2; eauto with cset).
    + rewrite <- H. rewrite rename_op_freeVars; eauto using lookup_set_union_incl.
    + eapply disj_1_incl.
      eapply renameApart_disj; eauto.
      rewrite <- domain_renameApart; eauto.
    + rewrite <- domain_incl_renameApart; eauto.
    + rewrite renamedApartAnn_decomp, snd_renamedApartAnn. reflexivity.
    + rewrite renamedApartAnn_decomp, snd_renamedApartAnn. reflexivity.
  - econstructor; [| reflexivity].
    rewrite <- H.
    rewrite lookup_set_list_union; eauto; [|eapply lookup_set_empty; eauto].
    eapply fold_left_subset_morphism; try reflexivity.
    repeat rewrite map_map.
    eapply map_ext_get; intros.
    rewrite <- rename_op_freeVars; eauto; reflexivity.
  - econstructor; eauto.
    rewrite rename_op_freeVars; eauto.
  - econstructor; only 1: eauto with len;
      only 5: (rewrite renamedApartAnn_decomp, snd_renamedApartAnn; reflexivity).
    + intros; inv_get. len_simpl.
      destruct x2 as [Z t].
      eapply H; eauto.
      * rewrite lookup_set_update_with_list_in_union_length; eauto with len.
        -- eapply incl_union_lr; eauto.
           rewrite <- H0.
           eapply lookup_set_incl; eauto.
           eapply incl_union_left.
           eapply incl_list_union; eauto using map_get_1.
        -- rewrite fresh_list_len; eauto.
      * rewrite <- fresh_list_domain_spec; eauto.
        rewrite <- domain_incl_renameApartFRight; eauto.
        rewrite H1. rewrite union_comm; eauto.
    + hnf; intros. hnf. inv_get.
      len_simpl. inv_get.
      revert H8 H9.
      rewrite drop_rev. len_simpl.
      orewrite (❬F❭ - S (❬F❭ - S n) = n). rewrite rev_rev.
      rewrite renameApartFRight_corr.
      hnf;
        rewrite ?fst_renamedApartAnn;
        rewrite ?snd_renamedApartAnn. simpl.
      split. rewrite union_comm; eauto.
      split. eapply fresh_list_nodup; eauto.
      split. symmetry. eapply disj_1_incl; try eapply fresh_list_disj; eauto.
      rewrite <- domain_incl_renameApartF; eauto.
      eapply disj_union_left.
      -- eapply disj_2_incl. symmetry.
         eapply renameApart_disj; eauto. eauto.
      -- eapply disj_2_incl. symmetry.
         eapply renameApart_disj; eauto.
         eauto.
    + eapply pairwise_ne_sym_ne'. eauto with typeclass_instances.
      hnf; intros. inv_get. len_simpl.
      revert H11 H10 H14 H13.
      rewrite !drop_rev. len_simpl.
      repeat orewrite (❬F❭ - S (❬F❭ - S n) = n).
      repeat orewrite (❬F❭ - S (❬F❭ - S m) = m).
      rewrite !rev_rev.
      rewrite !renameApartFRight_corr.
      simpl. inv_get.
      unfold defVars; simpl.
      rewrite !snd_renamedApartAnn. intros.
      eapply disj_union_right.
      eapply disj_1_incl. eapply fresh_list_disj; eauto.
      rewrite (take_take_app _ H2).
      rewrite renameApartF_app. simpl.
      erewrite <- get_eq_drop; eauto.
      rewrite take_one; try omega. simpl. repeat let_pair_case_eq; subst. simpl.
      renameApartF_swap_normal. simpl.
      rewrite <- domain_renameApartF; eauto.
      rewrite <- domain_renameApart; eauto.
      rewrite <- fresh_list_domain_spec; eauto.
      clear. cset_tac.
      eapply disj_1_incl. eapply renameApart_disj; eauto.
      rewrite (take_take_app _ H2).
      rewrite renameApartF_app. simpl.
      erewrite <- get_eq_drop; eauto.
      rewrite take_one; try omega. simpl. repeat let_pair_case_eq; subst. simpl.
      renameApartF_swap_normal. simpl.
      rewrite <- fresh_list_domain_spec; eauto.
      rewrite <- domain_renameApartF; eauto.
      rewrite <- domain_renameApart; eauto.
      rewrite <- fresh_list_domain_spec; eauto.
      clear. cset_tac.
    + eapply IHs; eauto with cset.
      rewrite <- domain_incl_renameApartF; eauto.
    + rewrite snd_renamedApartAnn, snd_renamedApartAnnF.
      eapply eq_union_lr; eauto.
      rewrite zip_rev; eauto with len.
      rewrite map_rev.
      rewrite <- !list_union_rev.
      rewrite list_union_defVars_decomp; eauto with len.
      rewrite renamedApartAnnF_snd_getAnn.
      rewrite !map_rev. rewrite <- list_union_rev.
      rewrite list_union_definedVarsF_decomp. reflexivity.
Qed.


Lemma renameApartF_agree {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi F f g
: (forall n Zs, get F n Zs ->
           forall f g fi, agree_on eq (freeVars (snd Zs)) f g
             -> renameApart FG fi f (snd Zs) = renameApart FG fi g (snd Zs))
  ->  agree_on eq
        (list_union
           (List.map
              (fun f0 : params * stmt => freeVars (snd f0) \ of_list (fst f0)) F)) f g
  -> renameApartF FG renameApart f F (nil, fi) = renameApartF FG renameApart g F (nil, fi).
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
  rewrite fresh_list_len; eauto.
Qed.

Lemma renameApart'_agree {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) fi s f g
: agree_on eq (freeVars s) f g
  -> renameApart FG fi f s = renameApart FG fi g s.
Proof.
  revert fi f g.
  induction s using stmt_ind'; simpl in * |- *; intros;
    repeat let_pair_case_eq; try simpl_pair_eqs; subst; simpl.
  - erewrite (IHs); eauto. erewrite rename_exp_agree; eauto using agree_on_incl with cset.
    eapply agree_on_update_same; eauto with cset.
  - erewrite (IHs1); eauto using agree_on_incl with cset.
    erewrite (IHs2); eauto using agree_on_incl with cset.
    erewrite rename_op_agree; eauto using agree_on_incl with cset.
  - do 2 f_equal. eapply map_ext_get_eq2; intros. eapply rename_op_agree.
    eapply agree_on_incl; eauto. eapply incl_list_union. eapply map_get_1; eauto. eauto.
  - erewrite rename_op_agree; eauto with cset.
  - erewrite (IHs); eauto with cset.
    erewrite renameApartF_agree; eauto.
    eapply agree_on_incl; eauto with cset.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)


Definition rename_apart {Fi} (FG:FreshGen Fi) s :=
  snd (renameApart FG (domain_add FG (empty_domain FG) (freeVars s)) id s).

Lemma rename_apart_renamedApart {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) (s:stmt)
: renamedApart (rename_apart FG s)
               (renamedApartAnn (rename_apart FG s) (freeVars s)).
  eapply renameApart'_renamedApart; eauto. eapply lookup_set_on_id; eauto.
  rewrite <- domain_add_spec; eauto.
Qed.

Lemma get_list_eq X (R:relation X) (L L':list X) (Len:❬L❭ = ❬L'❭)
  : (forall n x y, get L n x -> get L' n y -> R x y)
    -> list_eq R L L'.
Proof.
  general induction Len; eauto 20 using @list_eq, get.
Qed.


Lemma fst_renameApartF_length  {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG)
      fi  ϱ F
  : ((length (A:=nat) ⊝ fst ⊝ F
      = length (A:=nat) ⊝ fst ⊝ rev (fst (renameApartF FG renameApart ϱ F (nil, fi))))).
Proof.
  eapply list_eq_eq.
  eapply get_list_eq; intros.
  - eauto with len.
  - inv_get. len_simpl. inv_get.
    rewrite fresh_list_len; eauto.
Qed.

Lemma labelsDefined_paramsMatch  {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG) fi L s ϱ
: paramsMatch s L
  -> paramsMatch (snd (renameApart FG fi ϱ s)) L.
Proof.
  intros.
  general induction H; simpl;
    repeat (let_pair_case_eq); simpl; repeat simpl_pair_eqs; subst; simpl;
      eauto using paramsMatch with fresh len.
  - econstructor.
    + intros. inv_get; len_simpl. inv_get.
      exploit H0; eauto. eqassumption.
      erewrite <- fst_renameApartF_length; eauto.
    + exploit IHparamsMatch; swap 1 2.
      eqassumption.
      * erewrite <- fst_renameApartF_length; eauto.
      * eauto with fresh.
Qed.



Lemma app_expfree_rename_apart {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG) fi s ϱ
: app_expfree s
  -> app_expfree (snd (renameApart FG fi ϱ s)).
Proof.
  intros AEF.
  general induction AEF; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      eauto using app_expfree with fresh.
  - econstructor. intros; inv_get. exploit H; eauto.
    inv H1; simpl; eauto using isVar.
  - econstructor; intros; inv_get; eauto with fresh.
Qed.
