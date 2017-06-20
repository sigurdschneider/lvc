Require Import CSet Util Map.
Require Import Env IL Alpha StableFresh Annotation RenamedApart SetOperations.
Require Import LabelsDefined PairwiseDisjoint AppExpFree.

Export RenamedApart.

Set Implicit Arguments.

(** We first define [rename_apart' ϱ G s], a function that chooses
    a variable fresh for G at every binder, records the choice in ϱ,
    and renames all variables according to ϱ *)

Record FreshInfo :=
  {
    FreshInfoType :> Type;
    domain : FreshInfoType -> set var
  }.

Inductive FreshGen (Fi : FreshInfo) :=
  {
    fresh :> Fi -> var -> var * Fi;
    fresh_list : Fi -> list var -> list var * Fi
  }.

Inductive FreshGenSpec Fi (FG:FreshGen Fi) : Prop :=
  {
    fresh_spec : forall i x, fst (fresh FG i x) ∉ domain _ i;
    fresh_list_spec : forall i Z, domain _ (snd (fresh_list FG i Z))
                                    [=] (domain _ i) ∪ of_list (fst (fresh_list FG i Z));
    fresh_list_len : forall i Z, ❬fst (fresh_list FG i Z)❭ = ❬Z❭;
  }.

Create HintDb fresh discriminated.

Definition renameApartFStep {Fi} (FG:FreshGen Fi)
           (renameApart': FreshGen Fi -> Fi -> env var -> stmt -> set var * Fi * stmt)
           ϱ :=
  (fun YLfreshG (Zs:params*stmt) =>
     let '(YL, fi, G) := YLfreshG in
     let (Y, fi) := fresh_list FG fi (fst Zs) in
     let ϱZ := ϱ [ fst Zs <-- Y ] in
     let '(G'', fresh, s1') := renameApart' FG fi ϱZ (snd Zs) in
     ((Y, s1')::YL,
      fresh,
      G'' ∪ of_list Y ∪ G)).

Lemma renameApartFStep_exp Fi (FG:FreshGen Fi) renameApart YG F ϱ
  : snd YG ⊆ snd (renameApartFStep FG renameApart ϱ YG F).
Proof.
  unfold renameApartFStep.
  repeat let_pair_case_eq; repeat simpl_pair_eqs; simpl; subst; eauto with cset.
Qed.

Definition renameApartF Fi (FG:FreshGen Fi)
           renameApart'
           ϱ
           := fold_left (renameApartFStep FG renameApart' ϱ).

Lemma renameApartF_exp  Fi (FG:FreshGen Fi)
      renameApart YG F ϱ
  : snd YG ⊆ snd (renameApartF FG renameApart ϱ F YG).
Proof.
  general induction F; simpl; eauto.
  rewrite <- IHF.
  eapply renameApartFStep_exp.
Qed.

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

Fixpoint renameApart' {Fi} (FG:FreshGen Fi) (fi:Fi) (ϱ:env var) (s:stmt) : set var * Fi * stmt:=
match s with
   | stmtLet x e s0 =>
     let (y, fresh) := fresh FG fi x in
     let ϱ' := ϱ[x <- y] in
     let '(G', fresh, s') := renameApart' FG fi ϱ' s0 in
       ({y; G'}, fresh, stmtLet y (rename_exp ϱ e) s')
   | stmtIf e s1 s2 =>
     let '(G', fi, s1') := renameApart' FG fi ϱ s1 in
     let '(G'', fi, s2') := renameApart' FG fi ϱ s2 in
      (G' ∪ G'', fi, stmtIf (rename_op ϱ e) s1' s2')
   | stmtApp l Y => (∅, fi, stmtApp l (List.map (rename_op ϱ) Y))
   | stmtReturn e => (∅, fi, stmtReturn (rename_op ϱ e))
   | stmtFun F s2 =>
     let '(F', fi, G') := renameApartF FG (@renameApart' _) ϱ F (nil,fi, ∅) in
     let '(G'', fi, s2') := renameApart' FG fi ϱ s2 in
     (G' ∪ G'', fi, stmtFun (rev F')  s2')
   end.

(*
Lemma renameApartF_disj {Fi} (FG:FreshGen Fi) (fi:Fi)
      (renameApart' : FreshGen Fi -> Fi -> env nat -> stmt -> ⦃nat⦄ * Fi * stmt) G ϱ F
  : (forall ϱ G G' n Zs, get F n Zs -> G ⊆ G' ->
                    disj G (domain _ (snd (fst (renameApart' FG fi ϱ (snd Zs))))))
  -> forall Ys G', G ⊆ G' -> disj G (snd (renameApartF FG renameApart' ϱ F (Ys, fi, G'))).
Proof.
  general induction F; simpl; eauto.
  - unfold renameApartFStep.
    let_pair_case_eq; simpl_pair_eqs; simpl in *.
    eapply IHF; eauto using get.
    rewrite disj_app; split; eauto.
    rewrite disj_app; split; eauto.
    + subst. eapply H; eauto using get.
      eapply disj_2_incl; eauto using get with cset. simpl.
      simpl. eauto
    + symmetry. eapply disj_2_incl.
      eapply fresh_list_stable_spec; eauto with cset.
      eauto with cset.
Qed.


Lemma renameApart'_disj fresh ϱ G s
  : disj G (fst (renameApart' fresh ϱ G s)).
Proof.
  revert ϱ G. sind s; intros; destruct s; simpl; repeat let_pair_case_eq; simpl; subst; eauto.
  - rewrite disj_add; split; eauto.
    eapply disj_subset_subset_flip_impl;
      [| reflexivity | eapply (IH s)]; eauto with cset.
  - rewrite disj_app; split; eauto.
    eapply disj_subset_subset_flip_impl;
      [| reflexivity | eapply (IH s2)]; eauto with cset.
  - repeat (rewrite disj_app; split); eauto.
    + cut (forall Ys G', disj G G' ->
                    disj G (snd (renameApartF fresh renameApart' G ϱ F (Ys, G'))));
      eauto using renameApartF_disj.
    + eapply disj_subset_subset_flip_impl; [| reflexivity | eapply (IH s)]; eauto with cset.
Qed.
*)

Definition renameApartAnnFStep {Fi} (FG:FreshGen Fi)
           (renameApartAnn: FreshGen Fi -> Fi -> stmt ->
                            set var * Fi * ann (set var * set var)) :=
  (fun (Zs:params*stmt) YLfreshG =>
     let '(YL, fi, G) := YLfreshG in
     let (Y, fi) := fresh_list FG fi (fst Zs) in
     let '(G'', fresh, s1') := renameApartAnn FG fi (snd Zs) in
     (s1'::YL,
      fresh,
      G ∪ of_list Y ∪ G)).


Definition renameApartAnnF Fi (FG:FreshGen Fi)
           renameApartAnn
           := fold_right (renameApartAnnFStep FG renameApartAnn).

Fixpoint renameApartAnn {Fi} (FG:FreshGen Fi) (fi:Fi)
         (s:stmt) : set var * Fi * ann (set var * set var):=
  match s with
  | stmtLet x e s0 =>
    let G := domain _ fi in
    let (y, fi) := fresh FG fi x in
    let '(G', fi, a) := renameApartAnn FG fi s0 in
    ({y; G'}, fi, ann1 (G, G') a)
  | stmtIf e s1 s2 =>
    let G := domain _ fi in
    let '(G', fi, s1') := renameApartAnn FG fi s1 in
    let '(G'', fi, s2') := renameApartAnn FG fi s2 in
    (G' ∪ G'', fi, ann2 (G, G' ∪ G'') s1' s2')
  | stmtApp l Y => (∅, fi, ann0 (domain _ fi, ∅))
  | stmtReturn e => (∅, fi, ann0 (domain _ fi, ∅))
  | stmtFun F s2 =>
    let G := domain _ fi in
    let '(anF', fi, G') := renameApartAnnF FG (@renameApartAnn _) (nil,fi, ∅) F in
    let '(G'', fi, s2') := renameApartAnn FG fi s2 in
    (G' ∪ G'', fi, annF (G, G' ∪ G'') (rev anF') s2')
  end.

Lemma fst_renameApartAnn {Fi} (FG:FreshGen Fi) (fi:Fi) s
 : fst (getAnn (snd (renameApartAnn FG fi s))) = domain _ fi.
Proof.
  sind s; destruct s; simpl; eauto;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; simpl; eauto.
Qed.

(*
Lemma snd_renamedApartAnnF_fst fresh G' G'' s ϱ L L' G'''
: (forall n Zs ϱ G' fresh,
     get s n Zs ->
     snd (getAnn (renameApartAnn (snd (renameApart' fresh ϱ (snd Zs))) G'))
     = fst (fst (renameApart' fresh ϱ (snd Zs))))
  -> snd (renameApartAnnF renameApartAnn G' (L', G''') L) = G''
  ->
   snd
     (renameApartAnnF renameApartAnn
        G' (L', G''') (fst (fst (renameApartFRight renameApart' ϱ (L, fresh, G'') s)))) =
   snd (renameApartFRight renameApart' ϱ (L, fresh, G'') s).
Proof.
  intros.
  revert_except s. general induction s; intros; simpl.
  - eauto.
  - unfold renameApartFStep.
    repeat (let_pair_case_eq). simpl in *.
    erewrite <- IHs in *; intros; [ | eauto using get | eauto using get].
    rewrite H1 in *. subst YL. rewrite H10.
    f_equal. f_equal. rewrite <- H10.
    eapply eq_union_lr.
    + subst. erewrite H; eauto using get.
Qed.
 *)

Lemma definedVars_renameApartF {Fi} (FG:FreshGen Fi) (fi:Fi) ϱ F G
: (forall ϱ fi n Zs, get F n Zs -> definedVars (snd (renameApart' FG fi ϱ (snd Zs)))
                                        [=] fst (fst (renameApart' FG fi ϱ (snd Zs))))
  -> list_union
      (List.map
         (fun f : params * stmt =>
            (definedVars (snd f) ∪ of_list (fst f))%set)
         (fst (fst (renameApartF FG renameApart' ϱ F (nil, fi, G))))) ∪ G [=]
      snd (renameApartF FG renameApart' ϱ F (nil, fi, G)).
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F).
  assert (forall n Zs, get l n Zs -> exists n', get F n' Zs).
  intros. subst. eapply get_rev in H. eauto. clear Heql.
  general induction l.
  - simpl. cset_tac.
  - simpl.
    unfold renameApartFStep.
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst. simpl.
    rewrite list_union_start_swap.
    rewrite empty_neutral_union.
    rewrite union_assoc.
    rewrite IHl; eauto using get.
    edestruct H; eauto using get.
    eapply eq_union_lr; eauto.
    eapply eq_union_lr; eauto.
Qed.

Lemma definedVars_renamedApart' {Fi} (FG:FreshGen Fi) (fi:Fi) ϱ s
: definedVars (snd (renameApart' FG fi ϱ s)) [=] fst (fst (renameApart' FG fi ϱ s)).
Proof.
  revert ϱ fi.
  induction s using stmt_ind'; intros; simpl in *;
    repeat let_pair_case_eq; simpl in * |- *; subst; eauto with cset.
  - rewrite IHs.
    eapply eq_union_lr; eauto.
    rewrite <- definedVars_renameApartF; eauto.
    rewrite map_rev. rewrite <- list_union_rev.
    cset_tac.
Qed.

(*
Lemma snd_renamedApartAnnF' G F
: (forall n Zs, get F n Zs -> forall G, snd (getAnn (renameApartAnn (snd Zs) G)) [=] definedVars (snd Zs))
  -> snd (renameApartAnnF renameApartAnn G (nil, {}) F)[=]
        list_union
        (List.map
           (fun f : params * stmt =>
              (definedVars (snd f) ∪ of_list (fst f))%set) F).
Proof.
  general induction F; simpl; eauto.
  - rewrite H; eauto using get. simpl.
    rewrite list_union_start_swap. rewrite IHF; intros; eauto using get.
    rewrite empty_neutral_union. reflexivity.
Qed.
 *)

Lemma get_fst_renamedApartAnnF {Fi} (FG:FreshGen Fi) (FGS:FreshGenSpec FG) (fi:Fi)
      F n ans G
:  get (fst (fst (renameApartAnnF FG renameApartAnn (nil, fi, G) F))) n ans
   -> exists Zs fi, get F n Zs
              /\ ans = snd (renameApartAnn FG fi (snd Zs)).
Proof.
  intros.
  general induction F; simpl in * |- *; [ isabsurd |].
  unfold renameApartAnnFStep in H.
  revert H; repeat let_pair_case_eq; repeat simpl_pair_eqs; intros; subst; simpl in *.
  inv H.
  - do 2 eexists; split; eauto using get.
  - edestruct IHF as [? [? [? ?]]]; eauto.
    do 2 eexists; split; eauto using get.
Qed.


(*
Inductive FreshInv (P:FreshGen -> Prop) FG : Prop :=
  {
    fresh_inv_local : P FG;
    fresh_inv : forall x, FreshInv P (snd (fresh FG x));
    fresh_list_inv : forall Z, FreshInv P (snd (fresh_list FG Z))
  }.

Lemma renameApartFRight_inv' P fresh (INV:FreshInv P fresh) G ϱ F
      (IH:forall fresh ϱ n Zs, get F n Zs
                          -> FreshInv P fresh
                          -> FreshInv P (snd (fst (renameApart' fresh ϱ (snd Zs)))))
  : FreshInv P fresh
    -> FreshInv P (snd (fst (renameApartFRight renameApart' ϱ (nil, fresh, G) F))).
Proof.
  general induction F; simpl; eauto.
  unfold renameApartFStep;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl; eauto.
  eapply IH; eauto using get.
  eapply fresh_list_inv. eapply IHF; eauto using get.
Qed.

Lemma renameApart_inv P fresh ϱ s
  : FreshInv P fresh
    -> FreshInv  P(snd (fst (renameApart' fresh ϱ s))).
Proof.
  revert fresh ϱ.
  induction s using stmt_ind'; intros; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      eauto with fresh.
  - eapply IHs. eapply fresh_inv; eauto.
  - eapply IHs.
    rewrite <- renameApartFRight_corr.
    eapply renameApartFRight_inv'; eauto.
    intros. inv_get. eapply H; eauto.
Qed.

Lemma renameApartFRight_inv P fresh G ϱ F
  : FreshInv P fresh
    -> FreshInv P (snd (fst (renameApartFRight renameApart' ϱ (nil, fresh, G) F))).
Proof.
  intros. eapply renameApartFRight_inv'; eauto using renameApart_inv.
Qed.

Lemma renameApartF_inv P fresh `{FreshGenSpec fresh} G ϱ F
  : FreshInv P fresh
    -> FreshInv P (snd (fst (renameApartF renameApart' ϱ F (nil, fresh, G)))).
Proof.
  intros. rewrite <- renameApartFRight_corr; eauto.
  eapply renameApartFRight_inv; eauto.
Qed.

Lemma FreshGenSpec_FreshInv fresh
  : FreshGenSpec fresh
    -> FreshInv FreshGenSpec fresh.
Proof.
  intros; econstructor. eauto.
  intros. destruct H. econstructor; eauto.
Qed.

Hint Resolve renamedApart_inv renameApartFRight_inv renameApartF_inv : fresh.
 *)

Lemma get_fst_renameApartF Fi (FG:FreshGen Fi) G ϱ F n ans fi
:  get (fst (fst (renameApartF FG renameApart' ϱ F (nil, fi, G)))) n ans
   -> exists ϱ' Zs fi' G', get F (length F - S n) Zs
                 /\ snd ans = snd (renameApart' FG fi' ϱ' (snd Zs))
                 /\ ϱ' = ϱ [fst Zs <-- fst ans]
                 /\ fst ans = fst (fresh_list FG (snd (fst (renameApartFRight FG renameApart' ϱ (nil, fi, G') (drop (S n) (rev F))))) (fst Zs)).
(*                 /\ length (fst Zs) = length (fst ans)
                 /\ disj G (of_list (fst ans))
                 /\ NoDupA _eq (fst ans).*)
                          (*
                 /\ G' = (G ∪ snd (renameApartFRight renameApart' ϱ (nil, fresh, {}) (drop (S n) (rev F)))) ∪ (of_list (fst ans))
                 /\ fst ans = fst (fresh_list (fst (snd (renameApartFRight renameApart' ϱ (nil, fresh, G') (drop (S n) (rev F)))) (fst Zs))
                 /\ ϱ' = ϱ [fst Zs <-- fst ans]. *)
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F).
  general induction l; simpl in * |- *; [ isabsurd |].
  - unfold renameApartFStep in *.
    revert H; repeat let_pair_case_eq; repeat simpl_pair_eqs. subst.
    intros. simpl in *.
    inv H; subst.
    + do 4 eexists; eauto using get. split.
      * eapply get_rev. rewrite <- Heql. econstructor.
      * inv_get. simpl. split. reflexivity.
        split. reflexivity. reflexivity.
    + edestruct IHl as [? [? [? [? [? ?]]]]]; eauto.
      instantiate (1:=rev (tl (rev F))).
      rewrite <- Heql. simpl. rewrite rev_involutive; eauto.
      rewrite <- Heql in *. simpl in *.
      assert (S (length (rev l)) = length (rev F)).
      rewrite <- Heql. simpl. rewrite rev_length; eauto.
      do 4 eexists; split; eauto using get.
      assert (length F = S (length (rev l))).
      rewrite rev_length.
      rewrite <- rev_length. rewrite <- Heql. eauto.
      exploit rev_swap. symmetry; eauto. simpl in *.
      rewrite H5 at 1. eapply get_app.
      rewrite H3. simpl. eauto.
Qed.



(*
Lemma snd_renameApartAnn_fst fresh s G ϱ G'
: snd (getAnn (renamedApartAnn (snd (renameApart' fresh ϱ G s)) G')) [=] fst (renameApart' fresh ϱ G s).
Proof.
  revert G ϱ G'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; simpl; eauto; subst.
  - rewrite (IH s); eauto.
  - rewrite (IH s1); eauto. rewrite (IH s2); eauto.
  - let_pair_case_eq; simpl_pair_eqs; subst. simpl.
    rewrite (IH s); eauto.
    eapply union_eq_decomp; eauto.
    rewrite snd_renamedApartAnnF'; eauto.
    + rewrite <- definedVars_renameApartF; eauto using definedVars_renamedApart'.
      rewrite map_rev.
      rewrite <- list_union_rev; eauto.
    + intros.
      inv_get.
      edestruct get_fst_renameApartF as [? [? [? ?]]]; dcr; eauto; subst.
      setoid_rewrite H3. rewrite definedVars_renamedApart'.
      eapply IH; eauto.
Qed.
*)

(*
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
            (definedVars (snd f) ∪ of_list (fst f))%set) s).
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

Lemma add_minus_eq X `{OrderedType X} G1 G2 x G'
  :  G1 [=] G2 \ G' -> x ∉ G' -> {x; G1} [=] {x; G2} \ G'.
Proof.
  intros. rewrite H0; clear H0. cset_tac.
Qed.

Hint Resolve add_minus_eq : cset.

Local Hint Extern 10 =>
match goal with
| [ |- context [ snd (getAnn (renamedApartAnn ?s ?G))] ] => setoid_rewrite snd_renamedApartAnn
| [ |- context [ snd (renamedApartAnnF renamedApartAnn ?G (nil, _) ?s) ] ]
  => setoid_rewrite snd_renamedApartAnnF
end : ann.

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
  - econstructor; eauto 20 with pe ann cset.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - econstructor; eauto with cset pe ann.
  - intros.
    repeat let_pair_case_eq; subst; simpl.
    econstructor; eauto 20 with cset pe ann.
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
        eapply incl_right.
Qed.

Lemma renameApartF_pw_disj fresh G' ϱ F
: pw_disj (List.map
             (fun f : params * stmt =>
                (definedVars (snd f) ∪ of_list (fst f))%set)
             (fst (renameApartF fresh renameApart' G' ϱ F (nil, {})))).
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
  symmetry. eapply disj_2_incl. eapply fresh_list_stable_spec; eauto.
  eauto. intros. eapply definedVars_renamedApart'.
Qed.

 *)

Lemma renameApartF_length'  {Fi} (FG:FreshGen Fi)
      ϱ F x
: length (fst (fst (renameApartF FG renameApart' ϱ F x))) = length (fst (fst x)) + length F.
Proof.
  general induction F; simpl; eauto.
  unfold renameApartFStep. simpl.
  repeat let_pair_case_eq; repeat simpl_pair_eqs; subst.
  rewrite IHF.
  simpl. omega.
Qed.

Lemma renameApartF_length  {Fi} (FG:FreshGen Fi)
      ϱ F G fresh
  : length (fst (fst (renameApartF FG renameApart' ϱ F (nil, fresh, G)))) = length F.
Proof.
  rewrite renameApartF_length'. eauto.
Qed.

Ltac renameApartF_len_simpl :=
  match goal with
  | [ H : context [ ❬fst (fst (@renameApartF ?Fi ?FG ?f ?ϱ ?F _))❭ ] |- _ ] =>
    rewrite (@renameApartF_length Fi FG ϱ F) in H
  | [ |- context [ ❬fst (fst (@renameApartF ?Fi ?FG ?f ?ϱ ?F _))❭ ] ] =>
    rewrite (@renameApartF_length Fi FG ϱ F)
  end.

Smpl Add renameApartF_len_simpl : len.

(*
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
  induction F; simpl; eauto.
  rewrite <- IHF. rewrite fst_renamedApartAnnF_app; simpl; eauto.
Qed.

Lemma union_defVars_renameApartF fresh G G' ϱ F
  : list_union
      (zip defVars (fst (renameApartF fresh renameApart' G' ϱ F (nil, {})))
           (fst
              (renamedApartAnnF renamedApartAnn G (nil, {})
                                (fst (renameApartF fresh renameApart' G' ϱ F (nil, {}))))))[=]
      snd (renameApartF fresh renameApart' G' ϱ F (nil, {})).
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F). clear Heql. general induction l; simpl; eauto.
  unfold renameApartFStep. let_pair_case_eq; simpl_pair_eqs.
  simpl.
  rewrite list_union_start_swap. subst.
  rewrite IHl; eauto.
  eapply union_eq_decomp; eauto. unfold defVars. simpl.
  rewrite snd_renamedApartAnn.
  rewrite <- definedVars_renamedApart'.
  rewrite empty_neutral_union, union_comm. reflexivity.
Qed.

Lemma freeVars_renamedApart' fresh ϱ G s
: lookup_set ϱ (freeVars s) ⊆ G
  -> freeVars (snd (renameApart' fresh ϱ G s)) [=] lookup_set ϱ (freeVars s).
Proof.
  revert G ϱ.
  sind s; destruct s; intros; simpl;
    repeat let_pair_case_eq; simpl in * |- *; subst; eauto;
    repeat rewrite lookup_set_union; try rewrite freeVars_renameExp;
      try rewrite freeVars_renameOp; eauto; try reflexivity.
  - rewrite IH; eauto.
    + rewrite lookup_set_update_union_minus_single; eauto.
      assert (fresh G x ∉ lookup_set ϱ (freeVars s \ singleton x)).
      intro. eapply lookup_set_incl in H0; eauto.
      eapply H in H0. eapply stable_fresh_spec; eauto.
      cset_tac. cset_tac.
    + rewrite lookup_set_update_in_union; eauto.
      rewrite <- H at 3. repeat rewrite lookup_set_union; eauto.
      cset_tac; intuition.
  - repeat rewrite IH; eauto.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto with cset.
    + rewrite <- H at 1. repeat rewrite lookup_set_union; eauto with cset.
  - eapply freeVars_rename_op_list.
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
      rewrite renameApartF_length in H0. simpl in H0.

      intros.
      edestruct get_fst_renameApartF as [? [? [? ?]]]; dcr; eauto.
      orewrite (length F - S (length F - S n) = n) in H4. get_functional; subst.

      setoid_rewrite H6.
      rewrite IH; eauto.
      * { assert (freeVars (snd z) [=]
                           (freeVars (snd z) \ of_list (fst z))
                           ∪ (of_list (fst z) ∩ freeVars (snd z))). {
            clear_all; cset_tac.
          }
          rewrite H3 at 1.
          repeat rewrite lookup_set_union; eauto.
          repeat rewrite minus_dist_union.
          pose proof (update_with_list_agree_inv _ _ _ H9 H8); eauto.
          assert ((freeVars (snd z) ∪ of_list (fst z)) \ of_list (fst z) [=]
                                                         freeVars (snd z) \ of_list (fst z)). {
            clear_all; cset_tac; intuition.
          }
          rewrite <- lookup_set_agree; eauto.
          intros. rewrite disj_minus_eq.
          - setoid_rewrite diff_subset_equal at 2.
            rewrite union_comm. rewrite empty_neutral_union; reflexivity.
            time(rewrite <- incl_right in H8).
            rewrite meet_incl; [|reflexivity].
            rewrite <- lookup_set_agree; eauto.
            eapply update_with_list_lookup_set_incl; eauto.
          - eapply disj_1_incl; eauto.
            rewrite <- H. eapply lookup_set_incl; eauto.
            eapply incl_union_left. eapply incl_list_union.
            eapply map_get_1; eauto. eauto.
          - rewrite <- H12. eauto.
        }
      * assert (freeVars (snd z) ⊆ (freeVars (snd z) \ of_list (fst z)) ∪ of_list (fst z)). {
          clear_all; cset_tac; intuition.
        }
        rewrite H3. rewrite lookup_set_union; eauto.
        pose proof (update_with_list_agree_inv _ _ _ H9 H8); eauto.
        assert (freeVars (snd z) \ of_list (fst z) ⊆ (freeVars (snd z) ∪ of_list (fst z)) \ of_list (fst z)). {
          cset_tac; intuition.
        }
        eapply union_subset_3; eauto.
        rewrite <- H5. rewrite <- H.
        rewrite <- lookup_set_agree; eauto.
        eapply lookup_set_incl; eauto.
        eapply incl_union_left.
        eapply incl_list_union.
        eapply map_get_1; eauto. eauto.
        eauto using agree_on_incl.
        rewrite <- H7.
        time (rewrite <- incl_right in H8).
        rewrite <- lookup_set_agree; eauto.
        eapply update_with_list_lookup_set_incl; eauto.
    + rewrite IH; eauto. eapply incl_union_left. rewrite <- H.
      eapply lookup_set_incl; eauto.
Qed.


Lemma union_defVars_renameApartF_PIR2 fresh G G' ϱ F
  :
    AllInRel.PIR2 Equal (zip defVars (fst (renameApartF fresh renameApart' G' ϱ F (nil, {})))
                             (fst
                                (renamedApartAnnF renamedApartAnn G (nil, {})
                                                  (fst (renameApartF fresh renameApart' G' ϱ F (nil, {}))))))
                  (List.map
                     (fun f : params * stmt =>
                        (definedVars (snd f) ∪ of_list (fst f))%set)
                     (fst (renameApartF fresh renameApart' G' ϱ F (nil, {})))).
Proof.
  rewrite <- renameApartFRight_corr.
  remember (rev F). clear Heql F. general induction l; simpl; eauto.
  unfold renameApartFStep. let_pair_case_eq; simpl_pair_eqs.
  simpl. unfold defVars.
  econstructor.
  rewrite snd_renamedApartAnn; eauto. cset_tac; intuition.
  rewrite IHl; eauto.
Qed.


Lemma renameApart'_renamedApart fresh (s:stmt) ϱ G G'
: lookup_set ϱ (freeVars s) ⊆ G
  -> G ⊆ G'
  -> renamedApart (snd (renameApart' fresh ϱ G' s)) (renamedApartAnn (snd (renameApart' fresh ϱ G' s)) G).
Proof.
  revert ϱ G G'.
  sind s; destruct s; simpl; intros; repeat let_pair_case_eq; simpl.
  - subst. econstructor; eauto using renameApartAnn_decomp.
    + rewrite H0; eauto.
    + simpl in H.
      rewrite rename_exp_freeVars; eauto. etransitivity; eauto.
      eapply lookup_set_incl; eauto.
    + eapply IH; eauto with cset.
      lset_tac; lud; eauto.
      eapply H; lset_tac.
    + reflexivity.
  - subst s1' s2'.
    simpl in H. simpl. rename G'' into Gs2. rename G'0 into Gs1.
    eapply renamedApartIf with (Ds := Gs1) (Dt := Gs2).
    + rewrite <- H. rewrite rename_op_freeVars; eauto using lookup_set_union_incl.
    + eapply disj_incl.
      eapply (@renameApart'_disj fresh ϱ (G' ∪ Gs1) s2).
      subst; eauto. subst; eauto.
    + repeat rewrite snd_renameApartAnn_fst. subst; reflexivity.
    + subst. eapply (IH s1); eauto.
      etransitivity; eauto. eapply lookup_set_incl; eauto with cset.
    + pose proof (@renameApart'_disj fresh ϱ G' s1). rewrite H2 in H1.
      pose proof (@renameApart'_disj fresh ϱ (G' ∪ Gs1) s2). rewrite H3 in H4.
      assert (disj (occurVars (snd (renameApart' fresh ϱ (G' ∪ Gs1) s2))) Gs1). {
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
      eapply @renamedApart_minus; [ eapply disj_2_incl; try reflexivity |eapply (IH s2); eauto  |eapply ann_R_pe_notOccur].
      * eapply disj_2_incl; eauto. reflexivity.
      * instantiate (1:=G). rewrite <- H; eauto using lookup_set_union_incl with cset.
      * eauto with cset.
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
    rewrite <- rename_op_freeVars; eauto; reflexivity.
    eapply lookup_set_empty; eauto.
  - econstructor; eauto. simpl in H. rewrite <- H.
    rewrite rename_op_freeVars; eauto.
  - simpl. subst s2'.
    let_pair_case_eq. simpl_pair_eqs.
    subst. econstructor; eauto.
    Focus 7.
    rewrite snd_renamedApartAnnF.
    eapply union_eq_decomp.
    rewrite map_rev. rewrite <- list_union_rev.
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
      edestruct get_fst_renamedApartAnnF; eauto; dcr; subst.
      get_functional; subst.
      assert (n < length F). eapply get_range in H1.
      rewrite rev_length in H1. rewrite renameApartF_length in H1. eauto.
      eapply get_rev in H1.
      rewrite renameApartF_length in H1.
      edestruct get_fst_renameApartF as [? [? []]]; eauto; dcr.
      setoid_rewrite H7. eapply IH; eauto with cset.
      assert (freeVars (snd x0) ⊆ (freeVars (snd x0) \ of_list (fst x0)) ∪ of_list (fst x0)). {
        clear_all; cset_tac; intuition.
      }
      rewrite H4. rewrite lookup_set_union; eauto.
      eapply union_subset_3; eauto.
      eapply incl_union_left.
      rewrite <- lookup_set_agree; eauto.
      rewrite <- H.
      eapply lookup_set_incl; eauto.
      eapply incl_union_left.
      eapply incl_list_union.
      eapply map_get_1; eauto. eauto.
      eapply update_with_list_agree_inv; eauto using agree_on_incl with cset.
      time (rewrite <- incl_right in H9).
      rewrite <- lookup_set_agree; eauto.
      eapply incl_union_right.
      eapply update_with_list_lookup_set_incl; eauto.
    + hnf; intros. unfold funConstr.
      edestruct get_fst_renamedApartAnnF; eauto; dcr.
      get_functional; subst.
      rewrite fst_renamedApartAnn.
      split. clear_all; cset_tac; intuition.
      eapply get_rev in H1.
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
    + eapply renameApartAnn_decomp.
Qed.

Lemma renameApartF_agree fresh G F f g
: (forall n Zs, get F n Zs ->
           forall f g G, agree_on eq (freeVars (snd Zs)) f g
             -> renameApart' fresh f G (snd Zs) = renameApart' fresh g G (snd Zs))
  ->  agree_on eq
        (list_union
           (List.map
              (fun f0 : params * stmt => freeVars (snd f0) \ of_list (fst f0)) F)) f g
  -> renameApartF fresh renameApart' G f F (nil, ∅) = renameApartF fresh renameApart' G g F (nil, ∅).
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
  eapply agree_on_incl; eauto. eapply incl_list_union. eapply map_get_1; eauto. reflexivity. eauto with len.
Qed.

Lemma renameApart'_agree fresh G s f g
: agree_on eq (freeVars s) f g
  -> renameApart' fresh f G s = renameApart' fresh g G s.
Proof.
  revert G f g.
  sind s; destruct s; simpl in * |- *; intros; repeat let_pair_case_eq; try simpl_pair_eqs; subst.
  - erewrite (IH s); eauto. erewrite rename_exp_agree; eauto using agree_on_incl with cset.
    eapply agree_on_update_same; eauto with cset.
  - erewrite (IH s1); eauto using agree_on_incl with cset.
    erewrite (IH s2); eauto using agree_on_incl with cset.
    erewrite rename_op_agree; eauto using agree_on_incl with cset.
  - do 2 f_equal. eapply map_ext_get_eq2; intros. eapply rename_op_agree.
    eapply agree_on_incl; eauto. eapply incl_list_union. eapply map_get_1; eauto. eauto.
  - erewrite rename_op_agree; eauto with cset.
  - erewrite (IH s); eauto with cset.
    erewrite renameApartF_agree; eauto.
    eapply agree_on_incl; eauto with cset.
Qed.

(** Based on [rename_apart'], we can define a function that renames apart bound variables apart
    and keeps free variables the same *)
Definition rename_apart fresh s := snd (renameApart' fresh id (freeVars s) s).

Lemma rename_apart_renamedApart fresh (s:stmt)
: renamedApart (rename_apart fresh s)
               (renamedApartAnn (snd (renameApart' fresh id (freeVars s) s)) (freeVars s)).
  eapply renameApart'_renamedApart; eauto. eapply lookup_set_on_id; eauto.
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
*)

Lemma get_list_eq X (R:relation X) (L L':list X) (Len:❬L❭ = ❬L'❭)
  : (forall n x y, get L n x -> get L' n y -> R x y)
    -> list_eq R L L'.
Proof.
  general induction Len; eauto 20 using @list_eq, get.
Qed.


Lemma fst_renameApartF_length  {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG)
      fi  ϱ F
  : ((length (A:=nat) ⊝ fst ⊝ F
      = length (A:=nat) ⊝ fst ⊝ rev (fst (fst (renameApartF FG renameApart' ϱ F (nil, fi, {})))))).
Proof.
  eapply list_eq_eq.
  eapply get_list_eq; intros.
  - eauto with len.
  - inv_get.
    eapply get_fst_renameApartF in H0 as [? [? [? [? [? [? [? ]]]]]]]; subst; eauto.
    simpl in *.
    rewrite H3. len_simpl.
    rewrite fresh_list_len; eauto.
    assert (n < ❬F❭) by eauto with len.
    orewrite (❬F❭ - S (❬F❭ - S n) = n) in H0.
    get_functional. eauto.
Qed.

Lemma labelsDefined_paramsMatch  {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG) fi L s ϱ
: paramsMatch s L
  -> paramsMatch (snd (renameApart' FG fi ϱ s)) L.
Proof.
  intros.
  general induction H; simpl;
    repeat (let_pair_case_eq); simpl; repeat simpl_pair_eqs; subst; simpl;
      eauto using paramsMatch with fresh len.
  - econstructor.
    + intros. inv_get.
      eapply get_fst_renameApartF in H2 as [? [? [? [? [? [? [? ]]]]]]];
        subst; eauto.
      simpl in *.
      rewrite H3. len_simpl.
      simpl in *. subst.
      rewrite H5.
      exploit H0; eauto. eqassumption.
      erewrite <- fst_renameApartF_length; eauto.
    + exploit IHparamsMatch; swap 1 2.
      eqassumption.
      * erewrite <- fst_renameApartF_length; eauto.
      * eauto with fresh.
Qed.



Lemma app_expfree_rename_apart {Fi} (FG:FreshGen Fi) (FGS: FreshGenSpec FG) fi s ϱ
: app_expfree s
  -> app_expfree (snd (renameApart' FG fi ϱ s)).
Proof.
  intros AEF.
  general induction AEF; simpl;
    repeat let_pair_case_eq; repeat simpl_pair_eqs; subst; simpl;
      eauto using app_expfree with fresh.
  - econstructor. intros; inv_get. exploit H; eauto.
    inv H1; simpl; eauto using isVar.
  - econstructor; intros; inv_get; eauto with fresh.
    eapply get_fst_renameApartF in H1 as [? [? [? [? [? [? [? ]]]]]]];
      subst; eauto.
    setoid_rewrite H2.
    + eapply H0; eauto.
Qed.
