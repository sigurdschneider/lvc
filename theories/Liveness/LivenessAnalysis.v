Require Import Util CSet SetOperations Infra.Lattice SigR CSetPartialOrder Filter Take.
Require Import IL Annotation Analysis AnalysisBackward Terminating Subterm.
Require Import Liveness.Liveness.

Remove Hints trans_eq_bool.

Set Implicit Arguments.

Definition liveness_transform (i:overapproximation)
           (ZL:list params) (DL:list (set var))
           (st:stmt)
           (a:anni (⦃var⦄))
  : ⦃var⦄ :=
  match st, a with
  | stmtLet x e s, anni1 d =>
    d \ singleton x ∪ (if [x ∈ d \/ isCall e] then Exp.freeVars e else ∅)
  | stmtIf e s t, anni2 ds dt =>
    if [op2bool e = Some true] then
      ds
    else
      if [ op2bool e = Some false ] then
        dt
      else
        Op.freeVars e ∪ (ds) ∪ (dt)
  | stmtApp f Y, anni0 =>
    let lv := nth (counted f) DL ∅ in
    let Z :=  nth (counted f) ZL nil in
    (if isImperative i then lv \ of_list Z else ∅) ∪
       list_union (List.map Op.freeVars
                            (filter_by (fun x => B[x ∈ lv]) Z Y))
  | stmtReturn e, anni0 =>
    Op.freeVars e
  | stmtFun F t, anni1 dt =>
    (if isFunctional i then list_union ((take ❬F❭ DL) \\ (take ❬F❭ ZL)) else ∅) ∪ dt
  | _, _ => ∅
  end.


Definition liveness_transform_dep (i:overapproximation) (sT:stmt)
           (ZL:list params)
           (DL:list ({ X : set var | X ⊆ occurVars sT}))
      (s:stmt) (ST:subTerm s sT)
      (a:anni ({X : ⦃var⦄ | X ⊆ occurVars sT}))
  : {X : ⦃var⦄ | X ⊆ occurVars sT}.
Proof.
  eapply (exist _ (liveness_transform i ZL
                                      (@proj1_sig _ _ ⊝ DL) s
                                      (mapAnni (@proj1_sig _ _) a))).
  destruct s, a as [|[a ?]|[a ?] [a' ?]|a]; simpl in *;
    try now eapply incl_empty.
  - cases; [| cset_tac].
    cset_tac'; eauto; eapply subTerm_occurVars; eauto; simpl; cset_tac.
  - repeat cases; eauto. eapply subTerm_occurVars in ST; simpl in *.
    cset_tac.
  - eapply union_incl_split.
    + destruct (get_dec DL (counted l)) as [[[D PD] GetDL]|].
      * erewrite get_nth; eauto using map_get_1; simpl in *.
        cases; cset_tac.
      * rewrite not_get_nth_default;
          intros; inv_get; simpl in *; eauto using get. cases; cset_tac.
    + rewrite <- (subTerm_occurVars ST); simpl.
      eapply list_union_incl; try eapply H0; eauto with cset.
      intros; inv_get.
      cases in H1.
      eapply incl_list_union; eauto using map_get_1.
  - eapply subTerm_occurVars in ST; simpl in *. eauto.
  - cases; eauto.
    eapply union_incl_split; eauto.
    eapply list_union_incl; eauto with cset.
    intros; inv_get. destruct x1; simpl in *. rewrite <- s1. eauto with cset.
Defined.

Lemma liveness_transform_dep_monotone (i:overapproximation) (sT s : stmt) (ST : subTerm s sT)
      (ZL : 〔params〕) (AL AL' : 〔{x : ⦃var⦄ | x ⊆ occurVars sT}〕)
  : AL ⊑ AL' ->
    forall a b : anni ({x : ⦃var⦄ | x ⊆ occurVars sT}),
      a ⊑ b
      -> liveness_transform_dep i ZL AL ST a ⊑ liveness_transform_dep i ZL AL' ST b.
Proof.
  intros.
  time (inv H0; destruct s; simpl in * |- *; try reflexivity;
            repeat match goal with
                   | [ x : { x : set var | x ⊆ occurVars sT } |- _ ] =>
                     destruct x as [? ?]
                   end; simpl in * |- *; dcr).
  - eapply incl_union_lr.
    + cases; eauto.
      destruct (get_dec AL (counted l)) as [[[D PD] GetDL]|].
      * erewrite get_nth; eauto using map_get_1; simpl in *.
        PIR2_inv. destruct x. simpl in *; dcr.
        erewrite (@get_nth _ (_ ⊝ AL') ); eauto using map_get_1; simpl in *.
        rewrite H1; eauto.
      * rewrite not_get_nth_default; simpl; intros; inv_get; eauto.
        cset_tac.
    + eapply list_union_incl; eauto with cset.
      intros; inv_get.
      destruct (get_dec AL (counted l)) as [[[D PD] GetDL]|].
      * cases in H3.
        erewrite get_nth in COND; eauto; simpl in *.
        PIR2_inv. destruct x1. simpl in *.
        exploit get_filter_by. Focus 4.
        eapply incl_list_union. eapply map_get_1.
        eapply H7. reflexivity. eauto. eauto.
        simpl. cases; eauto.
        erewrite get_nth in NOTCOND; [| eauto using map_get_1].
        eapply NOTCOND. simpl. eauto.
      * rewrite not_get_nth_default in H3. simpl in *.
        cases in H3; cset_tac.
        intros; inv_get; eauto.
  - rewrite H1 at 1. repeat cases; eauto; cset_tac.
  - cases; [| rewrite H1; reflexivity].
    eapply incl_union_lr; eauto.
    eapply list_union_incl; eauto with cset.
    intros; inv_get. PIR2_inv.
    eapply incl_list_union; eauto using get_take, zip_get.
    eapply sig_R_proj1_sig in H4; eauto with cset.
  - repeat cases; try (now congruence); eauto.
    cset_tac.
Qed.

Lemma liveness_transform_dep_ext (i:overapproximation) (sT s : stmt) (ST : subTerm s sT)
      (ZL : 〔params〕) (AL AL' : 〔{x : ⦃var⦄ | x ⊆ occurVars sT}〕)
  : AL ≣ AL' ->
    forall a b : anni ({x : ⦃var⦄ | x ⊆ occurVars sT}),
      a ≣ b
      -> liveness_transform_dep i ZL AL ST a ≣ liveness_transform_dep i ZL AL' ST b.
Proof.
  intros.
  time (destruct s; eauto with cset; simpl; inv H0; simpl; try reflexivity;
            repeat match goal with
                   | [ x : { x : set var | x ⊆ occurVars sT } |- _ ] =>
                     destruct x as [? ?]
                   end; simpl in * |- *; dcr).
  - rewrite H1 at 1.
    repeat cases; try reflexivity.
    exfalso. eapply NOTCOND. destruct COND; eauto.
    left. rewrite <- H1. eauto.
    exfalso. eapply NOTCOND. destruct COND; eauto.
    left. rewrite H1. eauto.
  - repeat cases; try (now congruence); eauto.
    rewrite H1, H2. reflexivity.
  - eapply eq_union_lr.
    + destruct (get_dec AL (counted l)) as [[[D PD] GetDL]|].
      * erewrite get_nth; eauto using map_get_1; simpl in *.
        PIR2_inv. destruct x. simpl in *; dcr.
        erewrite (@get_nth _ (_ ⊝ AL') ); eauto using map_get_1; simpl in *.
        cases; eauto.
        rewrite H1. reflexivity.
      * rewrite not_get_nth_default; simpl; intros; inv_get; eauto.
        destruct (get_dec AL' (counted l)) as [[[D PD] GetDL]|].
        exfalso. edestruct PIR2_nth_2; eauto; dcr. eauto.
        rewrite (@not_get_nth_default _ (_ ⊝ AL')); simpl; intros; inv_get; eauto.
    + erewrite filter_by_ext; [reflexivity| eauto with len |].
      * intros; inv_get.
        destruct (get_dec AL (counted l)) as [[[D PD] GetDL]|]; PIR2_inv.
        erewrite get_nth; [| eauto using map_get_1].
        destruct x. simpl in *.
        erewrite get_nth; [| eauto using map_get_1]. simpl.
        repeat cases; eauto; exfalso; rewrite H2 in *; eauto.
        repeat erewrite not_get_nth_default; intros; inv_get; eauto.
  - cases; eauto.
    eapply eq_union_lr; eauto.
    eapply list_union_eq; eauto.
    + eapply PIR2_length in H. eauto with len.
    + intros; inv_get. PIR2_inv.
      eapply sig_R_proj1_sig in H2; rewrite H2; eauto.
Qed.

Definition liveness_analysis i :=
  makeBackwardAnalysis (fun s => { x : ⦃var⦄ | x ⊆ occurVars s}) _
                       (liveness_transform_dep i)
                       (liveness_transform_dep_monotone i)
                       (fun s => (@bunded_set_terminating _ _ (occurVars s))).

Require Import FiniteFixpointIteration.

Definition livenessAnalysis i s :=
  let a := safeFixpoint (liveness_analysis i s) in
  mapAnn (@proj1_sig _ _) (proj1_sig (proj1_sig a)).
