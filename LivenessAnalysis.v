Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Terminating.

Set Implicit Arguments.

Instance PartialOrder_Subset_Equal X `{OrderedType X} : PartialOrder (set X) :=
{
  poLe := Subset;
  poLe_dec := @Subset_computable _ _;
  poEq := Equal;
  poEq_dec := @Equal_computable _ _
}.
Proof.
  - intros. rewrite H0; eauto.
  - hnf; intros. split; eauto.
Defined.

Instance set_var_semilattice : BoundedSemiLattice (set var) := {
  bottom := ∅;
  join := union
}.
Proof.
  - intros; hnf; simpl. cset_tac.
  - hnf; intros. eapply union_idem.
  - hnf; intros. eapply union_comm.
  - hnf; intros. eapply union_assoc.
Defined.

Instance PartialOrder_Subset_Equal_Bounded X `{OrderedType X} U : PartialOrder ({ s : set X | s ⊆ U}) :=
{
  poLe x y := Subset (proj1_sig x) (proj1_sig y);
  poLe_dec x y := @Subset_computable _ _ (proj1_sig x) (proj1_sig y);
  poEq x y := Equal (proj1_sig x) (proj1_sig y);
  poEq_dec x y := @Equal_computable _ _ (proj1_sig x) (proj1_sig y)
}.
Proof.
  - econstructor.
    + hnf; intros. reflexivity.
    + hnf; intros. symmetry; eauto.
    + hnf; intros. etransitivity; eauto.
  - intros [a ?] [b ?]. simpl. intros. rewrite H0. reflexivity.
  - hnf; intros [a ?] [b ?] [c ?]; simpl; intros. etransitivity; eauto.
  - hnf; intros [a ?] [b ?]; simpl; intros. split; eauto.
Defined.

Instance set_var_semilattice_bounded U : BoundedSemiLattice ({ s : set var | s ⊆ U}) := {
  bottom := exist _ ∅ (@incl_empty var _ U);
  join x y := exist _ (union (proj1_sig x) (proj1_sig y)) _
}.
Proof.
  - destruct x,y; simpl. cset_tac.
  - intros [a ?]; simpl. cset_tac.
  - hnf; intros. eapply union_idem.
  - hnf; intros. eapply union_comm.
  - hnf; intros. eapply union_assoc.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H, H0. reflexivity.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H, H0. reflexivity.
Defined.

Lemma bunded_set_terminating X `{OrderedType X} U
  : Terminating {s : ⦃X⦄ | s ⊆ U} poLt.
Proof.
  hnf; intros [s Incl].
  remember (cardinal (U \ s)). assert (cardinal (U \ s) <= n) as Le by omega.
  clear Heqn. revert s Incl Le. induction n; intros.
  - econstructor. intros [y ?] [A B]; simpl in *.
    exfalso. eapply B. assert (cardinal (U \ s) = 0) by omega.
    rewrite <- cardinal_Empty in H0.
    eapply empty_is_empty_1 in H0. eapply diff_subset_equal' in H0.
    cset_tac.
  - intros. econstructor. intros [y ?] [A B]; simpl in *.
    eapply IHn.
    assert (~ y ⊆ s) by (intro; eapply B; split; eauto).
    edestruct not_incl_element; eauto; dcr.
    rewrite cardinal_difference'; eauto.
    rewrite cardinal_difference' in Le; eauto.
    erewrite (@cardinal_2 _ _ _ _ (y \ singleton x) y); eauto;
      [|cset_tac| rewrite Add_Equal; cset_tac; decide (x === a); eauto].
    assert (s ⊆ y \ singleton x) by cset_tac.
    eapply cardinal_morph in H1. omega.
Qed.

Definition liveness_transform
           (ZL:list params) (DL:list (set var * bool))
           (st:stmt)
           (a:anni (⦃var⦄ * bool))
  : ⦃var⦄ :=
  match st, a with
  | stmtLet x e s, anni1 d =>
    fst d \ singleton x ∪ (if [x ∈ fst d] then Exp.freeVars e else ∅)
  | stmtIf e s t, anni2 ds dt =>
    if [exp2bool e = Some true] then
      fst ds
    else
      if [ exp2bool e = Some false ] then
        fst dt
      else
        Exp.freeVars e ∪ (fst ds) ∪ (fst dt)
  | stmtApp f Y, anni0 =>
    let lv := nth (counted f) DL (∅, false) in
    let Z :=  nth (counted f) ZL nil in
    fst lv \ of_list Z ∪
        list_union (List.map Exp.freeVars
                             (filter_by (fun x => B[x ∈ fst lv]) Z Y))
  | stmtReturn e, anni0 =>
    Exp.freeVars e
  | stmtExtern x f Y s, anni1 d =>
    fst d \ singleton x ∪ list_union (List.map Exp.freeVars Y)
  | stmtFun F t, anni1 dt =>
    fst dt
  | _, _ => ∅
  end.

Require Import Subterm.

Definition mapOption A B (f:A -> B) (o:option A) : option B :=
  match o with
  | Some a => Some (f a)
  | None => None
  end.

Definition mapAnni {A B} (f:A -> B) (ai:anni A) : anni B :=
  match ai with
    | anni0 => anni0
    | anni1 a1 => anni1 (f a1)
    | anni2 a1 a2 => anni2 (f a1) (f a2)
    | anni2opt o1 o2 => anni2opt (mapOption f o1) (mapOption f o2)
  end.

Lemma list_sig_decomp A (P:A->Prop)
  : list { a : A | P a }
    -> { L : list A | forall n a, get L n a -> P a }.
Proof.
  intros.
  refine (exist _ (@proj1_sig A P ⊝ X) _).
  intros. inv_get. destruct x. eauto.
Defined.

Lemma not_get_nth_default A (L:list A) n d
  : (forall x, get L n x -> False)
    -> nth n L d = d.
Proof.
  intros. general induction n; destruct L; simpl; eauto using get.
  exfalso; eauto using get.
Qed.

Definition liveness_transform_dep (sT:stmt)
           (ZL:list params)
           (DL:list ({ X : set var | X ⊆ occurVars sT} * bool))
      (s:stmt) (ST:subTerm s sT)
      (a:anni ({X : ⦃var⦄ | X ⊆ occurVars sT} * bool))
  : {X : ⦃var⦄ | X ⊆ occurVars sT}.
Proof.
  eapply (exist _ (liveness_transform ZL
                                      ((fun p => (proj1_sig (fst p), snd p)) ⊝ DL) s
                                      (mapAnni (fun p => (proj1_sig (fst p), snd p)) a))).
  destruct s, a as [|[[a ?] b]|[[a ?] b] [[a' ?] b']|a]; simpl in *; try now eapply incl_empty.
  - cases; [| cset_tac].
    cset_tac; eauto. eapply subTerm_occurVars; eauto; simpl. cset_tac.
  - repeat cases; eauto. eapply subTerm_occurVars in ST; simpl in *.
    cset_tac. eapply ST; cset_tac.
  - eapply union_incl_split.
    + destruct (get_dec DL (counted l)) as [[[[D PD] b] GetDL]|].
      * erewrite get_nth; eauto using map_get_1; simpl in *.
        cset_tac.
      * rewrite not_get_nth_default;
          intros; inv_get; simpl in *; eauto using get. cset_tac.
    + rewrite <- (subTerm_occurVars ST); simpl.
      eapply list_union_incl; try eapply H0; eauto with cset.
      intros; inv_get. eapply filter_by_get in H; dcr.
      cases in H3; isabsurd.
      eapply incl_list_union; eauto using map_get_1.
  - eapply subTerm_occurVars in ST; simpl in *. eauto.
  - cset_tac; eauto. eapply subTerm_occurVars; eauto; simpl. cset_tac.
  - eauto.
Defined.

Require Import SetOperations.

Lemma liveness_transform_dep_monotone (sT s : stmt) (ST : subTerm s sT)
      (ZL : 〔params〕) (AL AL' : 〔{x : ⦃var⦄ | x ⊆ occurVars sT} * bool〕)
  : AL ⊑ AL' ->
    forall a b : anni ({x : ⦃var⦄ | x ⊆ occurVars sT} * bool),
      a ⊑ b
      -> liveness_transform_dep ZL AL ST a ⊑ liveness_transform_dep ZL AL' ST b.
Proof.
  intros.
  time (destruct s; eauto with cset; inv H0; simpl; try reflexivity;
            repeat match goal with
                   | [ x : { x : set var | x ⊆ occurVars sT } * bool |- _ ] =>
                     destruct x as [[? ?] ?]
                   end; simpl in * |- *; dcr).
  - repeat cases; cset_tac.
  - repeat cases; try (now congruence); eauto.
    cset_tac.
  - eapply incl_union_lr.
    + destruct (get_dec AL (counted l)) as [[[[D PD] b] GetDL]|].
      * erewrite get_nth; eauto using map_get_1; simpl in *.
        provide_invariants_P2. simpl in *; dcr.
        erewrite (@get_nth _ (_ ⊝ AL') ); eauto using map_get_1; simpl in *.
        cset_tac.
      * rewrite not_get_nth_default; simpl; intros; inv_get; eauto.
        cset_tac.
    + eapply list_union_incl; eauto with cset.
      intros; inv_get. eapply filter_by_get in H1. dcr.
      destruct (get_dec AL (counted l)) as [[[[D PD] b] GetDL]|].
      * cases in H5.
        erewrite get_nth in COND; eauto. simpl in *.
        provide_invariants_P2. simpl in *.
        eapply incl_list_union. eapply map_get_1.

  - rewrite H2; reflexivity.
  - eauto.
Qed.

Definition liveness_analysis :=
  makeBackwardAnalysis (fun s => { x : ⦃var⦄ | x ⊆ occurVars s}) _
                       liveness_transform_dep I.

Instance makeBackwardAnalysis
  : forall s, Analysis { a : ann ({} * bool) | annotation s a } :=
  {
    analysis_step := fun X : {a : ann (Dom s * bool) | annotation s a} =>
                      let (a, Ann) := X in
                      exist (fun a0 : ann (Dom s * bool) => annotation s a0)
                            (fst (backward () nil nil s a)) (backward_annotation (f s) nil nil Ann);
    initial_value :=
      exist (fun a : ann (Dom s * bool) => annotation s a)
            (setAnn bottom s)
            (setAnn_annotation bottom s)
  }.
Proof.
  - intros [d Ann]; simpl.
    pose proof (@ann_bottom s (Dom s * bool) _ _ _ Ann).
    eapply H0.
  - intros. eapply terminating_sig.
    eapply terminating_ann. eapply terminating_pair; eauto.
    eapply terminating_bool.
  - intros [a Ann] [b Bnn] LE; simpl in *.
    eapply (backward_monotone (f s) (fMon s)); eauto.
Qed.
 *)


(*

Program Definition liveness_transform (U:set var) (st:stmt)
           (st_incl:occurVars st ⊆ U)
           (ZL:list params) (DL:list ({ X : set var | X ⊆ U} * bool))
           (a:anni ({X : ⦃var⦄ | X ⊆ U} * bool))
  : {X : ⦃var⦄ | X ⊆ U} :=
  match st, a with
      | stmtLet x e s, anni1 d =>
        (proj1_sig (fst d) \ singleton x) ∪ (if [x ∈ proj1_sig (fst d)] then Exp.freeVars e else ∅)
      | stmtIf e s t, anni2 ds dt =>
        if [exp2bool e = Some true] then
          fst ds
        else
          if [ exp2bool e = Some false ] then
            fst dt
          else
            Exp.freeVars e ∪ (proj1_sig (fst ds)) ∪ (proj1_sig (fst dt))
      | stmtApp f Y, anni0 =>
        let lv := nth (counted f) DL (exist _ ∅ _, false) in
        let Z :=  nth (counted f) ZL nil in
        proj1_sig (fst lv) \ of_list Z ∪
                  list_union (List.map Exp.freeVars
                                       (filter_by (fun x => B[x ∈ proj1_sig (fst lv)]) Z Y))
      | stmtReturn e, anni0 =>
        Exp.freeVars e
      | stmtExtern x f Y s, anni1 d =>
        (proj1_sig (fst d) \ singleton x) ∪ list_union (List.map Exp.freeVars Y)
      | stmtFun F t, anni1 dt =>
        fst dt
      | _, _ => exist _ ∅ _
  end.
Next Obligation.
  simpl in *.
  cases; [| cset_tac].
  cset_tac; eauto. eapply st_incl. cset_tac.
Qed.
Next Obligation.
  simpl in *. cset_tac. specialize (st_incl a). cset_tac.
Qed.
Next Obligation.
  eapply incl_empty.
Qed.
Next Obligation.
  simpl in *.
  cset_tac. eapply st_incl.
    eapply list_union_incl; try eapply H0; eauto with cset.
    intros; inv_get. eapply filter_by_get in H. dcr.
    cases in H4; isabsurd.
    eapply incl_list_union; eauto using map_get_1.
  - eauto.
  - destruct d as [[d ?] b]; simpl.
    cset_tac. eapply st_incl. cset_tac.
    Grab Existential Variables. eapply incl_empty.
Defined.
 *)

Definition liveness_analysis (s:stmt) :=
  @makeBackwardAnalysis (fun s => { U : set var | U ⊆ occurVars s}) _ _
                        (fun s ZL AL s' => liveness_transform (occurVars s) s (CSetBasic.incl_refl _ _) ZL AL).
(fun Z an => (getAnn an, Z)).
