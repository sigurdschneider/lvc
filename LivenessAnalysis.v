Require Import CSet Le Var.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter Terminating.

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

Definition liveness_transform (DL:list (set var * params)) st a :=
  match st, a with
    | stmtLet x e s as st, anni1 d =>
      (d \ {{x}}) ∪ (if [x ∈ d] then Exp.freeVars e else ∅)
    | stmtIf e s t as st, anni2 ds dt =>
      if [exp2bool e = Some true] then
        ds
      else if [ exp2bool e = Some false ] then
        dt
      else
        Exp.freeVars e ∪ ds ∪ dt
    | stmtApp f Y as st, anni0 =>
      let (lv,Z) := nth (counted f) DL (∅,nil) in
      lv \ of_list Z ∪ list_union (List.map Exp.freeVars (filter_by (fun x => B[x ∈ lv]) Z Y))
    | stmtReturn e as st, anni0 => Exp.freeVars e
    | stmtExtern x f Y s as st, anni1 d =>
      (d \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | stmtFun F t as st, anni1 ds dt =>
      dt ∪ list_union (zip (fun Zs ds => (ds \ of_list (fst Zs))) F ds)
    | _, an => ∅
  end.


Definition liveness_analysis := makeBackwardAnalysis _ liveness_transform (fun Z an => (getAnn an, Z)).
