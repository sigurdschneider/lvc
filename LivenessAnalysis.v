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

Definition liveness_transform (U:set var) (st:stmt)
           (st_incl:occurVars st ⊆ U)
           (ZL:list params) (DL:list ({ X : set var | X ⊆ U} * bool))
           (a:anni ({X : ⦃var⦄ | X ⊆ U} * bool))
  : {X : ⦃var⦄ | X ⊆ U}.
Proof.
  refine(
      match st as s, a return st = s -> {X : ⦃var⦄ | X ⊆ U} with
      | stmtLet x e s, anni1 d =>
        fun EQ => exist _ ((proj1_sig (fst d) \ singleton x) ∪ (if [x ∈ proj1_sig (fst d)] then Exp.freeVars e else ∅)) _
      | stmtIf e s t, anni2 ds dt =>
        fun EQ => if [exp2bool e = Some true] then
          fst ds
        else
          if [ exp2bool e = Some false ] then
            fst dt
          else
            exist _ (Exp.freeVars e ∪ (proj1_sig (fst ds)) ∪ (proj1_sig (fst dt))) _
      | stmtApp f Y, anni0 =>
        fun EQ => let lv := nth (counted f) DL (exist _ ∅ _, false) in
        let Z :=  nth (counted f) ZL nil in
        exist _ (proj1_sig (fst lv) \ of_list Z ∪
                           list_union (List.map Exp.freeVars
                                                (filter_by (fun x => B[x ∈ proj1_sig (fst lv)]) Z Y))) _
      | stmtReturn e, anni0 =>
        fun _ => exist _ (Exp.freeVars e) _
      | stmtExtern x f Y s, anni1 d =>
        fun _ => exist _ ((proj1_sig (fst d) \ singleton x) ∪ list_union (List.map Exp.freeVars Y)) _
      | stmtFun F t, anni1 dt =>
        fun _ => fst dt
      | _, _ => fun _ => exist _ ∅ _
      end eq_refl); (try now eapply incl_empty); subst st; simpl in *.
  - destruct d as [[d ?] b]; simpl.
    cases; [| cset_tac].
    rewrite s0.
    cset_tac; eauto. eapply st_incl. cset_tac.
  - destruct ds as [[ds ?] bs], dt as [[dt ?] bt]; simpl.
    cset_tac. specialize (st_incl a0). cset_tac.
  - destruct lv as [[lv ?] b]; simpl.
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


Definition liveness_analysis (s:stmt) :=
  @makeBackwardAnalysis (fun s => { U : set var | U ⊆ occurVars s}) _ _
                        (fun s ZL AL s => liveness_transform (occurVars s) s (CSetBasic.incl_refl _ _) ZL AL).
(fun Z an => (getAnn an, Z)).
