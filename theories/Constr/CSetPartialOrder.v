Require Import Util CSet Infra.PartialOrder Terminating Infra.Lattice SigR.

Remove Hints trans_eq_bool.

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

Instance set_var_semilattice X `{OrderedType X} : JoinSemiLattice (set X) := {
  join := union
}.
Proof.
  - hnf; intros. eapply union_idem.
  - hnf; intros. eapply union_comm.
  - hnf; intros. eapply union_assoc.
  - hnf; intros. eapply incl_left.
Defined.

Instance PartialOrder_Subset_Equal_Bounded X `{OrderedType X} U : PartialOrder ({ s : set X | s ⊆ U}) :=
{
  poLe := sig_R Subset;
  poLe_dec x y := _;
  poEq := sig_R Equal;
  poEq_dec x y := _;
}.
Proof.
  - intros [a ?] [b ?]; simpl. intros EQ. rewrite EQ. reflexivity.
  - hnf; intros [a ?] [b ?]; simpl; intros. split; eauto.
Defined.

Instance set_var_semilattice_bound X `{OrderedType X} U : JoinSemiLattice ({ s : set X | s ⊆ U}) := {
  join x y := exist _ (union (proj1_sig x) (proj1_sig y)) _
}.
Proof.
  - destruct x,y; simpl. cset_tac.
  - hnf; intros [a ?]. eapply union_idem.
  - hnf; intros [a ?] [b ?]. eapply union_comm.
  - hnf; intros [a ?] [b ?] [c ?]. eapply union_assoc.
  - hnf; intros [a ?] [b ?]; simpl. eapply incl_left.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H0, H1. reflexivity.
  - simpl. unfold Proper, respectful; intros. destruct x,y,x0,y0; simpl in * |- *.
    rewrite H0, H1. reflexivity.
Defined.

Instance set_var_lower_bounded X `{OrderedType X} U : LowerBounded { s : set X | s ⊆ U} :=
  {
    bottom := exist _ ∅ _
  }.
Proof.
  - cset_tac.
  - simpl; intros []. cset_tac.
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
    edestruct not_incl_element; eauto; dcr.
    rewrite cardinal_difference'; eauto.
    rewrite cardinal_difference' in Le; eauto.
    erewrite (@cardinal_2 _ _ _ _ (y \ singleton x) y); eauto;
      [|cset_tac| rewrite Add_Equal; cset_tac; decide (x === a); eauto].
    assert (s ⊆ y \ singleton x) by cset_tac.
    eapply cardinal_morph in H0. omega.
Qed.
