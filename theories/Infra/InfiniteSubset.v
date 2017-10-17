Require Import Util CSet OrderedTypeComputable OrderedTypeLe Even.

Set Implicit Arguments.

Record inf_subset X `{OrderedType X}  :=
  {
    inf_subset_P :> X -> bool;
    inf_subset_least : {x : X | inf_subset_P x /\ forall z, inf_subset_P z -> _le x z };
    inf_subset_inf : forall x, {y : X | inf_subset_P y /\ _lt x y /\
                                   forall z, inf_subset_P z ->_lt z y -> _le z x};
    inf_subset_proper :> Proper (_eq ==> eq) inf_subset_P
  }.

Arguments inf_subset X {H}.
Hint Resolve inf_subset_inf.

Instance inf_subset_X X `{OrderedType X} (p : inf_subset X)
  :  Proper (_eq ==> eq) p.
Proof.
  eapply p.
Qed.

Hint Resolve inf_subset_X.

Lemma inf_subset_inf_ext X `{OrderedType X} (p:inf_subset X) (x y:X)
      (EQ:x === y)
  : proj1_sig (inf_subset_inf p x) === proj1_sig (inf_subset_inf p y).
Proof.
  repeat destr_sig; dcr.
  rewrite EQ in *.
  setoid_rewrite EQ in H6.
  clear x EQ.
  decide (_lt x0 x1).
  - exploit H3; eauto.
  - decide (_lt x1 x0); eauto.
    + exploit (H6 x1); eauto.
    + eapply lt_trans_eq in n; eauto.
Qed.

Definition even_inf_subset : inf_subset nat.
Proof.
  refine (@Build_inf_subset _ _ even _ _ _).
  - eexists 0. split; eauto.
    intros. hnf. simpl. omega.
  - intros. cbn.
    edestruct (next_even' x). dcr.
    eexists; repeat split; eauto.
    intros. exploit H2; eauto. hnf; simpl; omega.
Defined.

Definition odd_inf_subset : inf_subset nat.
Proof.
  refine (@Build_inf_subset _ _ odd _ _ _).
  - eexists 1. split; eauto.
    intros. simpl.
    destruct z; simpl in *; hnf; simpl; omega.
  - intros. cbn.
    destruct (next_odd' x). dcr.
    eexists; repeat split; eauto.
    intros. exploit H2; eauto. hnf; simpl; omega.
Defined.


Definition even_inf_subset_pos : inf_subset positive.
Proof.
  refine (@Build_inf_subset _ _ even_pos_fast _ _ _).
  - eexists xH. split; eauto.
    intros. simpl.
    eapply Pos.lt_eq_cases.
    eapply Pos.le_1_l.
  - intros. cbn. destruct (next_even_pos' x); eauto; dcr.
    exists x0. spos. repeat split; eauto.
    intros. exploit H2; eauto.
    eapply Pos2Nat.inj_le in H4.
    decide (Pos.to_nat z = Pos.to_nat x).
    * eapply Pos2Nat.inj in e. subst. reflexivity.
    * left. simpl. spos. omega.
Defined.

Definition odd_inf_subset_pos : inf_subset positive.
Proof.
  refine (@Build_inf_subset _ _ (fun x => negb (even_pos_fast x)) _ _ _).
  - eexists (xO xH). split; eauto.
    intros. simpl.
    eapply Pos.lt_eq_cases.
    destruct z; simpl in *.
    + exfalso; eauto.
    + eapply Pos.le_1_l.
    + exfalso; eauto.
  - intros. cbn. destruct (next_odd_pos' x); eauto; dcr.
    exists x0. spos. repeat split; eauto; spos; eauto.
    intros; hnf; simpl; spos. eapply H2 in H3; eauto.
    + rewrite <- Pos2Nat.inj_lt.
      eapply Pos.lt_eq_cases; spos; eauto.
Defined.
