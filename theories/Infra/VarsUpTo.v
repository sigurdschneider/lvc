Require Import CSet Var.

Definition vars_up_to (n:var) :=
  Pos.peano_rect (fun _ => set var)
                 {}
                 (fun x X => {x; X})
                 n.

Lemma inj_lt x y
  : (x < y)%positive
    <-> Pos.to_nat x < Pos.to_nat y.
Proof.
  rewrite <- (Pos2Nat.id y) at 1.
  rewrite <- (Pos2Nat.id x) at 1.
  unfold Pos.lt.
  rewrite <- Nat2Pos.inj_compare; eauto.
  - rewrite Nat.compare_lt_iff. reflexivity.
  - exploit (Pos2Nat.is_pos x). simpl in *. omega.
  - exploit (Pos2Nat.is_pos y). simpl in *. omega.
Qed.

Lemma inj_le x y
  : (x <= y)%positive
    <-> Pos.to_nat x <= Pos.to_nat y.
Proof.
  rewrite <- (Pos2Nat.id y) at 1.
  rewrite <- (Pos2Nat.id x) at 1.
  unfold Pos.le.
  rewrite <- Nat2Pos.inj_compare; eauto.
  - rewrite Nat.compare_le_iff. reflexivity.
  - exploit (Pos2Nat.is_pos x). simpl in *. omega.
  - exploit (Pos2Nat.is_pos y). simpl in *. omega.
Qed.

Lemma vars_up_to_in (x i:var)
  : (x < i)%positive <-> x ∈ vars_up_to i.
Proof.
  unfold vars_up_to.
  revert x.
  induction i using Pos.peano_ind; intros.
  - rewrite Pos.peano_rect_base.
    split; intros.
    + exfalso.
      eapply inj_lt in H.
      rewrite Pos2Nat.inj_1 in H.
      exploit (Pos2Nat.is_pos x). simpl in *. omega.
    + cset_tac.
  - rewrite Pos.peano_rect_succ.
    cset_tac'.
    + eapply IHi.
      eapply inj_lt.
      eapply inj_lt in H.
      rewrite Pos2Nat.inj_succ in *.
      decide (Pos.to_nat i = Pos.to_nat x).
      * simpl in *. exfalso. eapply n. hnf.
        eapply Pos2Nat.inj in e. eauto.
      * omega.
    + eapply inj_lt.
      rewrite Pos2Nat.inj_succ. omega.
    + eapply IHi in H0.
      eapply inj_lt in H0.
      eapply inj_lt.
      rewrite Pos2Nat.inj_succ. omega.
Qed.

Lemma in_vars_up_to (n m:var)
: (n < m)%positive -> n ∈ vars_up_to m.
Proof.
  intros. eapply vars_up_to_in. eauto.
Qed.

Lemma in_vars_up_to' n m
: (n <= m)%positive -> n ∈ vars_up_to (m + 1)%positive.
Proof.
  intros. eapply vars_up_to_in.
  eapply inj_lt. eapply inj_le in H.
  rewrite Pos.add_1_r. rewrite Pos2Nat.inj_succ. omega.
Qed.

Lemma vars_up_to_incl n m
: (n <= m)%positive -> vars_up_to n ⊆ vars_up_to m.
Proof.
  intros H x IN. eapply vars_up_to_in; eapply vars_up_to_in in IN.
  eapply inj_lt; eapply inj_lt in IN. eapply inj_le in H. omega.
Qed.

Lemma vars_up_to_max n m
: vars_up_to (Pos.max n m) [=] vars_up_to n ∪ vars_up_to m.
Proof.
  hnf. intros.
  rewrite <- !vars_up_to_in.
  cset_tac'.
  - rewrite <- !vars_up_to_in in *.
    rewrite inj_lt in *.
    rewrite Pos2Nat.inj_max in *.
    decide ((Pos.to_nat n) <= (Pos.to_nat m)).
    + rewrite Max.max_r in H; eauto.
    + rewrite Max.max_l in H; omega.
  - rewrite <- !vars_up_to_in in *.
    rewrite inj_lt in *.
    rewrite Pos2Nat.inj_max in *.
    decide ((Pos.to_nat n) <= (Pos.to_nat m)).
    + rewrite Max.max_r; omega.
    + rewrite Max.max_l; omega.
  - rewrite <- !vars_up_to_in in *.
    rewrite inj_lt in *.
    rewrite Pos2Nat.inj_max in *.
    decide ((Pos.to_nat n) <= (Pos.to_nat m)).
    + rewrite Max.max_r; omega.
    + rewrite Max.max_l; omega.
Qed.
