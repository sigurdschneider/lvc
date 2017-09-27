Require Import Util NaturalRep.


Fixpoint even (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => even n
  end.

Lemma even_or_successor x
  : even x \/ even (1 + x).
Proof.
  induction x; eauto.
  destruct IHx; eauto.
Qed.

Definition odd := (fun x => negb (even x)).

Lemma even_or_odd (x:nat)
  : even x + odd x.
Proof.
  unfold odd. destruct (even x); eauto.
Qed.

Lemma even_not_even x
  : even x = negb (even (S x)).
Proof.
  general induction x; eauto.
  - simpl even at 2.
    destruct (even x); destruct (even (S x)); simpl in *; intuition.
Qed.

Definition next_even (n:nat) := if [even n] then n else S n.

Definition next_even' (x:nat) :
  { y : nat | even y /\ x < y /\
            forall z, even z -> z < y -> z <= x}.
Proof.
  eexists (next_even (S x)). unfold next_even.
  cases.
  - repeat split; eauto.
    intros. omega.
  - repeat split; eauto.
    + rewrite even_not_even in NOTCOND.
      destruct (even (S (S x))); simpl in *; eauto.
    + intros. decide (z = x); subst; eauto.
      decide (z = S x); subst; eauto.
      * exfalso; eauto.
      * omega.
Defined.

Definition next_odd (n:nat) := if [even n] then S n else n.

Definition next_odd' (x:nat) :
  { y : nat | odd y /\ x < y /\
            forall z, odd z -> z < y -> z <= x}.
Proof.
  eexists (next_odd (S x)). unfold next_odd.
  cases; unfold odd.
  - repeat split; eauto.
    rewrite <- even_not_even; eauto.
    intros.
    decide (z = x); subst; eauto.
    decide (z = S x); subst; eauto.
    + exfalso; eauto.
      destruct (even (S x)); simpl in *; eauto.
    + omega.
  - repeat split; eauto.
    + destruct (even (S x)); simpl in *; eauto.
    + intros.
      decide (z = x); subst; eauto.
      decide (z = S x); subst; eauto.
      * exfalso; destruct (even (S x)); simpl in *; eauto.
        omega.
      * omega.
Defined.

Lemma next_even_even n
  : even (next_even n).
Proof.
  unfold next_even; cases; eauto.
  edestruct (even_or_successor n); eauto.
Qed.

Lemma even_add x y
  : even x
    -> even y
    -> even (x + y).
Proof.
  revert y. pattern x.
  eapply size_induction with (f:=id); intros.
  destruct x0; simpl; eauto.
  destruct x0; simpl; eauto.
  eapply H; eauto. unfold id. omega.
Qed.

Lemma even_max x y
  : even x
    -> even y
    -> even (max x y).
Proof.
  intros.
  decide (x < y).
  - rewrite max_r; try omega; eauto.
  - rewrite max_l; try omega; eauto.
Qed.

Lemma even_mult2 x
  : even (2 * x).
Proof.
  pattern x.
  eapply size_induction with (f:=id); intros.
  destruct x0; simpl; eauto.
  destruct x0; simpl; eauto. rewrite plus_comm. simpl.
  rewrite <- plus_assoc. simpl.
  exploit (H x0).
  - unfold id. omega.
  - simpl in H0. setoid_rewrite plus_comm in H0 at 2. simpl in *. eauto.
Qed.


Definition even_pos_fast (p:positive) :=
  match p with
  | (p'~1)%positive => true
  | (p'~0)%positive => false
  | _ => true
  end.

Lemma even_pos_fast_succ p
  : even_pos_fast (Pos.succ p) = negb (even_pos_fast p).
Proof.
  unfold even_pos_fast.
  destruct p; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma even_pos_fast_correct p
  : even (asNat p) = even_pos_fast p.
Proof.
  induction p using Pos.peano_ind.
  - simpl. eauto.
  - rewrite even_pos_fast_succ.
    change Pos.succ with (@succ positive _ _ _).
    nr. rewrite <- IHp.
    rewrite even_not_even. simpl. reflexivity.
Qed.

Definition next_even_pos (n:positive) :=
  if [even_pos_fast n] then n else succ n.

Lemma next_even_pos_even n
  : even (asNat (next_even_pos n)).
Proof.
  unfold next_even_pos.
  rewrite <- even_pos_fast_correct.
  cases; eauto. nr.
  edestruct (even_or_successor (asNat n)); eauto.
Qed.

Definition next_even_pos'' (n:positive) :=
  if [even_pos_fast n] then (succ (succ n)) else succ n.

Definition next_even_pos' (x:positive) :
  { y : positive | even_pos_fast y /\ (x < y)%positive /\
                   forall z, even_pos_fast z -> (z < y)%positive -> (z <= x)%positive}.
Proof.
  eexists (next_even_pos'' x). unfold next_even_pos''.
  cases.
  - rewrite <- even_pos_fast_correct in *.
    repeat split; eauto.
    + nr. simpl; eauto.
    + simpl. nr. omega.
    + intros.
      rewrite <- even_pos_fast_correct in *.
      simpl in *. nr.
      eapply Pos2Nat.inj_le.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * decide (Pos.to_nat z = S (Pos.to_nat x)); subst; eauto.
        unfold asNat in *. simpl in *.
        rewrite e in *. simpl in *.
        rewrite even_not_even in COND.
        erewrite <- S_pred in COND.
        destruct (even (Pos.to_nat x)); eauto. inv COND. inv H.
        eapply Pos2Nat.is_pos.
        omega.
  - repeat split; eauto; intros; rewrite <- even_pos_fast_correct in *.
    + nr.
      rewrite even_not_even in NOTCOND.
      destruct (even (S (asNat x))); simpl in *; eauto.
    + simpl. nr. omega.
    + intros. nr.
      simpl in *. nr.
      eapply Pos2Nat.inj_le.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * omega.
Defined.

Definition next_odd_pos'' (n:positive) :=
  if [even_pos_fast n] then (succ n) else succ (succ n).

Definition next_odd_pos' (x:positive) :
  { y : positive | ~ even_pos_fast y /\ (x < y)%positive /\
                   forall z, ~ even_pos_fast z -> (z < y)%positive -> (z <= x)%positive}.
Proof.
  eexists (next_odd_pos'' x). unfold next_odd_pos''.
  cases.
  - repeat split; eauto; intros; rewrite <- even_pos_fast_correct in *.
    + nr.
      rewrite even_not_even. simpl.
      destruct (even (asNat x)); simpl in *; eauto.
    + simpl. nr. omega.
    + intros. nr.
      simpl in *. nr.
      eapply Pos2Nat.inj_le.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * omega.
  - rewrite <- even_pos_fast_correct in *.
    repeat split; eauto.
    + nr. simpl; eauto.
    + simpl. nr. omega.
    + intros.
      rewrite <- even_pos_fast_correct in *.
      simpl in *. nr.
      eapply Pos2Nat.inj_le.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * decide (Pos.to_nat z = S (Pos.to_nat x)); subst; eauto.
        unfold asNat in *. simpl in *.
        rewrite e in *. simpl in *.
        rewrite even_not_even in NOTCOND.
        erewrite <- S_pred in NOTCOND; eauto using Pos2Nat.is_pos.
        destruct (even (Pos.to_nat x)); eauto. exfalso; eauto. exfalso; eauto.
        omega.
Defined.
