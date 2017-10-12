Require Import Util.


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

Lemma even_not_even' x
  : ~ even (S x) <-> even x.
Proof.
  rewrite even_not_even.
  simpl. destruct (even x); firstorder.
Qed.

Lemma even_not_even'' x
  : even (S x) <-> ~ even x.
Proof.
  rewrite even_not_even.
  simpl. destruct (even x); firstorder.
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


Smpl Create spos.
Ltac spos := repeat smpl spos.

Smpl Add
     match goal with
     | [ LT : context [  Pos.to_nat (Pos.succ _) ] |- _ ] =>
       rewrite Pos2Nat.inj_succ in LT
     | [ |- context [  Pos.to_nat (Pos.succ _) ] ] =>
       rewrite Pos2Nat.inj_succ
     end : spos.

Lemma even_pred_to_nat x
  : even (Init.Nat.pred (Pos.to_nat x))
    = even (S (Pos.to_nat x)).
Proof.
  case_eq (Pos.to_nat x); intros.
  + exfalso. exploit (Pos2Nat.is_pos x). omega.
  + reflexivity.
Qed.

Smpl Add
     match goal with
     | [ LT : context [ even (Init.Nat.pred (Pos.to_nat _)) ] |- _ ] =>
       rewrite even_pred_to_nat in LT
     | [ |- context [ even (Init.Nat.pred (Pos.to_nat _)) ] ] =>
       rewrite even_pred_to_nat
     | [ LT : ~ Is_true (even (S _)) |- _ ] =>
       setoid_rewrite even_not_even' in LT
     | [ |- context [ ~ Is_true (even (S _)) ] ] =>
       setoid_rewrite even_not_even'
     | [ LT : Is_true (even (S _)) |- _ ] =>
       setoid_rewrite even_not_even'' in LT
     | [ |- context [ Is_true (even (S _)) ] ] =>
       setoid_rewrite even_not_even''
     | [ LT : context [ Init.Nat.pred (S ?x) ] |- _ ] =>
       change (Init.Nat.pred (S x)) with x in LT
     | [ |- context [ Init.Nat.pred (S ?x) ] ] =>
       change (Init.Nat.pred (S x)) with x
     | [ LT : context [ even (S (S ?x)) ] |- _ ] =>
       change (even (S (S x))) with (even x) in LT
     | [ |- context [ even (S (S ?x)) ] ] =>
       change (even (S (S x))) with (even x)
     end : spos.

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
  : even (pred (Pos.to_nat p)) = even_pos_fast p.
Proof.
  induction p using Pos.peano_ind.
  - simpl. eauto.
  - spos.
    rewrite even_pos_fast_succ.
    rewrite <- IHp; clear IHp.
    rewrite <- even_not_even. reflexivity.
Qed.

Definition next_even_pos (n:positive) :=
  if [even_pos_fast n] then n else Pos.succ n.

Lemma next_even_pos_even n
  : even (pred (Pos.to_nat (next_even_pos n))).
Proof.
  unfold next_even_pos.
  rewrite <- even_pos_fast_correct.
  cases; eauto. spos.
  edestruct (even_or_successor (Pos.to_nat n)); eauto.
Qed.

Definition next_even_pos'' (n:positive) :=
  if [even_pos_fast n] then (Pos.succ (Pos.succ n)) else Pos.succ n.

Smpl Add
     match goal with
     | [ LT : context [ (_ < _)%positive ] |- _ ] =>
       setoid_rewrite Pos2Nat.inj_lt in LT
     | [ |- context [ (_ < _)%positive ] ] =>
       setoid_rewrite Pos2Nat.inj_lt
     | [ LT : context [ (_ <= _)%positive ] |- _ ] =>
       setoid_rewrite Pos2Nat.inj_le in LT
     | [ |- context [ (_ <= _)%positive ] ] =>
       setoid_rewrite Pos2Nat.inj_le
     end : spos.

Smpl Add
     match goal with
     | [ H : Is_true (negb _) |- _ ] => eapply negb_prop_elim in H
     | [ |- Is_true (negb _) ] => eapply negb_prop_intro
     | [ H : ~ Is_true (negb _) |- _ ] => eapply negb_prop_classical in H
     | [ H : ?P, H' : ~ ?P |- _ ] => exfalso; eapply (H' H)
     end : spos.

Definition next_even_pos' (x:positive) :
  { y : positive | even_pos_fast y /\ (x < y)%positive /\
                   forall z, even_pos_fast z -> (z < y)%positive -> (z <= x)%positive}.
Proof.
  eexists (next_even_pos'' x). unfold next_even_pos''.
  cases.
  - rewrite <- even_pos_fast_correct in *;
      intros; repeat split; spos; eauto.
    + intros.
      rewrite <- even_pos_fast_correct in *.
      spos.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * decide (Pos.to_nat z = S (Pos.to_nat x)); subst; eauto.
        rewrite e in *. spos. omega.
  - repeat split; eauto; intros; rewrite <- even_pos_fast_correct in *; spos; eauto.
    omega.
Defined.

Definition next_odd_pos'' (n:positive) :=
  if [even_pos_fast n] then (Pos.succ n) else Pos.succ (Pos.succ n).

Definition next_odd_pos' (x:positive) :
  { y : positive | ~ even_pos_fast y /\ (x < y)%positive /\
                   forall z, ~ even_pos_fast z -> (z < y)%positive -> (z <= x)%positive}.
Proof.
  eexists (next_odd_pos'' x). unfold next_odd_pos''.
  cases.
  - repeat split; eauto; intros; rewrite <- even_pos_fast_correct in *; spos; eauto; try omega.
  - rewrite <- even_pos_fast_correct in *;
    repeat split; eauto; spos; eauto.
    + intros.
      rewrite <- even_pos_fast_correct in *. spos.
      decide (Pos.to_nat z = Pos.to_nat x); subst; eauto.
      * omega.
      * decide (Pos.to_nat z = S (Pos.to_nat x)); subst; eauto.
        rewrite e in *. spos. omega.
Defined.
