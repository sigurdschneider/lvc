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
