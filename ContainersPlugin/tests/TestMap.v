Time Require Import Maps.

(** Testing notations and set declarations *)
Section Test.
  Fixpoint fill (s : Map[nat,nat]) (n : nat) :=
    match n with
      | O => s
      | S n0 => fill s[n0 <- S n0] n0
    end.
(*   Time Eval vm_compute in {}. *)
  Time Eval vm_compute in (fill [] 7)[8].
  Time Eval vm_compute in (fill [] 7)[4].
  Time Eval vm_compute in elements (fill [] 7).

  Check Map[nat,nat].
  Check Map[bool*nat,nat].
  Check Map[Map[nat,nat],nat].
  Check Map[nat,Map[nat,Prop]].
End Test.

(** Testing sets specifications *)
Fixpoint fill_ (s : Map[nat,nat]) (n : nat) :=
  match n with
    | O => s
    | S n0 => fill_ s[n0 <- S n0] n0
  end.
Definition fill2 n := fill_ [] n.

Lemma fill__iff :
  forall n s k k', MapsTo k k' (fill_ s n) <->
    (k < n /\ k' = S k \/ MapsTo k k' s).
Proof.
  induction n; intros s k k'; split; simpl; intro H.
  right; assumption.
  destruct H; auto; apply False_rec; Omega.omega.
  simpl in H; rewrite IHn in H; destruct H.
  left; intuition.
  destruct (eq_dec k n). compute in H0; subst.
  left; split; auto.
  assert (e := find_1 H).
  rewrite (find_1 (add_1 s (S n) (refl_equal n))) in e; congruence.
  right; apply add_3 with n (S n); auto; symmetry; auto.

  rewrite IHn; destruct H.
  destruct H; inversion H; subst.
  right; apply add_1; reflexivity.
  left; intuition. right.
  admit.
Qed.
Print Assumptions MapAVLInstance.MapAVL_FMapSpecs. (* closed ! *)

Require Import MapPositiveInstance.
Require Import NArith.

Check Map[positive, bool].
Fixpoint pfill_ (s : Map[positive,nat]) (n : nat) :=
  match n with
    | O => s
    | S n0 => pfill_ s[P_of_succ_nat n0 <- n0] n0
  end.
Definition pfill2 n := pfill_ [] n.

Eval vm_compute in pfill2 12.
