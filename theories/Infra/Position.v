Require Import CSet LengthEq Option Map OrderedTypeEx Util List Get Computable DecSolve AllInRel.

Set Implicit Arguments.

Unset Printing Abstraction Types.

Fixpoint pos X `{OrderedType X} (l:list X) (x:X) (n:nat) : option nat :=
  match l with
    | nil => None
    | y::l => if [ x === y ] then Some n else pos l x (S n)
  end.

Lemma pos_add X `{OrderedType X} k' symb (f:X) k i
: pos symb f k = Some i -> pos symb f (k' + k) = Some (k' + i).
Proof.
  general induction symb; eauto.
  unfold pos in *; fold pos in *.
  cases. congruence.
  eapply IHsymb in H0. orewrite (S (k' + k) = k' + S k). eauto.
Qed.

Lemma pos_sub X `{OrderedType X} k' symb (f:X) k i
: pos symb f (k' + k) = Some (k' + i) -> pos symb f k = Some i.
Proof.
  general induction symb; eauto.
  unfold pos in *; fold pos in *.
  cases. f_equal. inv H0. omega.
  orewrite (S (k' + k) = k' + S k) in H0.
  eauto.
Qed.

Lemma pos_ge X `{OrderedType X} symb (l:X) i k
: pos symb l k = Some i
  -> k <= i.
Proof.
  general induction symb. unfold pos in H0; fold pos in H0.
  cases in H0. omega.
  exploit IHsymb; eauto. omega.
Qed.

Lemma pos_sub' X `{OrderedType X} k' symb (f:X) k i
: pos symb f k = Some i -> k' <= k -> pos symb f (k - k') = Some (i - k').
Proof.
  intros.
  eapply pos_sub.
  instantiate (1:=k').
  orewrite (k' + (k - k') = k).
  exploit pos_ge; eauto.
  orewrite (k' + (i - k') = i). eauto.
Qed.

Lemma get_first_pos X `{OrderedType X} n
      (Z:list X) z
: get Z n z
  -> (forall n' z', n' < n -> get Z n' z' -> z' =/= z)
  -> pos Z z 0 = Some n.
Proof.
  intros. general induction H0; simpl; cases; eauto.
  - exfalso. exploit (H1 0); eauto using get. omega.
  - exploit IHget; eauto.
    intros; eapply (H1 (S n')); eauto using get. omega.
    eapply pos_add with (k':=1) in H2. eauto.
Qed.

Lemma pos_get X  `{OrderedType X} (symb:list X) v x i
:  pos symb v i = ⎣x ⎦
   -> exists v', get symb (x-i) v' /\ v === v' /\ x >= i.
Proof.
  general induction symb; simpl in * |- *; eauto using get.
  cases in H0.
  - orewrite (x - x = 0). eexists; split; eauto using get.
  - exploit IHsymb; eauto; dcr.
    orewrite (x - i = S (x - S i)).
    eexists; split. econstructor; eauto. split; eauto; omega.
Qed.

Lemma pos_none X `{OrderedType X} symb (x:X) k k'
: pos symb x k = None
  -> pos symb x k' = None.
Proof.
  general induction symb; eauto; simpl in *.
  cases; try congruence.
  rewrite H0; eauto.
Qed.

Lemma pos_eq X `{OrderedType X} symb y k
: pos symb y k = Some k
  -> hd_error symb === Some y.
Proof.
  intros. destruct symb; simpl in *; try cases in H0; simpl; try congruence.
  - constructor. rewrite COND. reflexivity.
  - exfalso. exploit pos_ge; eauto. omega.
Qed.


Lemma pos_indep  X `{OrderedType X} symb symb' x y k k'
: pos symb x k = pos symb' y k
  -> pos symb x k' = pos symb' y  k'.
Proof.
  general induction symb.
  - general induction symb'; simpl in *; eauto.
    cases in H0; try congruence; eauto.
  - simpl in *. cases.
    + symmetry in H0. eapply pos_eq in H0. destruct symb'; simpl in *.
      inv H0.
      cases; eauto. inv H0; exfalso; eauto.
    + destruct symb'; simpl in *. eauto using pos_none.
      cases.
      * exfalso. exploit pos_ge; eauto. omega.
      * eauto.
Qed.

Lemma pos_inc  X `{OrderedType X} symb symb' x y k k'
: pos symb x k = pos symb' y k
  -> pos symb x (k' + k) = pos symb' y (k' + k).
Proof.
  intros. eapply pos_indep; eauto.
Qed.


Lemma pos_dec  X `{OrderedType X} symb symb' x y k k'
: pos symb x k = pos symb' y k
  -> pos symb x (k - k') = pos symb' y (k - k').
Proof.
  intros. eapply pos_indep; eauto.
Qed.


Lemma pos_app_in X `{OrderedType X} x k L L'
: x ∈ of_list L
  -> pos (L ++ L') x k = pos L x k.
Proof.
  intros.
  general induction L; simpl in * |- *; cset_tac'.
  - cases; try congruence; exfalso; eauto.
  - cases; try congruence; eauto.
Qed.


Lemma pos_app_not_in X `{OrderedType X} x k L L'
: x ∉ of_list L
  -> pos (L ++ L') x k = pos L' x (length L + k).
Proof.
  intros.
  general induction L; simpl in * |- *; cset_tac'.
  cases; try congruence; eauto.
  - rewrite IHL; eauto.
Qed.

Require Import Drop.

Lemma pos_get_first X  `{OrderedType X} (symb:list X) v x i
:  pos symb v i = ⎣x ⎦
   -> exists v', get symb (x-i) v' /\ v === v' /\ x >= i /\
     forall z' n, n < x-i -> get symb n z' -> z' =/= v.
Proof.
  general induction symb; simpl in * |- *; eauto using get.
  cases in H0.
  - orewrite (x - x = 0). eexists; repeat split; eauto using get.
    + intros. exfalso. omega.
  - exploit IHsymb; eauto; dcr.
    orewrite (x - i = S (x - S i)).
    eexists; split. econstructor; eauto. repeat split; eauto; try omega.
    + intros. inv H5; intro; eauto. eapply H6; eauto. omega.
Qed.

Instance trivial_pos_instance X `{OrderedType X}
  : Proper (eq ==> eq ==> eq ==> eq) (@pos X _).
Proof.
  unfold Proper, respectful. intros; subst. eauto.
Qed.
