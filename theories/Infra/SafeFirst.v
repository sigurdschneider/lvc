Require Import Util.

Set Implicit Arguments.

Section SafeFirst.

  Hypothesis Q : nat -> Prop.
  Inductive safe : nat -> Prop :=
  | safe_here n : Q n -> safe n
  | safe_after n : safe (S n) -> safe n.

  Lemma safe_antitone m n
  : safe n
    -> m < n
    -> safe m.
  Proof.
    intros. general induction H0; eauto using safe.
  Qed.

  Lemma exists_is_safe
  : (exists x, Q x) -> exists n, safe n.
  Proof.
    intros. destruct H; eexists; eauto using safe.
  Qed.

  Hypothesis comp  : forall n, Computable (Q n).

  Lemma safe_upward n
  : safe n -> ~ Q n -> safe (S n).
  Proof.
    intros; destruct H.
    - destruct (H0 H).
    - eapply H.
  Defined.

  Fixpoint safe_first n (s:safe n) : nat.
  refine (if [ Q n ] then n else safe_first (S n) _).
  destruct s; eauto. destruct (n0 H).
  Defined.

  Hypothesis P : nat -> Prop.
  Hypothesis I : nat -> Prop.
  Hypothesis PQ : forall n, P n -> Q n.
  Hypothesis Step : forall n, I n -> ~ Q n -> I (S n).
  Hypothesis Final : forall n , I n -> Q n -> P n.

  Fixpoint safe_first_spec n s
    : I n -> P (@safe_first n s).
  Proof.
    unfold safe_first.
    destruct s.
    - simpl. destruct (decision_procedure (Q n)); eauto.
    - cases; eauto.
  Qed.

End SafeFirst.

Fixpoint safe_first_ext P Q n
      (PC:forall n, Computable (P n))
      (QC:forall n, Computable (Q n))
      (PS:safe P n)
      (QS:safe Q n)
      (EXT:(forall x, P x <-> Q x)) {struct PS}
: safe_first PC PS = safe_first QC QS.
Proof.
  destruct PS; destruct QS; simpl; repeat cases; eauto;
  exfalso; firstorder.
Qed.

Lemma safe_impl (P Q: nat -> Prop) n
: safe P n -> (forall x, P x -> Q x) -> safe Q n.
Proof.
  intros. general induction H; eauto using safe.
Qed.
