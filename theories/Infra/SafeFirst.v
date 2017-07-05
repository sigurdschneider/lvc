Require Import CSet Util PidgeonHole OrderedTypeMax.

Set Implicit Arguments.

Section SafeFirst.
  Variable N : Type.
  Context `{NaturalRepresentationSucc N}.

  Hypothesis Q : N -> Prop.
  Hypothesis Qpr : Proper (_eq ==> iff) Q.

  Inductive safe : N -> Prop :=
  | Isafe n : (~ (Q n) -> safe (succ n)) -> safe n.

  Lemma safe_eq x y
    : safe x -> x === y -> safe y.
  Proof.
    unfold Proper, respectful; intros.
    general induction H2; eauto.
    econstructor; intros. eapply H3; eauto.
    rewrite H4. eauto. rewrite H4; eauto.
  Qed.

  Global Instance safe_proper
    : Proper (_eq ==> iff) safe.
  Proof.
    unfold Proper, respectful; split; eauto using safe_eq.
  Qed.

  Lemma safe_antitone' (m n:nat)
  : safe (ofNat n)
    -> m < n
    -> safe (ofNat m).
  Proof.
    intros.
    general induction H3; eauto using safe.
    - rewrite <- succ_ofNat in H2.
      econstructor; eauto.
    - rewrite <- succ_ofNat in H2.
      assert (safe (ofNat m0)) by (econstructor; eauto).
      eapply IHle in H4; eauto.
  Qed.

  Lemma safe_antitone m n
    : safe n
      -> _lt m n
      -> safe m.
  Proof.
    intros. rewrite <- ofNat_asNat.
    rewrite <- ofNat_asNat in H2.
    eapply order_respecting' in H3.
    eapply safe_antitone'; eauto.
  Qed.

  Lemma exists_is_safe
  : (exists x, Q x) -> exists n, safe n.
  Proof.
    intros. destruct H2; eexists; econstructor; intros.
    exfalso; eauto.
  Qed.

  Lemma safe_upward n
  : safe n -> ~ Q n -> safe (succ n).
  Proof.
    intros. inv H2. eauto.
  Defined.

  Hypothesis comp  : forall n, Computable (Q n).
  Fixpoint safe_first n (s:safe n) : N.
  refine (if [ Q n ] then n else safe_first (succ n) _).
  destruct s; eauto.
  Defined.

  Hypothesis P : N -> Prop.
  Hypothesis I : N -> Prop.
  Hypothesis PQ : forall n, P n -> Q n.
  Hypothesis Step : forall n, I n -> ~ Q n -> I (succ n).
  Hypothesis Final : forall n , I n -> Q n -> P n.

  Fixpoint safe_first_spec n s
    : I n -> P (@safe_first n s).
  Proof.
    unfold safe_first.
    destruct s.
    - simpl. destruct (decision_procedure (Q n)); eauto.
  Qed.

End SafeFirst.

Fixpoint safe_first_ext N `{NaturalRepresentationSucc N} P Q n
      (PC:forall n, Computable (P n))
      (QC:forall n, Computable (Q n))
      (PS:safe P n)
      (QS:safe Q n)
      (EXT:(forall x, P x <-> Q x)) {struct QS}
: safe_first PC PS = safe_first QC QS.
Proof.
  destruct PS. destruct QS. simpl. repeat cases. reflexivity.
  - exfalso. eapply n0. rewrite <- EXT. eauto.
  - exfalso. eapply n0. rewrite EXT. eauto.
  - eapply safe_first_ext. eauto.
Qed.

Lemma safe_impl N `{NaturalRepresentationSucc N} (P Q: N -> Prop) n
: safe P n -> (forall x, P x -> Q x) -> safe Q n.
Proof.
  intros. general induction H2; eauto 20 using @safe.
Qed.
