Require Import CSet Util InfiniteSubset.

Set Implicit Arguments.

Lemma inf_subset_inf_ext X `{OrderedType X} (p:inf_subset X) (x y:X)
      (EQ:x === y)
  : proj1_sig (inf_subset_inf p x) === proj1_sig (inf_subset_inf p y).
Proof.
  repeat destr_sig; dcr.
  rewrite EQ in *.
  setoid_rewrite EQ in H6.
  clear x EQ.
  decide (_lt x0 x1).
  - exploit H3; eauto. destruct H4.
    + exfalso. assert (_lt x0 x0) by (etransitivity; eauto).
      eapply OrderedType.StrictOrder_Irreflexive in H7. eauto.
    + rewrite H4 in *.
      eapply OrderedType.StrictOrder_Irreflexive in H5. eauto.
  - decide (_lt x1 x0); eauto.
    + exploit H6. eapply H0. eauto. destruct H4.
      * exfalso. assert (_lt x1 x1) by (etransitivity; eauto).
        eapply OrderedType.StrictOrder_Irreflexive in H7. eauto.
      * exfalso. rewrite H4 in *.
        eapply OrderedType.StrictOrder_Irreflexive in H2. eauto.
    + eapply lt_trans_eq in n; eauto.
Qed.

Section SafeFirst.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable p : @inf_subset X H.

  Hypothesis Q : X -> Prop.
  Hypothesis Qpr : Proper (_eq ==> iff) Q.
  Hypothesis Qsub : forall x, Q x -> p x.

  Inductive safe : X -> Prop :=
  | Isafe n (P:p n) : (~ (Q n) -> safe (proj1_sig (inf_subset_inf p n))) -> safe n.

  Lemma safe_sub n
    : safe n -> p n.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Lemma safe_eq x y
    : safe x -> x === y -> safe y.
  Proof.
    unfold Proper, respectful; intros.
    general induction H0; eauto.
    econstructor; intros.
    - rewrite <- H2. eauto.
    - eapply H1; eauto. rewrite H2; eauto.
      eapply inf_subset_inf_ext; eauto.
  Qed.

  Global Instance safe_proper
    : Proper (_eq ==> iff) safe.
  Proof.
    unfold Proper, respectful; split; eauto using safe_eq.
  Qed.

(*  Lemma safe_antitone' (m n:X)
  : safe n
    -> _lt m n
    -> safe m.
  Proof.
    intros.
    general induction H0; eauto using safe.
    - econstructor; eauto. intros.
      eapply H1; eauto.
      destr_sig; dcr.
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
 *)

  Lemma exists_is_safe
  : (exists x, Q x) -> exists n, safe n.
  Proof.
    intros EX. destruct EX. eexists; econstructor; intros.
    eapply Qsub; eauto.
    exfalso; eauto.
  Qed.

  Lemma safe_upward n
  : safe n -> ~ Q n -> safe (proj1_sig (inf_subset_inf p n)).
  Proof.
    intros. invt safe. eapply H2. eauto.
  Defined.

  Hypothesis comp  : forall n, Computable (Q n).
  Fixpoint safe_first n (s:safe n) : X.
  refine (if [ Q n ] then n else safe_first (proj1_sig (inf_subset_inf p n)) _).
  destruct s; eauto.
  Defined.

  Hypothesis P : X -> Prop.
  Hypothesis I : X -> Prop.
  Hypothesis PQ : forall n, P n -> Q n.
  Hypothesis Step : forall n, I n -> ~ Q n -> I (proj1_sig (inf_subset_inf p n)).
  Hypothesis Final : forall n , I n -> Q n -> P n.

  Fixpoint safe_first_spec n s
    : I n -> P (@safe_first n s).
  Proof.
    unfold safe_first.
    destruct s.
    - simpl. destruct (decision_procedure (Q n)); eauto.
  Qed.

End SafeFirst.

Fixpoint safe_first_ext X `{OrderedType X} (p:@inf_subset X H) P Q n
      (PC:forall n, Computable (P n))
      (QC:forall n, Computable (Q n))
      (PS:safe p P n)
      (QS:safe p Q n)
      (EXT:(forall x, P x <-> Q x)) {struct QS}
: safe_first PC PS = safe_first QC QS.
Proof.
  destruct PS. destruct QS. simpl. repeat cases. reflexivity.
  - exfalso. eapply n0. rewrite <- EXT. eauto.
  - exfalso. eapply n0. rewrite EXT. eauto.
  - eapply safe_first_ext. eauto.
Qed.

Lemma safe_impl X `{OrderedType X} (p:@inf_subset X H) (P Q: X -> Prop) n
: safe p P n -> (forall x, P x -> Q x) -> safe p Q n.
Proof.
  intros. general induction H0; eauto 20 using @safe.
Qed.
