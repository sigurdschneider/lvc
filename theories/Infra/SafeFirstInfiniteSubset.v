Require Import CSet Util InfiniteSubset.

Set Implicit Arguments.

Section SafeFirst.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable p : @inf_subset X H.

  Hypothesis Q : X -> Prop.
  Hypothesis Qpr : Proper (_eq ==> iff) Q.
  Hypothesis Qsub : forall x, Q x -> p x.

  Inductive safe : X -> Prop :=
  | Isafe n : (~ (Q n) -> safe (proj1_sig (inf_subset_inf p n))) -> safe n.

  Lemma safe_eq x y
    : safe x -> x === y -> safe y.
  Proof.
    unfold Proper, respectful; intros.
    general induction H0; eauto.
    econstructor; intros.
    - eapply H1; eauto. rewrite H2; eauto.
      eapply inf_subset_inf_ext; eauto.
  Qed.

  Global Instance safe_proper
    : Proper (_eq ==> iff) safe.
  Proof.
    unfold Proper, respectful; split; eauto using safe_eq.
  Qed.

  Lemma exists_is_safe
  : (exists x, Q x) -> exists n, safe n.
  Proof.
    intros EX. destruct EX. eexists x. econstructor; intros.
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
  intros. general induction H0; eauto.
  econstructor; intros. eapply H1; eauto.
Qed.

Lemma safe_impl' X `{OrderedType X} (p:@inf_subset X H) (P Q: X -> Prop) n
: safe p P n -> (forall x, _lt n x \/ _eq n x -> P x -> Q x) -> safe p Q n.
Proof.
  intros. general induction H0; eauto.
  econstructor; intros. eapply H1; eauto.
  intros x. destr_sig. simpl in *. dcr. intros.
  eapply H2; eauto. destruct H5.
  - left; etransitivity; eauto.
  - left; rewrite <- H5; eauto.
Qed.
