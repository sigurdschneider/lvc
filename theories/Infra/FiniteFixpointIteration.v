Require Import Util Coq.Classes.RelationClasses Infra.Lattice Terminating.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Class Monotone Dom `{PartialOrder Dom} Dom' `{PartialOrder Dom'} (f:Dom->Dom') :=
  monotone : forall a b, poLe a b -> poLe (f a) (f b).

Class Iteration (Dom: Type) := makeIteration {
  dom_po :> PartialOrder Dom;
  step : Dom -> Dom;
  initial_value : Dom;
  initial_value_small : initial_value ⊑ step initial_value;
  finite_height : Terminating Dom poLt;
  step_monotone : Monotone step
}.

Local Hint Extern 5 =>
match goal with
  [ H : poLe ?d ?d' |- poLe (step ?d) (step ?d')] =>
  eapply (step_monotone _ _ H)
end.

Section FixpointAlgorithm.
  Variable Dom : Type.
  Variable iteration : Iteration Dom.

  Fixpoint safeFirst (d:Dom) (mon:poLe d (step d)) (trm:terminates poLt d)
    : { d' : Dom | exists n : nat, d' = iter n d step /\ poEq (step d') d' }.
    decide (poLe (step d) d).
    - eexists d, 0; simpl.
      split; eauto.
      eapply poLe_antisymmetric; eauto.
    - destruct (safeFirst (step d)) as [d' H]; [ eauto | |].
      + destruct trm. eapply H.
        eapply poLe_poLt; eauto.
      + eexists d'. destruct H as [n' H]. eexists (S n'); simpl. eauto.
  Defined.

  Definition safeFixpoint
    : { d' : Dom | exists n : nat, d' = iter n initial_value step
                            /\ poEq (step d') d' }.
    eapply @safeFirst.
    - eapply initial_value_small.
    - eapply finite_height.
  Defined.

  Lemma safeFixpoint_chain n
    : iter n initial_value step
           ⊑ iter (S n) initial_value step.
  Proof.
    induction n.
    - simpl. eapply initial_value_small.
    - do 2 rewrite iter_comm.
      eapply step_monotone. eauto.
  Qed.

  Lemma safeFixpoint_induction (P:Dom -> Prop) n
    : P initial_value
      -> (forall a, poLe a (step a) -> P a -> P (step a))
      -> P (iter n initial_value step).
  Proof.
    intros. induction n; eauto.
    rewrite iter_comm. eapply H0.
    - rewrite <- iter_comm. eapply safeFixpoint_chain.
    - eapply IHn; eauto.
  Qed.

End FixpointAlgorithm.
