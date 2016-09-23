Parameter T : Prop.
Parameter t : T.

Hint Extern 1 (T) => apply t.
Ltac diverge a := diverge a.
Hint Extern 2 (T) => diverge idtac.

Lemma test : T.
Proof.
  auto. (* executes the first hint, succeeds, and never executes
           the second hint. *)
Qed.

Lemma test2 : T.
Proof.
  eauto. (* executes the first and second hint;
            the latter of which results in a "stack overflow",
            and eauto does not solve the goal. *)
Abort.