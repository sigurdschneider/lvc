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

Lemma test3 : T.
Proof.
  eauto. (* executes the first and second hint;
            the latter of which results in a "stack overflow",
            and eauto does not solve the goal. *)
Abort.


Parameter T : Prop.
Parameter t : T.

Hint Extern 1 (T) => apply t.
Hint Extern 2 (T) => fail.

Lemma test : T.
Proof.
  auto. (* executes the first hint, succeedes, and never executes
           the second hint. *)
Qed.

Lemma test2 : T.
Proof.
  eauto. (* executes the first hint, and then the second hint,
            and then succeedes with the second hint (inspect
            with Set Ltac Debug. *)
Qed.

Ltac diverge a := diverge a.
Hint Extern 3 (T) => diverge idtac.

Lemma test3 : T.
Proof.
  eauto. (* executes the first, second, and third hint
            and fails with a stack overflow. *)
Abort.
