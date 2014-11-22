Require Import Util.

Lemma minus_n_0: forall n, n-0 = n.

Proof.
intros; general induction n; eauto.
Qed.

Lemma andtrue_subst:
forall A B,
A /\ True /\ B <-> A /\ B.

Proof.
 intros; split; intros; destruct H; try destruct H0; split; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)