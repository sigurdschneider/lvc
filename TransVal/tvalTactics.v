Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim Var.

Tactic Notation "setSubst" hyp(A) :=hnf in A; simpl in A; cset_tac; eapply A.
Tactic Notation "setSubst2" hyp(A) := hnf; intros; hnf in A;  eapply A; simpl; cset_tac; eauto.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)