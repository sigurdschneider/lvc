Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Coherence Fresh Util SetOperations Sim Var.

Tactic Notation "setSubst" hyp(A) :=hnf in A; simpl in A; cset_tac; eapply A.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)