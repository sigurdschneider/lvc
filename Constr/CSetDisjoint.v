Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation CSetTac CSetComputable.

Set Implicit Arguments.

Definition disj {X} `{OrderedType X} (s t: set X)
  := s ∩ t [=] ∅.

Instance disj_sym {X} `{OrderedType X} : Symmetric disj.
Proof.
  unfold Symmetric, disj; intros.
  cset_tac; intuition; eauto.
Qed.

Instance disj_eq_eq_iff {X} `{OrderedType X}
: Proper (Equal ==> Equal ==> iff) disj.
Proof.
  unfold Proper, respectful, disj; intros.
  split; intros;
  cset_tac; intuition; firstorder.
Qed.

Instance disj_subset_subset_flip_impl {X} `{OrderedType X}
: Proper (Subset ==> Subset ==> flip impl) disj.
Proof.
  unfold Proper, respectful, disj; intros.
  split; intros;
  cset_tac; intuition; firstorder.
Qed.

Lemma disj_app {X} `{OrderedType X} (s t u: set X)
: disj s (t ++ u) <-> disj s t /\ disj s u.
Proof.
  split; unfold disj; intros; cset_tac; intuition; eauto.
Qed.

Lemma disj_add {X} `{OrderedType X} (x:X) (s t: set X)
: disj s {x; t} <-> x ∉ s /\ disj s t.
Proof.
  split; unfold disj; intros; cset_tac; intuition; eauto.
Qed.

Lemma disj_empty {X} `{OrderedType X} (s: set X)
: disj s {}.
Proof.
  unfold disj; intros; cset_tac; intuition; eauto.
Qed.

Hint Extern 20 (disj ?a ∅) => eapply disj_empty.

Hint Extern 20 (disj ∅ ?a) => eapply disj_sym; eapply disj_empty.

Lemma disj_singleton X `{OrderedType X} x D
:  x ∉ D
   -> disj D {x}.
Proof.
  intros. unfold disj. cset_tac; intuition.
Qed.

Lemma disj_1_incl X `{OrderedType X} D D' D''
:  disj D D'
   -> D'' ⊆ D
   -> disj D'' D'.
Proof.
  intros. rewrite H1; eauto.
Qed.

Lemma disj_2_incl X `{OrderedType X} D D' D''
:  disj D' D
   -> D'' ⊆ D
   -> disj D' D''.
Proof.
  intros. rewrite H1; eauto.
Qed.

Lemma in_disj_absurd X `{OrderedType X} (s t: set X) x
: x ∈ s -> x ∈ t -> disj s t -> False.
Proof.
  unfold disj; cset_tac; intuition; eauto.
Qed.

Hint Extern 10 =>
match goal with
  | [ H : disj ?s ?t, H' : ?x ∈ ?s, H'' : ?x ∈ ?t |- _ ] =>
    exfalso; eapply (in_disj_absurd H' H'' H)
end.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
