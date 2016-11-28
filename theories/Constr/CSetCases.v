Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation CSetTac Util CSetComputable.

Section theorems.
  Variable X : Type.
  Context `{OrderedType X}.

  Lemma in_add_case s (x y:X)
    : y ∈ {{x}} ∪ s -> x===y \/ (x =/= y /\ y ∈ s).
  Proof.
    cset_tac.
  Qed.

  Lemma in_in_neq s (x y:X)
    : x ∈ s -> ~y ∈ s -> x =/= y.
  Proof.
    cset_tac.
  Qed.

  Lemma minus_inane s (x:X)
    : x ∉ s
    -> s [=] (s\{{x}}).
  Proof.
    cset_tac.
  Qed.

  Lemma incl_set_decomp (s t:set X)
    : s ⊆ t -> t [=] s ∪ (t \ s).
  Proof.
    cset_tac.
  Qed.

  Lemma incl_union_minus (s t:set X)
    : s ⊆ (t ∪ (s \ t)).
  Proof.
    cset_tac.
  Qed.

  Lemma union_minus s (x:X)
    : x ∉ s -> s [=] ({{x}} ∪ s) \ {{x}}.
  Proof.
    cset_tac.
  Qed.

  Lemma set_fact_1 s t (x:X)
    : x ∉ t
    -> {{x}} ∪ (s \ ({{x}} ∪ t)) [=] {{x}} ∪ s \ t.
  Proof.
    cset_tac.
  Qed.

  Lemma incl_not_in (x:X) s t
    : x ∉ s -> s\{{x}} ⊆ t -> s ⊆ t.
  Proof.
    cset_tac. specialize (H1 a). cset_tac.
  Qed.


  Lemma minus_incl_special (c c' d : set X)
    : c ⊆ c'
    -> c ∪ (c' \ (c \ d)) [=] c'.
  Proof.
    cset_tac.
    decide(a ∈ c); cset_tac.
  Qed.

  Lemma minus_incl_meet_special (c c' d : set X)
    : d ⊆ c
    -> c ⊆ c'
    -> c ∩ (c' \ (c \ d)) [=] d.
  Proof.
    cset_tac.
  Qed.

  Lemma minus_minus_id (s t: set X)
    : s ⊆ t
    -> s [=] t \ (t \ s).
  Proof.
    cset_tac.
  Qed.
End theorems.
