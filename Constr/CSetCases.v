Require Export Setoid Coq.Classes.Morphisms.  
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation CSetTac Util CSetComputable.

Section theorems.
  Variable X : Type.
  Context `{OrderedType X}.

  Lemma in_add_case s (x y:X)
    : y ∈ {{x}} ∪ s -> x===y \/ (x =/= y /\ y ∈ s).
  Proof.
    decide (x===y); cset_tac; firstorder.
  Qed.

  Lemma in_in_neq s (x y:X)
    : x ∈ s -> ~y ∈ s -> x =/= y.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_inane s (x:X)
    : x ∉ s
    -> s ≅ (s\{{x}}).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.
 
  Lemma incl_set_decomp (s t:set X)
    : s ⊆ t -> t ≅ s ∪ (t \ s).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma incl_union_minus (s t:set X)
    : s ⊆ (t ∪ (s \ t)).
  Proof.
    cset_tac; firstorder.
  Qed.
  
  Lemma union_minus s (x:X)
    : x ∉ s -> s ≅ ({{x}} ∪ s) \ {{x}}.
  Proof.
    repeat (cset_tac; firstorder). 
  Qed.

  Lemma set_fact_1 s t (x:X)
    : x ∉ t
    -> {{x}} ∪ (s \ ({{x}} ∪ t)) ≅ {{x}} ∪ s \ t.
  Proof.
    intros. cset_tac; firstorder. cset_tac. 
    decide (a===x); firstorder. 
  Qed.

  Lemma incl_not_in (x:X) s t
    : x ∉ s -> s\{{x}} ⊆ t -> s ⊆ t.
  Proof.
    cset_tac. specialize (H1 a). cset_tac; firstorder.
  Qed.

  
  Lemma minus_incl_special (c c' d : set X)
    : c ⊆ c'
    -> c ∪ (c' \ (c \ d)) ≅ c'.
  Proof.
    cset_tac.
    decide(a ∈ c). firstorder.
    set (b:=c\d). assert (a ∉ b). subst b. cset_tac; firstorder.
    cset_tac; firstorder.
  Qed.

  Lemma minus_incl_meet_special (c c' d : set X)
    : d ⊆ c
    -> c ⊆ c'
    -> c ∩ (c' \ (c \ d)) ≅ d.
  Proof.
    cset_tac; firstorder.
    decide(a ∈ d); firstorder.
  Qed.

  Lemma minus_minus_id (s t: set X)
    : s ⊆ t
    -> s ≅ t \ (t \ s).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.
End theorems.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)



