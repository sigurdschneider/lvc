Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation Util CSetTac.

Section theorems.
  Variable X : Type.
  Context `{OrderedType X}.

  Lemma single_spec_neq (x y:X)
    : x ∈ {{ y }} -> x === y.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma neq_not_in_single (x y:X)
    :  x =/= y -> ~x ∈ {{y}}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_empty (s:set X)
    : s \ ∅ ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_in_in s t (x:X)
    : x ∈ (s \ t) -> x ∈ s /\ ~x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_in_minus s t (x:X)
    : x ∈ s -> ~x ∈ t -> x ∈ (s \ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_comm (s t:set X)
    : s ∪ t ≅ t ∪ s .
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_inane_set (s t:set X)
    : s ∩ t ≅ ∅ -> (s \ t) ≅ s.
  Proof.
    intros.   cset_tac.


 cset_tac. specialize (H0 a). cset_tac; firstorder.
  Qed.

  Lemma minus_union_set (s t:set X)
    : s ∩ t ≅ ∅ -> ((s ∪ t) \ t) ≅ s.
  Proof.
    cset_tac. specialize (H0 a). cset_tac; firstorder.
  Qed.


  Lemma in_minus_neq s (x y:X)
    : x =/= y -> x ∈ s
    -> x ∈ (s\{{y}}).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma add_inane s (x:X)
    : x ∈ s
    -> s ≅ ({{x}} ∪ s).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma in_single_union s (y:X)
    : y ∈ {{y}} ∪ s.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.

  Lemma minus_union (s t u:set X)
    : (s \ t \ u) ≅ s \ (t ∪ u).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma incl_empty (s:set X)
    : ∅ ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_singleton (x:X) (s:set X)
    : x ∈ s -> singleton x ⊆ s.
  Proof.
    intros. hnf; intros. cset_tac; intuition.
  Qed.

  Lemma minus_incl (s t:set X)
    : (s\t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma empty_neutral_union (s:set X)
    : ∅ ∪ s ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_add s (x:X)
    :  s ⊆ ({{x}} ∪ s).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_refl (s:set X)
  : s ⊆ s.
  Proof.
    reflexivity.
  Qed.

  Lemma incl_right (s t:set X)
    :  s ⊆ (t ∪ s).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_add' (s:set X) x
    :  s ⊆ {x; s}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_add' (s:set X) x
    :  x ∈ {x; s}.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_minus (s t : set X)
    :  (s \ t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma union_assoc (s t u : set X)
    : s ∪ t ∪ u ≅ s ∪ (t ∪ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_minus_incl (s t:set X)
    : ((t ∪ s) \ t) ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_minus_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s \ t' ⊆ s' \ t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.


  Lemma union_idem (s:set X)
    : s ∪ s ≅ s.
  Proof.
    hnf; cset_tac; firstorder.
  Qed.

  Lemma minus_in s t (x:X)
    : x ∉ s -> x ∉ t -> x ∉ (s ∪ t).
  Proof.
    repeat (cset_tac; firstorder).
  Qed.

  Lemma union_cases s t (x:X)
    : x ∈ (s ∪ t) -> x ∈ s \/ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_comp  (s t : set X) x :
    ~x ∈ s /\ ~x ∈ t -> ~x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma not_in_union_decomp s t (x:X)
    : x ∉ (s ∪ t) -> x ∉ s /\ x ∉ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_left s t (x:X)
    : x ∈ s -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_right s t (x:X)
    : x ∈ t -> x ∈ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_fact_2 s t (x:X)
    : (s \ ({{x}} ∪ t)) \ {{x}} ≅ s \ ({{x}} ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_union_absorption (s t:set X)
    : s ⊆ t -> s ∪ t ≅ t.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_union_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s ∪ t ⊆ s' ∪ t'.
  Proof.
    intros; hnf in *; hnf; cset_tac; firstorder.
  Qed.

  Lemma incl_left (s t:set X)
    : s ⊆ (s ∪ t).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma in_meet (s t:set X) (x:X)
    : x ∈ s -> x ∈ t -> x ∈ s ∩ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in (s t:set X) (x:X)
    : x ∈ s ∩ t -> x ∈ s /\ x ∈ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_incl (s t u:set X)
    : s ⊆ u -> s ∩ t ⊆ u.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_comm (s t:set X)
    : s ∩ t ≅ t ∩ s.
  Proof.
    cset_tac. firstorder.
  Qed.

  Lemma incl_meet (s t:set X)
    : s ⊆ t -> s ≅ s ∩ t.
  Proof.
    repeat (cset_tac; subst; firstorder).
  Qed.


  Lemma minus_meet (s t u:set X)
    : (s \ t) ∩ u ≅ s ∩ u \ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma set_incl (s t: set X)
    : s ⊆ t -> t ⊆ s -> t ≅ s.
  Proof.
    intros; hnf in *; cset_tac; firstorder.
  Qed.


  Lemma elements_nil_eset (s : set X) :
    s ≅ ∅ <-> elements s = nil.
  Proof.
    split; intros.
    remember (elements s). destruct l; eauto.
    assert (x ∈ s). eapply elements_iff.
    rewrite <- Heql. firstorder.
    exfalso. rewrite H0 in H1. eapply not_in_empty; eauto.

    specialize (elements_iff s); intros.
    rewrite H0 in H1.
    cset_tac. specialize (H1 a). firstorder. inv H1.
  Qed.

  Lemma union_meet_distr_r (s t u : set X) :
    (s ∪ t) ∩ u ≅ (s ∩ u) ∪ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_is_empty (s t : set X) :
    s ∪ t ≅ ∅ -> (s ≅ ∅ /\ t ≅ ∅).
  Proof.
    cset_tac; specialize (H0 a); cset_tac; firstorder.
  Qed.

  Lemma smaller_meet_empty (s t u : set X) :
    (s ∪ t) ∩ u ≅ ∅ -> t ∩ u ≅ ∅.
  Proof.
    intros. cset_tac; specialize (H0 a); cset_tac; firstorder.
  Qed.

  Lemma empty_intersection_in_one_not_other (s t : set X) x :
    s ∩ t ≅ ∅ -> x ∈ s -> ~ x ∈ t.
  Proof.
    cset_tac. specialize (H0 x); cset_tac; firstorder.
  Qed.

  Lemma meet_assoc (s t u : set X)
    : s ∩ t ∩ u ≅ s ∩ (t ∩ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_meet_lr (s s' t t':set X)
    : s ⊆ s' -> t ⊆ t' -> s ∩ t ⊆ s' ∩ t'.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in_union (s t : set X)
    : s ∩ t ⊆ s ∪ t.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_union (s t u:set X)
    : (s ∪ t) \ u ≅ (s \ u) ∪ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_dist_intersection (s t u:set X)
    : (s ∩ t) \ u ≅ (s \ u) ∩ (t \ u).
  Proof.
    cset_tac; firstorder.
  Qed.


  Lemma incl_not_member (s t:set X) x
    : s ⊆ t -> ~x ∈ t -> ~x ∈ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_meet_empty (s t u:set X)
    : s ⊆ t -> u ∩ t ≅ empty -> u ∩ s ≅ empty.
  Proof.
    cset_tac. specialize (H1 a); cset_tac; firstorder.
  Qed.

  Lemma union_incl_split (s t u : set X)
    : s ⊆ u -> t ⊆ u -> s ∪ t ⊆ u.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma union_minus_remove (a b : set X)
        : (a ∪ b) \ a ≅ b \ a.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma minus_incl_meet_special2 (c c' d : set X)
    : c ⊆ d
    -> c ⊆ c'
    -> c ∩ (c' \ (c \ d)) ≅ c.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_minus (s t : set X)
    : s ∩ (t \ s) ≅ ∅.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma meet_in_left (s t : set X)
    : s ∩ t ⊆ s.
  Proof.
    hnf; intros. cset_tac; firstorder.
  Qed.

  Lemma not_in_meet_empty (D:set X) x
    : ~ x ∈ D
    -> D ∩ {{x}} ≅ ∅.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma incl_eq (s t:set X)
    : s ⊆ t -> t ⊆ s -> t ≅ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  Lemma eq_incl (s t:set X)
    : t ≅ s -> s ⊆ t /\ t ⊆ s.
  Proof.
    cset_tac; firstorder.
  Qed.

  End theorems.

  Section moretheorems.

  Require Import List.
  Variable X : Type.
  Context `{OrderedType X}.

  Hypothesis equiv_is_eq : _eq = eq.


End moretheorems.

Definition addf {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y) :=
  (fun x t => add (f x) t).

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f}
  : (addf f)
  with signature
    _eq ==> Equal ==> Equal as addf_morphism.
Proof.
  intros. unfold addf. rewrite H2. rewrite H3. reflexivity.
Qed.

Add Parametric Morphism {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  : (addf f)
  with signature
    eq ==> Equal ==> Equal as addf_morphism2.
Proof.
  intros. unfold addf. rewrite H1. reflexivity.
Qed.

Lemma addf_transpose {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
 : transpose Equal (addf f).
Proof.
  hnf; intros.
  unfold addf. hnf. intros. rewrite add_add. split; eauto.
Qed.


Lemma minus_union_both X `{OrderedType X} (s t: set X) x
  : x ∉ s -> s \ t [=] (s ∪ {{x}}) \ (t ∪ {{x}}).
Proof.
  cset_tac; firstorder.
Qed.

Lemma list_eq_eq {X} {L L':list X}
  : list_eq eq L L' <-> L = L'.
Proof.
  split; intros. eapply list_eq_ind; intros; subst; f_equal; eauto.
  general induction L; econstructor; eauto.
Qed.

Lemma minus_idem X `{OrderedType X} (s t:set X)
: s \ t [=] (s \ t) \ t.
Proof.
  cset_tac; intuition.
Qed.

Lemma meet_incl_eq {X} `{OrderedType X} (s s' t t':set X)
: t' ⊆ t -> s ∩ t [=] s' ∩ t -> s ∩ t' [=] s' ∩ t'.
Proof.
  intros; cset_tac; intuition; firstorder.
Qed.

Lemma InA_in {X} `{OrderedType X} x L
 : InA _eq x L <-> x ∈ of_list L.
Proof.
  split; intros.
  general induction L. inv H0.
  simpl. inv H0. rewrite H2. eapply add_iff; intuition.
  eapply add_iff; intuition.
  general induction L. inv H0.
  simpl in *. eapply add_iff in H0. destruct H0.
  rewrite H0; firstorder.
  constructor 2. eapply IHL; eauto.
Qed.


Lemma minus_minus_eq {X} `{OrderedType X} (s t : set X)
  : s [=] s \ (t \ s).
Proof.
  cset_tac; firstorder.
Qed.


Lemma union_incl_left {X} `{OrderedType X} (s t u: set X)
: s ⊆ t -> s ⊆ t ∪ u.
Proof.
  cset_tac; intuition.
Qed.

Lemma of_list_app X `{OrderedType X} (A B: list X)
  : of_list (A ++ B) [=] of_list A ∪ of_list B.
Proof.
  split; intros.
  - rewrite of_list_1 in H0. cset_tac. eapply InA_app in H0.
    repeat rewrite of_list_1. intuition. destruct H; eauto.
  - rewrite of_list_1. eapply InA_app_iff. destruct H; eauto.
    cset_tac. repeat rewrite of_list_1 in H0. intuition.
Qed.

Lemma incl_set_left X `{OrderedType X} (s t : set X)
: s [=] t -> s [<=] t.
Proof.
  cset_tac; firstorder.
Qed.

Lemma minus_inter_empty X `{OrderedType X} s t u
: s ∩ t [=] s ∩ u
  -> s \ t [=] s \ u.
Proof.
  intros. cset_tac; intuition.
  hnf in H0. eapply H3. eapply H0; eauto.
  eapply H3. eapply H0. eauto.
Qed.

Lemma union_eq_decomp X `{OrderedType X} s s' t t'
: s [=] s' -> t [=] t' -> s ++ t [=] s' ++ t'.
Proof.
  cset_tac; intros; firstorder.
Qed.

Lemma add_struct_eq X `{OrderedType X} x s t
: s [=] t
  -> {x; s} [=] {x; t}.
Proof.
  intros. rewrite H0; eauto.
Qed.

Lemma union_struct_eq_1 X `{OrderedType X} s t u
: s [=] t
  ->  s ++ u [=] t ++ u.
Proof.
  cset_tac; firstorder.
Qed.

Lemma union_struct_eq_2 X `{OrderedType X} s t u
: s [=] t
  ->  u ++ s [=] u ++ t.
Proof.
  cset_tac; firstorder.
Qed.

Lemma not_in_minus X `{OrderedType X} (s t: set X) x
: x ∉ s
  -> x ∉ s \ t.
Proof.
  cset_tac; intuition.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
