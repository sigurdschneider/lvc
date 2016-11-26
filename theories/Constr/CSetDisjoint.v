Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation CSetTac CSetComputable.

Set Implicit Arguments.

Definition disj {X} `{OrderedType X} (s t: set X)
  := forall x, x ∈ s -> x ∈ t -> False.

Instance disj_sym {X} `{OrderedType X} : Symmetric disj.
Proof.
  unfold Symmetric, disj; intros.
  cset_tac; intuition; eauto.
Qed.

Instance disj_eq_eq_iff {X} `{OrderedType X}
: Proper (Equal ==> Equal ==> iff) disj.
Proof.
  unfold Proper, respectful, disj; intros.
  cset_tac; firstorder.
Qed.

Instance disj_subset_subset_flip_impl {X} `{OrderedType X}
: Proper (Subset ==> Subset ==> flip impl) disj.
Proof.
  unfold Proper, respectful, disj, flip, impl; intros.
  firstorder.
Qed.

Lemma disj_app {X} `{OrderedType X} (s t u: set X)
: disj s (t ∪ u) <-> disj s t /\ disj s u.
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

Lemma disj_incl X `{OrderedType X} (D1 D1' D2 D2':set X)
  : disj D1' D2'
    -> D1 ⊆ D1'
    -> D2 ⊆ D2'
    -> disj D1 D2.
Proof.
  intros.
  eapply disj_1_incl. eapply disj_2_incl; eauto.
  eauto.
Qed.

Hint Resolve disj_incl : cset.

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

Lemma disj_minus_eq X `{OrderedType X} (s t:set X)
: disj s t
  -> s \ t [=] s.
Proof.
  unfold disj; cset_tac; intuition; eauto.
Qed.


Lemma disj_not_in X `{OrderedType X} x s
: disj {x} s
  -> x ∉ s.
Proof.
  unfold disj; cset_tac.
Qed.

Lemma disj_eq_minus X `{OrderedType X} (s t u: set X)
: s [=] t
  -> disj t u
  -> s [=] t \ u.
Proof.
  unfold disj.
  cset_tac; intuition; eauto.
  - eapply H0; eauto.
  - eapply H1; intuition; eauto. eapply H0; eauto.
  - eapply H0; eauto.
Qed.

Lemma disj_struct_1 X `{OrderedType X} s t u
: s [=] t
  ->  disj s u -> disj t u.
Proof.
  intros. rewrite <- H0; eauto.
Qed.

Lemma disj_struct_1_r X `{OrderedType X} s t u
: s [=] t
  ->  disj t u -> disj s u.
Proof.
  intros. rewrite H0; eauto.
Qed.

Lemma disj_struct_2 X `{OrderedType X} s t u
: s [=] t
  ->  disj u s -> disj u t.
Proof.
  intros. rewrite <- H0; eauto.
Qed.

Lemma disj_struct_2_r X `{OrderedType X} s t u
: s [=] t
  ->  disj u t -> disj u s.
Proof.
  intros. rewrite H0; eauto.
Qed.

Lemma disj_intersection X `{OrderedType X} s t
  : disj s t <-> s ∩ t [=] ∅.
Proof.
  intros. split; cset_tac; firstorder.
Qed.

Lemma not_incl_minus X `{OrderedType X} (s t u: set X)
: s ⊆ t
  -> disj s u
  -> s ⊆ t \ u.
Proof.
  cset_tac; intuition.
Qed.

Lemma disj_minus X `{OrderedType X} s t u
  : (s ∩ t) ⊆ u
    -> disj s (t \ u).
Proof.
  intros. hnf; intros. specialize (H0 x).
  cset_tac.
Qed.
