Require Export Setoid Coq.Classes.Morphisms.
Require Export CSet Containers.SetDecide.
Require Import EqDec Computable Util AutoIndTac.
Require Export MapBasics.

Set Implicit Arguments.

Section MapLookup.
  Open Scope fmap_scope.
  Variable X : Type.
  Context `{OrderedType X}.
  Variable Y : Type.

  (* Functions are always functional with respect to leibniz equality
   maps are functional w.r.t. the decidable equality they are parameterized over
   *)

  Definition lookup_set `{OrderedType Y} (m:X -> Y) (s:set X) : set Y :=
    SetConstructs.map m s.

  Lemma lookup_set_spec `{OrderedType Y} (m:X -> Y) s y `{Proper _ (_eq ==> _eq) m}
  : y ∈ lookup_set m s <-> exists x, x ∈ s /\ y === m x.
  Proof.
    intros. unfold lookup_set. eapply SetConstructs.map_spec; eauto.
  Qed.

  Lemma lookup_set_helper `{OrderedType Y} (m:X -> Y) s x `{Proper _ (_eq ==> _eq) m}
  : x ∈ s -> m x ∈ lookup_set m s.
  Proof.
    intros. eapply SetConstructs.map_spec; eauto.
  Qed.

  Lemma lookup_set_incl `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : s ⊆ t -> (lookup_set m s) ⊆ (lookup_set m t).
  Proof.
    intros P I; hnf. intros Q.
    eapply lookup_set_spec in Q; [|now eauto].
    decompose records. eapply lookup_set_spec; eauto.
  Qed.

  Lemma lookup_set_union `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : (lookup_set m (s ∪ t)) [=] (lookup_set m s ∪ lookup_set m t).
  Proof.
    intro. split; intros.
    - eapply lookup_set_spec in H2; eauto.
      cset_tac.
      + left. eapply lookup_set_spec; firstorder.
      + right; eapply lookup_set_spec; firstorder.
    - cset_tac; eapply lookup_set_spec in H3; dcr; eauto.
      + eapply lookup_set_spec; eauto. eexists x; cset_tac; firstorder.
      + eapply lookup_set_spec; eauto. eexists x; cset_tac; firstorder.
  Qed.

  Lemma lookup_set_minus_incl `{OrderedType Y}
        (s t:set X) (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : lookup_set m s \ (lookup_set m t) ⊆ lookup_set m (s \ t).
  Proof.
    intros; hnf; intros.
    edestruct minus_in_in; eauto. eapply lookup_set_spec; eauto.
    eapply lookup_set_spec in H3; decompose records.
    eexists x; split; eauto. eapply in_in_minus; eauto.
    intro. eapply H4. eapply lookup_set_spec. intuition.
    eexists x; eauto. intuition.
  Qed.

End MapLookup.

Arguments lookup_set {X} {H} {Y} {H0} m s.

Lemma lookup_set_on_id {X} `{OrderedType X} (s t : set X)
  : s ⊆ t -> (lookup_set (fun x => x) s) ⊆ t.
Proof.
  intros. hnf; intros.
  eapply lookup_set_spec in H1; intuition. firstorder. rewrite H2; auto.
Qed.


Global Instance lookup_set_morphism {X} `{OrderedType X} {Y} `{OrderedType Y} {f:X->Y}
 `{Proper _ (_eq ==> _eq) f}
  : Proper (Subset ==> Subset) (lookup_set f).
Proof.
  unfold Proper, respectful, Subset; intros.
  eapply lookup_set_spec. firstorder. eapply lookup_set_spec in H3.
  decompose records. eexists x0. split. eauto. rewrite H6. eapply H1.
  firstorder. eauto.
Qed.

Global Instance lookup_set_morphism_eq {X} `{OrderedType X} {Y} `{OrderedType Y} {f:X->Y}
 `{Proper _ (_eq ==> _eq) f}
  : Proper (Equal ==> Equal) (lookup_set f).
Proof.
  unfold Proper, respectful, Subset; intros. eapply double_inclusion in H2; dcr.
  split; intros. rewrite <- H3; eauto. rewrite <- H4; eauto.
Qed.

Lemma lookup_set_singleton {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f} x
  : lookup_set f {{x}} [=] {{f x}}.
Proof.
  cset_tac; intuition.
Qed.

Lemma lookup_set_singleton' {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f} x
  : lookup_set f (singleton x) [=] singleton (f x).
Proof.
  cset_tac.
  - eapply lookup_set_spec in H2; dcr; eauto.
    cset_tac; rewrite H4; eauto.
  - eapply lookup_set_spec; eauto.
    eexists x; cset_tac; eauto.
Qed.


Lemma lookup_set_single X `{OrderedType X} Y `{OrderedType Y} (ϱ:X->Y)
      `{Proper _ (_eq ==> _eq) ϱ} D D' v
: v ∈ D
  -> lookup_set ϱ D ⊆ D'
  -> {{ ϱ v }} ⊆ D'.
Proof.
  intros. hnf; intros.
  eapply H3. cset_tac; intuition.
  eapply lookup_set_spec; eauto.
Qed.

Lemma lookup_set_add X `{OrderedType X} Y `{OrderedType Y} x s (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
: (lookup_set m {x; s}) [=] {m x; lookup_set m s}.
Proof.
  intro. split; intros.
  - eapply lookup_set_spec in H2; eauto.
    cset_tac.
    + left; rewrite H2; symmetry; eauto.
    + right; eapply lookup_set_spec; firstorder.
  - cset_tac; eapply lookup_set_spec; eauto.
    + eexists x; cset_tac; firstorder.
    + eapply lookup_set_spec in H3; eauto.
      firstorder.
Qed.

Ltac rewrite_lookup_set dummy := match goal with
           | [ H : context [ In ?y (lookup_set ?f ?s) ] |- _ ] =>
             rewrite (@lookup_set_spec _ _ _ _ f s y) in H
           | [ |- context [ In ?y (lookup_set ?f ?s) ]] =>
             rewrite (@lookup_set_spec _ _ _ _ f s y)
           end.
Ltac lset_tac := set_tac rewrite_lookup_set.


Lemma lookup_set_empty X `{OrderedType X} Y `{OrderedType Y} (ϱ:X->Y)
      `{Proper _ (_eq ==> _eq) ϱ}
: lookup_set ϱ {} [=] {}.
Proof.
  unfold lookup_set. cset_tac.
Qed.

Hint Extern 20 (lookup_set ?ϱ {} [=] {}) => eapply lookup_set_empty; eauto.
Hint Extern 20 ({} [=] lookup_set ?ϱ {}) => symmetry; eapply lookup_set_empty; eauto.

Hint Extern 20 (lookup_set ?ϱ (singleton ?v) [=] singleton (?ϱ ?v)) => eapply lookup_set_singleton'; eauto.
Hint Extern 20 (singleton (?ϱ ?v) [=] lookup_set ?ϱ (singleton ?v)) => symmetry; eapply lookup_set_singleton'; eauto.


Lemma lookup_set_single_fact X `{OrderedType X} (x:X) ϱ `{Proper _ (_eq ==> _eq) ϱ}
  : singleton (ϱ x) ⊆ lookup_set ϱ {x}.
Proof.
  cset_tac.
Qed.

Lemma lookup_set_union_incl X `{OrderedType X} s t u ϱ `{Proper _ (_eq ==> _eq) ϱ}
  : u ⊆ lookup_set ϱ s ∪ lookup_set ϱ t
    -> u ⊆ lookup_set ϱ (s ∪ t).
Proof.
  rewrite lookup_set_union; eauto.
Qed.

(*  This hint Resolve will slow everything down by 100x *)
(* Hint Resolve lookup_set_union_incl. *)
Hint Resolve lookup_set_single_fact.
