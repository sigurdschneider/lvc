Require Export Setoid Coq.Classes.Morphisms.
Require Export CSet Containers.SetDecide.
Require Import EqDec Computable Util AutoIndTac.
Require Export MapBasics.

Set Implicit Arguments.

Definition lookup_set X `{OrderedType X} Y `{OrderedType Y} (m:X -> Y) (s:set X) : set Y :=
  SetConstructs.map m s.

Lemma lookup_set_spec X `{OrderedType X} Y `{OrderedType Y} (m:X -> Y) s y `{Proper _ (_eq ==> _eq) m}
  : y ∈ lookup_set m s <-> exists x, x ∈ s /\ y === m x.
Proof.
  intros. unfold lookup_set. eapply SetConstructs.map_spec; eauto.
Qed.


Ltac rewrite_lookup_set dummy := match goal with
                                | [ H : context [ In _ (lookup_set ?f ?s) ] |- _ ] =>
                                  rewrite (@lookup_set_spec _ _ _ _ f s) in H
                                | [ |- context [ In _ (lookup_set ?f ?s) ]] =>
                                  rewrite (@lookup_set_spec _ _ _ _ f s)
                                end.
Ltac lset_tac := set_tac rewrite_lookup_set.


Lemma lookup_set_helper X `{OrderedType X} Y `{OrderedType Y} (m:X -> Y) s x `{Proper _ (_eq ==> _eq) m}
  : x ∈ s -> m x ∈ lookup_set m s.
Proof.
  intros. eapply SetConstructs.map_spec; eauto.
Qed.

Lemma lookup_set_incl X `{OrderedType X} Y `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : s ⊆ t -> (lookup_set m s) ⊆ (lookup_set m t).
Proof.
  intros P I; hnf. intros Q.
  eapply lookup_set_spec in Q; [|now eauto].
  dcr. eapply lookup_set_spec; eauto.
Qed.

Lemma lookup_set_union X `{OrderedType X} Y `{OrderedType Y} s t (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : (lookup_set m (s ∪ t)) [=] (lookup_set m s ∪ lookup_set m t).
Proof.
  intro. split; intros; lset_tac.
Qed.

Lemma lookup_set_minus_incl X `{OrderedType X} Y `{OrderedType Y}
      (s t:set X) (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : lookup_set m s \ (lookup_set m t) ⊆ lookup_set m (s \ t).
Proof.
  lset_tac.
Qed.

Lemma lookup_set_minus_single_incl X `{OrderedType X} Y `{OrderedType Y}
      (s:set X) x (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
  : lookup_set m s \ singleton (m x) ⊆ lookup_set m (s \ singleton x).
Proof.
  intros; hnf; intros.
  eapply lookup_set_minus_incl; eauto.
Qed.

Arguments lookup_set {X} {H} {Y} {H0} m s.

(*
Instance In_morph_Subset_flip (Y : Type) (H : OrderedType Y)
  : Proper (_eq ==> flip Subset ==> flip impl) In.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  rewrite <- H1, H0. eauto.
Qed.

Instance In_morph_Subset_flip' (Y : Type) (H : OrderedType Y)
  : Proper (equiv ==> flip Subset ==> flip impl) In.
Proof.
  unfold Proper, respectful, flip, impl; intros.
  rewrite <- H1, H0. eauto.
Qed.
 *)


Lemma lookup_set_on_id {X} `{OrderedType X} (s t : set X)
  : s ⊆ t -> (lookup_set (fun x => x) s) ⊆ t.
Proof.
  lset_tac.
Qed.


Instance lookup_set_morphism {X} `{OrderedType X} {Y} `{OrderedType Y} {f:X->Y}
 `{Proper _ (_eq ==> _eq) f}
  : Proper (Subset ==> Subset) (lookup_set f).
Proof.
  unfold Proper, respectful, Subset; intros.
  lset_tac.
Qed.

Instance lookup_set_morphism_flip {X} `{OrderedType X} {Y} `{OrderedType Y} {f:X->Y}
 `{Proper _ (_eq ==> _eq) f}
  : Proper (flip Subset ==> flip Subset) (lookup_set f).
Proof.
  unfold Proper, respectful, flip, Subset; intros.
  lset_tac.
Qed.

Instance lookup_set_morphism_eq {X} `{OrderedType X} {Y} `{OrderedType Y} {f:X->Y}
 `{Proper _ (_eq ==> _eq) f}
  : Proper (Equal ==> Equal) (lookup_set f).
Proof.
  unfold Proper, respectful, Subset; intros ? ? A.
  eapply double_inclusion in A; dcr. lset_tac.
Qed.

Lemma lookup_set_singleton {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f} x
  : lookup_set f {{x}} [=] {{f x}}.
Proof.
  cset_tac.
Qed.

Lemma lookup_set_singleton' {X} `{OrderedType X} {Y} `{OrderedType Y} (f:X->Y)
  `{Proper _ (_eq ==> _eq) f} x
  : lookup_set f (singleton x) [=] singleton (f x).
Proof.
  lset_tac.
  - rewrite H4; eauto.
Qed.


Lemma lookup_set_single X `{OrderedType X} Y `{OrderedType Y} (ϱ:X->Y)
      `{Proper _ (_eq ==> _eq) ϱ} D D' v
: v ∈ D
  -> lookup_set ϱ D ⊆ D'
  -> {{ ϱ v }} ⊆ D'.
Proof.
  intros. rewrite <- H3. lset_tac.
Qed.

Lemma lookup_set_single' X `{OrderedType X} Y `{OrderedType Y} (ϱ:X->Y)
      `{Proper _ (_eq ==> _eq) ϱ} D D' v
: v ∈ D
  -> lookup_set ϱ D ⊆ D'
  -> singleton (ϱ v) ⊆ D'.
Proof.
  intros. rewrite <- H3. lset_tac.
Qed.

Lemma lookup_set_add X `{OrderedType X} Y `{OrderedType Y} x s (m:X -> Y) `{Proper _ (_eq ==> _eq) m}
: (lookup_set m {x; s}) [=] {m x; lookup_set m s}.
Proof.
  intro. lset_tac.
Qed.

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
Hint Immediate lookup_set_union_incl : cset.
Hint Resolve lookup_set_single_fact : cset.

Lemma map_incl X `{OrderedType X} Y `{OrderedType Y} D D' (f:X->Y)
      `{Proper _ (_eq ==> _eq) f}
  : D ⊆ D'
    -> map f D ⊆ map f D'.
Proof.
  intros; hnf; intros. cset_tac.
Qed.

Hint Resolve map_incl : cset.

Lemma map_incl_incl X `{OrderedType X} Y `{OrderedType Y} (f:X->Y)
      `{Proper _ (_eq ==> _eq) f} (s t:set X) (u: set Y)
  : map f s ⊆ u
    -> t ⊆ s
    -> map f t ⊆ u.
Proof.
  intros. rewrite map_incl; eauto.
Qed.

Hint Resolve map_incl_incl : cset.
