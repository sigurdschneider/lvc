Require Export Setoid Coq.Classes.Morphisms Omega.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec CSetNotation CSetTac CSetComputable.
Require Import CSetDisjoint CSetGet Drop AllInRel.

Set Implicit Arguments.


Definition pairwise_ne {X} (P:X->X->Prop) (L:list X) :=
  forall n m a b, n <> m -> get L n a -> get L m b -> P a b.

Lemma pairwise_ne_rev X (P:relation X) (L: list X)
: pairwise_ne P L
  -> pairwise_ne P (rev L).
Proof.
  intros; hnf; intros.
  exploit (get_range H1); eauto.
  exploit (get_range H2); eauto.
  eapply get_rev in H1.
  eapply get_rev in H2.
  eapply H; try eapply H1; try eapply H2; eauto.
  rewrite rev_length in H3.
  rewrite rev_length in H4.
  omega.
Qed.

Definition pairwise_disj_PIR2 X `{OrderedType X} L L'
: pairwise_ne disj L
  -> PIR2 Equal L L'
  -> pairwise_ne disj L'.
Proof.
  unfold pairwise_ne; intros.
  eapply PIR2_nth_2 in H3; eauto; dcr.
  eapply PIR2_nth_2 in H4; eauto; dcr.
  rewrite <- H7, <- H8; eauto.
Qed.

Fixpoint pw_disj X `{OrderedType X} (L:list (set X)) :=
  match L with
    | x::xs => disj x (list_union xs) /\ pw_disj xs
    | nil => True
  end.

Lemma pw_disj_get X `{OrderedType X} (L:list (set X)) n s
: pw_disj L -> get L n s -> disj s (list_union (drop (S n) L)).
Proof.
  intros. general induction H1; simpl in * |- *; eauto.
Qed.

Lemma pw_disj_pairwise_disj X `{OrderedType X} (L:list (set X))
: pw_disj L -> pairwise_ne disj L.
Proof.
  intros. hnf; intros.
  exploit pw_disj_get; try eapply H2; eauto.
  exploit pw_disj_get; try eapply H3; eauto.
  decide (n < m).
  - eapply disj_2_incl; eauto. eapply incl_list_union.
    eapply drop_get. instantiate (2:=m - S n).
    orewrite (S n + (m - S n) = m); eauto. eauto.
  - symmetry. eapply disj_2_incl; eauto.
    eapply incl_list_union.
    eapply drop_get. instantiate (2:=n - S m).
    orewrite (S m + (n - S m) = n); eauto. eauto.
Qed.

Definition disjoint X `{OrderedType X} (DL:list (option (set X))) (G:set X) :=
  forall n s, get DL n (Some s) -> disj s G.

Lemma disjoint_incl X `{OrderedType X} L D D'
  : disjoint L D
    -> D' ⊆ D
    -> disjoint L D'.
Proof.
  firstorder.
Qed.

Instance disjoint_morphism_subset X `{OrderedType X}
  : Proper (eq ==> Subset ==> flip impl) (@disjoint X _).
Proof.
  unfold Proper, respectful, impl, flip, disj, disjoint; intros; subst.
  rewrite H1; eauto.
Qed.

Instance disjoint_morphism X `{OrderedType X}
  : Proper (eq ==> Equal ==> iff) (@disjoint X _).
Proof.
  unfold Proper, respectful, iff, disjoint; split; intros; subst.
  - rewrite <- H1; eauto.
  - rewrite H1; eauto.
Qed.

Lemma disjoint_app X `{OrderedType X} L L' D
: disjoint (L ++ L') D <-> disjoint L D /\ disjoint L' D.
Proof.
  split; unfold disjoint.
  - split; intros; eauto using get_shift, get_app.
  -intros. eapply get_app_cases in H1; intuition; eauto.
Qed.
