Require Import CMap MoreList MapNotations.

Definition domain {X} `{OrderedType X} {Y} (d:Map [X, Y])
: set X := of_list (List.map fst (elements d)).


Lemma not_domain_find {X} `{OrderedType X} {Y} (d:Map [X, Y]) x
: x ∉ domain d -> find x d = None.
Proof.
  unfold domain. intros.
  case_eq (find x d); intros; eauto.
  exfalso. eapply H0.
  rewrite MapFacts.elements_o in H1.
  eapply findA_get in H1. destruct H1 as [? [? ]]; dcr; subst.
  unfold MapFacts.eqb in H5.
  cbv in H5. destruct x0.
  pose proof (_compare_spec x x0).
  Transparent compare. unfold compare in H5.
  inv H1; rewrite  <- H3 in H5; intuition.
  rewrite H4.
  eapply get_in_of_list. change x0 with (fst (x0, y)). eapply map_get_1; eauto.
Qed.

Lemma domain_find {X} `{OrderedType X} {Y} (d:Map [X, Y]) x
: x ∈ domain d -> exists v, find x d = Some v.
Proof.
  unfold domain.
  intros IN.
  eapply of_list_get_first in IN; dcr. inv_get.
  destruct x2.
  eapply get_InA_R with (R:=eq_key_elt) in H0; eauto.
  rewrite <- MapFacts.elements_mapsto_iff in H0.
  eapply MapFacts.find_mapsto_iff in H0. simpl in *. rewrite <- H1 in H0.
  eauto.
Qed.

Lemma find_domain (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) (x : X)
  : find x d <> None -> x \In domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply not_domain_find in n. congruence.
Qed.

Lemma not_find_domain (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) (x : X)
  : find x d = None -> x ∉ domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply domain_find in i. dcr; congruence.
Qed.

Lemma find_domain' (X : Type) (H : OrderedType X) (Y : Type) (d : Map [X, Y]) x v
  : find x d = Some v -> x \In domain d.
Proof.
  intros.
  decide (x ∈ domain d); eauto.
  exfalso. eapply not_domain_find in n. congruence.
Qed.


Lemma domain_remove X `{OrderedType X} Y (m:Map [X,Y]) x
  : domain (remove x m) [=] domain m \ singleton x.
Proof.
  eapply incl_eq.
  - hnf; intros.
    cset_tac'.
    eapply find_domain.
    rewrite !MapFacts.remove_neq_o; eauto.
    eapply domain_find in H1; dcr; congruence.
  - hnf; intros.
    eapply domain_find in H0; dcr.
    decide (x === a).
    + rewrite !MapFacts.remove_eq_o in H1; eauto. congruence.
    + rewrite !MapFacts.remove_neq_o in H1; eauto.
      eapply find_domain' in H1. cset_tac.
Qed.


Lemma domain_add (X : Type) (H : OrderedType X) (Y : Type) (m : Map [X, Y]) (x : X) v
  : domain (m [- x <- v -]) [=] {x; domain m}.
Proof.
  eapply incl_eq.
  - hnf; intros. cset_tac'.
    + eapply find_domain. mlud. congruence.
    + eapply find_domain. mlud. congruence.
      eapply domain_find in H1; dcr. congruence.
  - hnf; intros. cset_tac'.
    + eapply find_domain.
      eapply domain_find in H0; dcr.
      rewrite MapFacts.add_neq_o in H1; try congruence.
Qed.
