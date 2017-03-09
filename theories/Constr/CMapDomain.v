Require Import CMap MoreList.

Definition domain {X} `{OrderedType X} {Y} (d:Map [X, Y])
: set X := of_list (List.map fst (elements d)).

(*
Lemma domain_join (d d':Dom)
: domain (map2 join' d d') [=] domain d ∪ domain d'.
Proof.
  unfold domain. split; intros.
  - eapply of_list_1 in H.
    eapply InA_map_inv with (R':=eq_key_elt) in H; eauto.
    destruct H; dcr. destruct x. simpl in *; subst.
    assert (IN:In n (map2 join d d')). {
      rewrite MapFacts.elements_in_iff; eauto.
    }
    eapply map2_2 in IN.
    destruct IN; eauto.
    + eapply MapFacts.elements_in_iff in H; dcr.
      eapply InA_eq_key_elt in H1. cset_tac.
    + eapply MapFacts.elements_in_iff in H; dcr.
      eapply InA_eq_key_elt in H1. cset_tac.
  - eapply of_list_1.
    cset_tac'.
    + eapply of_list_1 in H0.
      eapply InA_map_inv with (R':=eq_key_elt) in H0; eauto.
      destruct H0; dcr. destruct x. simpl in *; subst.
      assert (IN:In n d). {
        rewrite MapFacts.elements_in_iff; eauto.
      }
      eapply of_list_1.
      enough (exists y, InA eq_key_elt (n,y) (elements (map2 join d d'))). {
        dcr. eapply InA_eq_key_elt; eauto.
      }
      eapply MapFacts.elements_in_iff.
      rewrite MapFacts.in_find_iff.
      rewrite map2_1; eauto.
      eapply MapFacts.in_find_iff in IN.
      destruct (find n d); simpl in *; isabsurd.
      repeat cases; eauto; discriminate.
    + eapply of_list_1 in H0.
      eapply InA_map_inv with (R':=eq_key_elt) in H0; eauto.
      destruct H0; dcr. destruct x. simpl in *; subst.
      assert (IN:In n d'). {
        rewrite MapFacts.elements_in_iff; eauto.
      }
      eapply of_list_1.
      enough (exists y, InA eq_key_elt (n,y) (elements (map2 join d d'))). {
        dcr. eapply InA_eq_key_elt; eauto.
      }
      eapply MapFacts.elements_in_iff.
      rewrite MapFacts.in_find_iff.
      rewrite map2_1; eauto.
      eapply MapFacts.in_find_iff in IN.
      destruct (find n d'); simpl in *; isabsurd.
      destruct (find n d); simpl; repeat cases; eauto; subst;
        discriminate.
Qed.
 *)


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
