Require Import CSet CMap CMapDomain Infra.PartialOrder Infra.OptionR.

Set Implicit Arguments.

Definition leMap X `{OrderedType X} Y `{PartialOrder Y} (d d': Map [X, Y]) : Prop :=
 (forall x, poLe (find x d) (find x d')).

Lemma leMap_irreflexive X `{OrderedType X} Y `{PartialOrder Y} (x y:Map [X,Y])
: ~leMap x y -> ~Equal x y.
Proof.
  intros. intro. eapply H1.
  hnf; intros. rewrite H2.
  reflexivity.
Qed.

Instance leMap_ref X `{OrderedType X} Y `{PartialOrder Y} : Reflexive (@leMap X _ Y _).
Proof.
  hnf; intros. hnf; intros. reflexivity.
Qed.


Lemma le_domain_find X `{OrderedType X} Y `{PartialOrder Y} x (d d':Map [X, Y])
  : (forall x, x \In domain d ∪ domain d' ->
              poLe ((find x d)) ((find x d')))
    -> poLe (find x d) (find x d').
Proof.
  intros DEQ. specialize (DEQ x). revert DEQ.
  case_eq (find x d'); intros; eauto.
  - eapply find_domain' in H1; eauto.
    eapply DEQ. cset_tac.
  - simpl. case_eq (find x d); intros; eauto; simpl.
    + pose proof H2. eapply find_domain' in H2.
    exploit DEQ; eauto. cset_tac. simpl in *.
    rewrite H3 in H4. eauto.
Qed.

Instance leMap_proper X `{OrderedType X} Y `{PartialOrder Y} (d d':Map [X, Y])
  : Proper (_eq ==> iff) (fun x => find x d ⊑ find x d').
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - rewrite <- H1; eauto.
  - rewrite H1; eauto.
Qed.

Instance leMap_dec X `{OrderedType X} Y `{PartialOrder Y}
  :  forall d d' : Map [X, Y], Computable (leMap d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d')
                                   (fun x => poLe ((find x d))
                                               (find x d'))).
  - eapply leMap_proper.
  - hnf; intros.
    eauto with typeclass_instances.
  - left; eauto.
    hnf; intros.
    eapply le_domain_find; eauto.
  - right; eauto.
Defined.

Instance leMap_tran X `{OrderedType X} Y `{PartialOrder Y}
  : Transitive (@leMap X _ Y _).
Proof.
  hnf. unfold leMap; intros.
  etransitivity; eauto.
Qed.

Definition eqMap X `{OrderedType X} Y `{PartialOrder Y}
           (d d' : Map [X, Y]) : Prop :=
 (forall x, poEq (find x d) (find x d')).

Instance eqMap_Equiv  X `{OrderedType X} Y `{PartialOrder Y}
  : Equivalence (@eqMap X _ Y _).
Proof.
  constructor; unfold eqMap; hnf; intros.
  - reflexivity.
  - symmetry; eauto.
  - etransitivity; eauto.
Qed.


Lemma eq_domain_find X `{OrderedType X} Y `{PartialOrder Y} x (d d':Map [X, Y])
  : (forall x, x \In domain d ∪ domain d' -> poEq (find x d)
                                               (find x d'))
    -> poEq (find x d) (find x d').
Proof.
  intros DEQ. specialize (DEQ x). revert DEQ.
  case_eq (find x d'); intros; eauto.
  - eapply find_domain' in H1; eauto.
    eapply DEQ. cset_tac.
  - simpl. case_eq (find x d); intros; eauto; simpl.
    + pose proof H2. eapply find_domain' in H2.
    exploit DEQ; eauto. cset_tac. simpl in *.
    rewrite H3 in H4. eauto.
Qed.

Instance eqDom_dec X `{OrderedType X} Y `{PartialOrder Y}
  :  forall d d' : Map [X, Y], Computable (eqMap d d').
Proof.
  intros; hnf; intros.
  edestruct (@set_quant_computable _ _ (domain d ∪ domain d')
                                   (fun x => poEq ((find x d))
                                               ((find x d')))).
  - unfold Proper, respectful; intros.
    split; intros.
    rewrite <- H1; eauto.
    rewrite H1; eauto.
  - hnf; intros.
    eauto with typeclass_instances.
  - left; eauto.
    hnf; intros. eapply eq_domain_find; eauto.
  - right; eauto.
Defined.

Instance leMap_anti X `{OrderedType X} Y `{PartialOrder Y}
  : Antisymmetric (Map [X, Y]) (@eqMap X _ Y _) (@leMap X _ Y _).
Proof.
  hnf. unfold leMap, Equal.
  intros. hnf; intros.
  eapply poLe_antisymmetric in H1; eauto.
Qed.

Set Implicit Arguments.

Instance find_eqMap_proper  X `{OrderedType X} Y `{PartialOrder Y}
  : Proper (_eq ==> @eqMap X _ Y _  ==> poEq) find.
Proof.
  unfold Proper, respectful, eqMap.
  intros. rewrite H2, H1. reflexivity.
Qed.

Instance Dom_semilattice_ltDom  X `{OrderedType X} Y `{PartialOrder Y}
  : PartialOrder (Map [X, Y]) := {
  poLe := @leMap X _ Y _;
  poLe_dec := (@leMap_dec X _ Y _);
  poEq := @eqMap X _ Y _;
  poEq_dec := _
}.
Proof.
  intros. hnf; intros.
  rewrite H1. reflexivity.
Defined.


Lemma leMap_domain X `{OrderedType X} Y `{PartialOrder Y} x y
  : leMap x y -> domain x ⊆ domain y.
Proof.
  unfold leMap. intros.
  hnf; intros.
  specialize (H1 a).
  eapply domain_find in H2. dcr.
  rewrite H3 in H1. inv H1.
  eapply find_domain. congruence.
Qed.



Instance ltMap_proper X `{OrderedType X} Y `{PartialOrder Y} (d d':Map [X, Y])
  : Proper (_eq ==> iff) (fun x => find x d ⊏ find x d').
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  - rewrite <- H1; eauto.
  - rewrite H1; eauto.
Qed.


Lemma leMap_remove X `{OrderedType X} Y `{PartialOrder Y} (m m':Map [X, Y]) x
  : leMap m m'
    -> leMap (remove x m) (remove x m').
Proof.
  unfold leMap; intros LE y.
  specialize (LE y).
  decide (x === y).
  - rewrite !MapFacts.remove_eq_o; eauto.
  - rewrite !MapFacts.remove_neq_o; eauto.
Qed.

Lemma eqMap_remove X `{OrderedType X} Y `{PartialOrder Y} (m m':Map [X, Y]) x
  : eqMap m m'
    -> eqMap (remove x m) (remove x m').
Proof.
  unfold eqMap; intros LE y.
  specialize (LE y).
  decide (x === y).
  - rewrite !MapFacts.remove_eq_o; eauto.
  - rewrite !MapFacts.remove_neq_o; eauto.
Qed.
