Require Import Util Get ListUpdateAt PartialOrder AllInRel.

Set Implicit Arguments.

Inductive terminates X (R: X -> X -> Prop) : X -> Prop :=
| terminatesI x : (forall y, R x y -> terminates R y) -> terminates R x.

Class Terminating X (R: X -> X -> Prop) : Prop :=
  terminating : forall x, terminates R x.

Arguments Terminating X R : clear implicits.

Instance terminating_list Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> Terminating (list Dom) poLt.
Proof.
  intros. hnf; intros.
  assert (LE:poLe x x) by reflexivity.
  revert LE. generalize x at 2 3.
  induction x; intros; clear_trivial_eqs.
  - inv LE. econstructor. intros ? [A B].
    inv A. exfalso. eauto.
  - invc LE.
    specialize (H a).
    revert y pf YL H3.
    induction H; intros.
    assert (poLe x x) by reflexivity.
    revert y pf YL H3. specialize (IHx _ H1). clear H1.
    induction IHx; intros.
    econstructor. intros ? [A B]; inv A.
    decide (poEq YL YL0).
    + decide (poEq y y1).
      * exfalso; apply B.
        rewrite p, p0. reflexivity.
      * eapply (H0 y1); eauto.
    + eapply (H2 YL0); eauto.
      split; eauto.
      rewrite H3, H7. reflexivity.
      intro. eapply n.
      eapply poLe_antisymmetric; eauto.
Qed.

Lemma terminates_get_list Dom `{PO:PartialOrder Dom} L
  : terminates poLt L
    -> forall n x, get L n x -> terminates poLt x.
Proof.
  intro Trm.
  induction Trm; intros.
  + econstructor; intros.
    eapply H0. instantiate (1:=list_update_at x n y).
    * revert H1 H2. clear_all.
      general induction x; simpl; isabsurd.
      inv H1.
      split. econstructor; eauto.
      intro. eapply H2. inv H; eauto.
      exploit IHx; eauto. split; eauto.
      intro. eapply H. inv H0; eauto.
    * eapply list_update_at_get_3; eauto.
Qed.

Lemma terminates_list_get Dom `{PO:PartialOrder Dom} L
  : (forall n x, get L n x -> terminates poLt x)
    -> terminates poLt L.
Proof.
  intros.
  assert (LE:poLe L L) by reflexivity.
  revert LE. generalize L at 2 3.
  induction L; intros.
  - inv LE. econstructor. intros ? [A B].
    inv A. exfalso. eapply B. reflexivity.
  - invc LE.
    pose proof (H 0 a (getLB _ _)).
    revert y pf YL H3.
    induction H0; intros.
    exploit IHL; [ eauto using get | reflexivity |].
    revert y pf YL H3.
    induction H2; intros.
    econstructor. intros ? [A B]; inv A.
    decide (poEq YL YL0).
    + decide (poEq y y1).
      exfalso; eapply B.
      rewrite p, p0; eauto.
      eapply (H1 y1); eauto.
      intros ? ? Get; inv Get; eauto using get.
    + assert (poLe x0 YL0) by (etransitivity; eauto).
      assert (poLt x0 YL0). {
        split; eauto. intro. eapply n.
        eapply poLe_antisymmetric; eauto.
      }
      eapply H3; eauto.
      * intros ? ? Get. inv Get; eauto using get.
        exploit H2 as Trm; eauto using get.
        eapply terminates_get_list in Trm; eauto.
      * intros. eapply H1; eauto.
        intros ? ? Get; inv Get; eauto using get.
Qed.

Instance terminating_sig Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> forall P, Terminating { x : Dom | P x } poLt.
Proof.
  intros Trm P [x Px].
  specialize (Trm x).
  induction Trm.
  econstructor.
  intros [y Py] [LE NEQ]; simpl in *.
  eapply H0. split; eauto.
Qed.

Instance terminating_pair Dom `{PO:PartialOrder Dom} Dom' `{PO':PartialOrder Dom'}
  : Terminating Dom poLt
    -> Terminating Dom' poLt
    -> Terminating (Dom * Dom') poLt.
Proof.
  intros Trm1 Trm2 [x y].
  specialize (Trm1 x).
  specialize (Trm2 y).
  assert (H:poLe y y) by reflexivity; revert H.
  generalize y at 2 3.
  induction Trm1.
  assert (H':poLe x x) by reflexivity; revert H'.
  generalize x at 2 3.
  induction Trm2.
  econstructor.
  intros [z z'] [[LE1 LE2] NEQ]; simpl in *.
  decide (poEq x1 z).
  + decide (poEq y z').
    * exfalso; eapply NEQ; split; simpl; eauto.
    * eapply (H2 z'); eauto.
  + eapply H0; eauto.
Qed.

Instance terminating_bool
  : Terminating bool poLt.
Proof.
  intros x.
  econstructor. intros y [A B].
  destruct x, y; simpl in *; isabsurd.
  econstructor. intros [] [A' B']; isabsurd.
Qed.
