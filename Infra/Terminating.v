Require Import Util Get ListUpdateAt PartialOrder AllInRel Annotation.

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
  induction x; intros.
  - inv LE. econstructor. intros ? [A B].
    inv A. exfalso. eapply B. reflexivity.
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
      exfalso; apply B; econstructor; eauto.
      eapply (H0 y1); eauto.
    + eapply (H2 YL0); eauto.
      time rewrite H3. split; eauto.
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
      econstructor; eauto. eapply H.
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
      exfalso; eapply B; econstructor; eauto.
      eapply (H1 y1); eauto.
      intros ? ? Get; inv Get; eauto using get.
    + assert (poLe x0 YL0) by (etransitivity; eauto).
      assert (poLt x0 YL0) by (time rewrite H4; split; eauto).
      eapply H3; eauto.
      * intros ? ? Get. inv Get; eauto using get.
        exploit H2 as Trm; eauto using get.
        eapply terminates_get_list in Trm; eauto.
      * intros. eapply H1; eauto.
        intros ? ? Get; inv Get; eauto using get.
Qed.

Lemma terminating_ann Dom `{PO:PartialOrder Dom}
  : Terminating Dom poLt
    -> Terminating (ann Dom) poLt.
Proof.
  intros Trm a.
  econstructor. intros ? [A _].
  induction A.
  - specialize (Trm b).
    general induction Trm.
    econstructor. intros ? [A B].
    inv A.
    eapply H0; eauto. split; eauto.
    intro. eapply B. econstructor. eauto.
  - pose proof (Trm b) as FST. clear A H.
    rename IHA into SND.
    assert (poLe bn bn) by reflexivity.
    revert H. generalize bn at 2 3.
    induction FST as [? ? FST].
    assert (poLe x x) by reflexivity.
    revert H0. generalize x at 2 3.
    induction SND as [? ? SND].
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq bn bn0).
    + decide (poEq x1 b).
      exfalso; eapply B; econstructor; eauto.
      eapply FST; eauto.
    + eapply (SND bn0); eauto.
  - clear H A1 A2 ans ant a.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    specialize (Trm b).
    induction Trm.
    induction IHA1.
    induction IHA2.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        exfalso; apply B; econstructor; eauto.
        eapply (H4 bnt0); eauto.
      * eapply (H2 bns0); eauto.
    + eapply (H0 b0); eauto.
  - clear H A.
    pose proof (Trm b) as FST.
    rename IHA into SND.
    assert (TRD:terminates poLt bns). {
      eapply terminates_list_get.
      intros. symmetry in H0; edestruct get_length_eq; eauto.
    }
    clear H0 H1 H2.
    assert (poLe bns bns) by reflexivity.
    revert H. generalize bns at 2 3.
    assert (poLe bnt bnt) by reflexivity.
    revert H. generalize bnt at 2 3.
    assert (poLe b b) by reflexivity.
    revert H. generalize b at 2 3.
    induction FST.
    induction SND.
    induction TRD.
    intros.
    econstructor; intros ? [A B].
    inv A.
    decide (poEq b b0).
    + decide (poEq bns bns0).
      * decide (poEq bnt bnt0).
        exfalso; apply B; eauto. econstructor; eauto.
        intros. eapply PIR2_nth in p0; eauto.
        dcr. get_functional. eauto.
        eapply (H2 bnt0); eauto.
      * eapply PIR2_get in H14; eauto.
        eapply (H4 bns0); eauto.
    + eapply PIR2_get in H14; eauto.
      eapply (H0 b0); eauto.
Qed.
