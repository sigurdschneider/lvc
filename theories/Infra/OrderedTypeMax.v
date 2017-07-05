Require Import CSet.

Definition nr_max X `{OrderedType X} (x y:X) :=
  if [_lt x y] then y else x.

Arguments nr_max {X} {H} x y.

Instance nr_max_eq_proper X `{OrderedType X}
  : Proper (_eq ==> _eq ==> _eq) nr_max.
Proof.
  unfold Proper, respectful; intros.
  unfold nr_max. repeat cases; eauto.
  exfalso. eapply NOTCOND. rewrite <- H1, <- H0. eauto.
  exfalso. eapply NOTCOND. rewrite H1, H0. eauto.
Qed.

Lemma nr_max_sym X `{OrderedType X} (x y:X)
  : nr_max x y === nr_max y x.
Proof.
  unfold nr_max; repeat cases; eauto.
  - exfalso. assert (_lt x x) by (etransitivity; eauto).
    eapply OrderedType.StrictOrder_Irreflexive in H0; eauto.
  - eapply lt_trans_eq; eauto.
Qed.

Lemma nr_max_assoc X `{OrderedType X} (x y z:X)
  : nr_max x (nr_max y z) === nr_max (nr_max x y) z.
Proof.
  unfold nr_max.
  decide (_lt y z); decide (_lt x y).
  - assert (_lt x z) by (etransitivity; eauto).
    repeat cases; eauto.
  - repeat cases; eauto.
  - repeat cases; eauto.
    exfalso; eauto.
  - repeat cases; eauto.
    exfalso; eauto.
    eapply le_trans; eauto.
Qed.