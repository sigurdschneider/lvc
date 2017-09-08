Require Import CSet Le Arith.Compare_dec Plus Util NaturalRep.

Lemma all_in_lv_cardinal' X `{NaturalRepresentation X} (lv:set X) (n:nat)
  : (forall m : X, _lt m (ofNat n) -> m \In lv) -> cardinal lv >= n.
Proof.
  general induction n; simpl.
  - omega.
  - exploit (IHn (lv \ singleton (ofNat n))).
    + intros. cset_tac'.
      * eapply H1. etransitivity; eauto.
        eapply order_respecting. omega.
      * rewrite <- H3 in H2. exfalso.
        eapply OrderedType.StrictOrder_Irreflexive in H2. eauto.
    + assert (EQ:lv [=] {ofNat n; lv \ singleton (ofNat n) }). {
        exploit (H1 (ofNat n)); eauto.
        eapply order_respecting. omega.
        cset_tac.
      }
      rewrite EQ.
      assert (ofNat n ∉ lv \ singleton (ofNat n)) by cset_tac.
      erewrite cardinal_2; eauto. omega.
Qed.

Arguments all_in_lv_cardinal' {X} {H} {H0} lv n.

Lemma all_in_lv_cardinal X `{NaturalRepresentation X} (lv:set X) y
  : (forall x : X, _lt x y -> x \In lv) -> cardinal lv >= asNat y.
Proof.
  intros. eapply all_in_lv_cardinal'.
  intros m. rewrite ofNat_asNat. eauto.
Qed.

Arguments all_in_lv_cardinal {X} {H} {H0} lv y.

Lemma neg_pidgeon_hole X `{NaturalRepresentation X} (lv:set X)
  : (forall m : X, _lt m (ofNat (S (cardinal lv))) -> m \In lv) -> False.
Proof.
  intros. exploit (all_in_lv_cardinal' lv (S (cardinal lv))); eauto.
  - omega.
Qed.
