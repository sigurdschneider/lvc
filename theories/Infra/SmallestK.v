Require Import CSet NaturalRep InfiniteSubset InfinitePartition.

Set Implicit Arguments.

Fixpoint nextk X `{OrderedType X} (p:inf_subset X) n (x:X) :=
  match n with
  | 0 => nil
  | S n =>
    let y := proj1_sig (inf_subset_inf p x) in
    x::nextk p n y
  end.

Lemma nextk_length X `{OrderedType X} (p:inf_subset X) n x
  : ❬nextk p n x❭ = n.
Proof.
  general induction n; simpl; eauto.
Qed.

Lemma nextk_p X `{OrderedType X} (p:inf_subset X) n x (P:p x)
  : forall y, InA _eq y (nextk p n x) -> p y.
Proof.
  intros. general induction H0; destruct n; simpl in *; clear_trivial_eqs.
  - rewrite H0 in *. eauto.
  - revert H0; destr_sig; intros; dcr. simpl in *. dcr.
    eapply IHInA. eauto. reflexivity.
Qed.


Definition ksmallest X `{OrderedType X} (p:inf_subset X) n :=
  nextk p n (proj1_sig (inf_subset_least p)).

Lemma nextk_lt X `{OrderedType X} (p:inf_subset X) n x
  : forall y, InA _eq y (nextk p n x) -> _lt x y \/ _eq x y.
Proof.
  intros.
  general induction H0; destruct n; simpl in *; clear_trivial_eqs; eauto.
  revert H0. destr_sig; dcr; eauto. simpl in *. dcr.
  exploit IHInA; eauto.
  intros. destruct H1; eauto.
  - left. etransitivity; eauto.
  - left. rewrite <- H1. eauto.
Qed.

Lemma nextk_nodup X `{OrderedType X} (p:inf_subset X) n x
  : NoDupA _eq (nextk p n x).
Proof.
  general induction n; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro. eapply nextk_lt in H0. revert H0. destr_sig.
  intro. dcr.
  destruct H0.
  - rewrite H0 in H3.
    eapply OrderedType.StrictOrder_Irreflexive in H3. cset_tac.
  - rewrite H0 in *.
    eapply OrderedType.StrictOrder_Irreflexive in H3. cset_tac.
Qed.

Lemma ksmallest_card X `{OrderedType X} (p:inf_subset X) k
  : SetInterface.cardinal (of_list (ksmallest p k)) = k.
Proof.
  rewrite cardinal_of_list_nodup; eauto using nextk_nodup, nextk_length.
Qed.

Lemma nextk_greater X `{OrderedType X} (p:inf_subset X) k x z
      (NOTIN:x ∉ of_list (nextk p k z))
      (GR: _lt z x \/ _eq z x) (P:p z) (P':p x)
  : forall y : X, y \In of_list (nextk p k z) -> _lt y x.
Proof.
  general induction k; simpl in *.
  - cset_tac.
  - revert H0. destr_sig. simpl in *; intros. dcr.
    assert (_lt x0 x \/ _eq x0 x). {
      destruct GR as [GR|GR].
      - decide (_lt x x0); eauto.
        + exploit H4. eapply P'. eauto. destruct H2.
          exfalso. rewrite H2 in GR.
          exfalso. eapply OrderedType.StrictOrder_Irreflexive in GR. cset_tac.
          rewrite H2 in GR.
          exfalso. eapply OrderedType.StrictOrder_Irreflexive in GR. cset_tac.
        + decide (x0 === x); eauto.
          left.
          eapply le_neq. eapply n. cset_tac.
      - rewrite GR in *. cset_tac.
    }
    cset_tac'.
    + rewrite <- H0. rewrite <- H8. eauto.
    + rewrite <- H0. rewrite <- H8. eauto.
Qed.

Lemma least_fresh_part_bounded X
      `{NaturalRepresentationSucc X}
      `{@NaturalRepresentationMax X H H0}
      k (lv:set X) (p:inf_subset X)
      (* (INCL1: of_list (ksmallest p k) ⊆ lv)*)
      (INCL: SetInterface.cardinal (filter p lv) < k)
  : least_fresh_P p lv ∈ of_list (ksmallest p k).
Proof.
  edestruct (least_fresh_P_full_spec p lv); dcr.
  decide (least_fresh_P p lv \In of_list (ksmallest p k)); eauto.
  exfalso.
  set (x:=least_fresh_P p lv) in *.
  assert (forall y, y ∈ of_list (ksmallest p k) -> _lt y x /\ p y). {
    intros. unfold ksmallest in *.
    exploit nextk_greater; try eapply n; eauto.
    - destruct k; simpl in *. cset_tac.
      destr_sig; dcr. simpl in *. dcr.
      edestruct (H8 x); eauto.
    - destr_sig; eauto.
    - split; eauto.
      eapply InA_in in H4.
      eapply nextk_p in H4. eauto. destr_sig; dcr; eauto.
  }
  assert (of_list (ksmallest p k) ⊆ filter p lv). {
    hnf; intros.
    eapply H4 in H7. eapply H5; eauto.
  }
  rewrite <- H7 in INCL.
  rewrite ksmallest_card in INCL. omega.
Qed.
