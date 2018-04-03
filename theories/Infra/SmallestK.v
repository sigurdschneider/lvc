Require Import CSet OrderedTypeComputable OrderedTypeLe InfiniteSubset InfinitePartition StableFresh.

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
  : forall y, InA _eq y (nextk p n x) -> _le x y.
Proof.
  intros.
  general induction H0; destruct n; simpl in *; clear_trivial_eqs; eauto.
  - rewrite H0; reflexivity.
  - revert H0. destr_sig; dcr; eauto. simpl in *. dcr.
    exploit IHInA; eauto.
    intros.
    rewrite H2, H1. reflexivity.
Qed.

Lemma nextk_nodup X `{OrderedType X} (p:inf_subset X) n x
  : NoDupA _eq (nextk p n x).
Proof.
  general induction n; simpl; eauto using NoDupA.
  econstructor; eauto.
  intro. eapply nextk_lt in H0. revert H0. destr_sig.
  intro. dcr.
  rewrite <- H0 in H3. eauto.
Qed.

Lemma ksmallest_card X `{OrderedType X} (p:inf_subset X) k
  : SetInterface.cardinal (of_list (ksmallest p k)) = k.
Proof.
  rewrite cardinal_of_list_nodup; eauto using nextk_nodup, nextk_length.
Qed.

Lemma nextk_greater X `{OrderedType X} (p:inf_subset X) k x z
      (NOTIN:x ∉ of_list (nextk p k z))
      (GR: _le z x) (P:p z) (P':p x)
  : forall y : X, y \In of_list (nextk p k z) -> _lt y x.
Proof.
  general induction k; simpl in *.
  - cset_tac.
  - revert H0. destr_sig. simpl in *; intros. dcr.
    assert (_le x0 x). {
      destruct GR as [GR|GR].
      - decide (_lt x x0); eauto.
        + exploit H4. eapply P'. eauto. destruct H2.
          * exfalso. rewrite H2 in GR. eauto.
          * rewrite H2 in GR. eauto.
        + decide (x0 === x); eauto.
          rewrite e; reflexivity.
          left. eapply le_neq. eapply n. cset_tac.
      - rewrite GR in *. cset_tac.
    }
    cset_tac'. rewrite H7 in *.
    destruct GR; eauto. exfalso; eauto.
Qed.

Lemma least_fresh_part_bounded X
      `{OrderedType X}
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
      edestruct (H5 x); eauto.
    - destr_sig; eauto.
    - split; eauto.
      eapply InA_in in H1.
      eapply nextk_p in H1. eauto. destr_sig; dcr; eauto.
  }
  assert (of_list (ksmallest p k) ⊆ filter p lv). {
    hnf; intros.
    eapply H1 in H4. eapply H2; eauto.
  }
  rewrite <- H4 in INCL.
  rewrite ksmallest_card in INCL. omega.
Qed.


Lemma least_fresh_part_small1 X `{OrderedType X} p o G x k
  : (part_1 p) (least_fresh_part p o G x)
    -> SetInterface.cardinal (filter (part_1 p) G) < k
    -> least_fresh_part p o G x \In of_list (ksmallest (part_1 p) k).
Proof.
  unfold least_fresh_part in *. cases.
  + intros.
    eapply least_fresh_part_bounded; eauto.
  + intros.
    pose proof (least_fresh_P_p (part_2 p) G).
    exfalso.
    unfold least_fresh_P_oracle in H0. cases in H0; dcr.
    eapply (part_disj p _ H0 H3).
    eapply (part_disj p _ H0 H2).
Qed.

Definition part_vars_bounded (p:inf_subset positive) k (x:positive) := p x -> (x ∈ of_list (ksmallest p k)).

Definition part_size_bounded X `{OrderedType X} (p:inf_subset X) k a :=
  SetInterface.cardinal (filter p a) <= k.

Lemma fresh_list_stable_small (p:inf_partition positive) o G k Z (ND:NoDupA eq Z)
  (BNDk : SetInterface.cardinal (filter (part_1 p) G) +
       SetInterface.cardinal (filter (part_1 p) (of_list Z)) <= k)
  : For_all (part_vars_bounded (part_1 p) k)
            (of_list (fst (fresh_list_stable (stable_fresh_part p o) G Z))).
Proof.
  hnf; intros.
  eapply of_list_get_first in H; eauto; dcr. invc H1.
  edestruct fresh_list_stable_get; eauto; dcr. subst.
  hnf; simpl. intros.
  eapply least_fresh_part_small1.
  --- eauto.
  --- rewrite <- BNDk.
      rewrite filter_union; eauto.
      rewrite union_cardinal_le; eauto.
      rewrite plus_comm.
      eapply plus_lt_compat_l.
      eapply cardinal_smaller; eauto.
      eapply least_fresh_part_p1. eauto.
Qed.
