Require Import CSet Le Arith.Compare_dec.
Require Import Plus Util Map Get Take LengthEq SafeFirst.
Require Export PidgeonHole StableFresh OrderedTypeMax.

Set Implicit Arguments.

Section LeastFresh.
  Variable V : Type.
  Context `{NaturalRepresentationSucc V}.
  Context `{@NaturalRepresentationMax V H H0}.

  Definition fresh (s : set V) : V :=
    succ (fold max s (ofNat 0)).

  Lemma max_transpose
    : transpose _eq max.
  Proof.
    hnf; intros.
    rewrite !max_asNat.
    rewrite !asNat_ofNat.
    rewrite Max.max_comm. rewrite <- Max.max_assoc.
    setoid_rewrite Max.max_comm at 2. reflexivity.
  Qed.

  Lemma fold_max_lt (G:set V)
    : forall (x:V), x ∈ G -> _lt x (succ (fold max G (ofNat 0))).
  Proof.
    pattern G. pattern (fold max G (ofNat 0)). eapply fold_rec.
    - cset_tac.
    - intros ? ? ? ? IN NOTIN ADD LT y yIn.
      eapply ADD in yIn. destruct yIn.
      + rewrite fold_2; eauto.
        * rewrite <- H3.
          nr.
          eapply Peano.le_n_S.
          eapply Nat.max_le_iff. left. reflexivity.
        * eapply max_proper.
        * eapply max_transpose.
      + rewrite fold_2; eauto.
        * exploit LT; eauto.
          nr.
          eapply Peano.le_n_S.
          rewrite Nat.max_le_iff. right. omega.
        * eapply max_proper.
        * eapply max_transpose.
  Qed.

  Lemma fresh_spec G : fresh G ∉ G.
  Proof.
    intro A. unfold fresh in A.
    pose proof (fold_max_lt A) as B.
    eapply lt_antirefl in B; eauto.
  Qed.

  Lemma fresh_variable_always_exists (lv:set V) n
    : safe (fun x => x ∉ lv) n.
  Proof.
    - decide (_lt (fold max lv (ofNat 0)) n).
      + econstructor; intro.
        exploit fold_max_lt. cset_tac.
        nr.
        omega.
      + eapply safe_antitone with (n:=succ (fold max lv (ofNat 0))).
        * unfold Proper, respectful. intros. rewrite H3. reflexivity.
        * econstructor. intro. exploit fold_max_lt; eauto.
          cset_tac. nr. omega.
        * nr. omega.
  Qed.

  Definition least_fresh_gen (lv:set V) : V.
    refine (@safe_first _ _ _ _ (fun x => x ∉ lv) _ (ofNat 0) _).
    - eapply fresh_variable_always_exists.
  Defined.

  (*
  Lemma all_in_lv_cardinal (lv:set nat) n
    : (forall m : nat, m < n -> m \In lv) -> cardinal lv >= n.
  Proof.
    general induction n; simpl.
    - omega.
    - exploit (IHn _ _ _ _ _ (lv \ singleton n)).
      + intros. cset_tac'; omega.
      + assert (lv [=] {n; lv \ singleton n }). {
          exploit (H3 (n)); eauto.
          cset_tac.
        }
        rewrite H5.
        assert (n ∉ lv \ singleton n) by cset_tac.
        erewrite cardinal_2; eauto. omega.
  Qed.

  Lemma neg_pidgeon_hole (lv:set nat)
    : (forall m : nat, m <= cardinal lv -> m \In lv) -> False.
  Proof.
    intros. exploit (@all_in_lv_cardinal lv (S (cardinal lv))).
    intros; eapply H; eauto. omega. omega.
  Qed.
   *)

  Lemma least_fresh_full_spec G
    : least_fresh_gen G ∉ G
      /\ asNat (least_fresh_gen G) <= cardinal G
      /\ forall m, _lt m (least_fresh_gen G) -> m ∈ G.
  Proof.
    unfold least_fresh_gen.
    eapply safe_first_spec
      with (I:= fun n => le (asNat n) (cardinal G) /\ forall m, _lt m n -> m ∈ G).
    - intros ? [A B] NOTIN.
      assert (IN:n ∈ G) by cset_tac. clear NOTIN.
      split.
      + eapply all_in_lv_cardinal.
        intros. decide (x === n); try rewrite e in *; eauto; nr.
        eapply B. omega.
      + intros. decide (m === n); try rewrite e in *; eauto; nr.
        eapply B. omega.
    - intuition.
    - split; intros; nr; omega.
  Qed.

  Lemma least_fresh_gen_ext (G G':set V)
    : G [=] G'
      -> least_fresh_gen G = least_fresh_gen G'.
  Proof.
    intros. unfold least_fresh_gen.
    eapply safe_first_ext; eauto.
    split; intros.
    - rewrite <- H3; eauto.
    - rewrite H3; eauto.
  Qed.

End LeastFresh.

Require LeastFresh.


(*
Lemma least_fresh_spec G
: least_fresh G ∉ G.
Proof.
  eapply least_fresh_full_spec.
Qed.

Lemma least_fresh_small (G:set nat)
: least_fresh G <= cardinal G.
Proof.
  unfold least_fresh. simpl.
  eapply LeastFreshNat.least_fresh_full_spec.
Qed.

Lemma least_fresh_smallest G
: forall m, m < least_fresh G -> m ∈ G.
Proof.
  eapply least_fresh_full_spec.
Qed.

Definition fresh_stable (lv:set nat) (x:nat) : nat :=
  if [x ∉ lv] then x else fresh lv.

Lemma fresh_stable_spec G x
      : fresh_stable G x ∉ G.
Proof.
  unfold fresh_stable. cases; eauto using fresh_spec.
Qed.
*)

Section FreshList.
  Variable V : Type.
  Context `{OrderedType V}.
  Variable fresh : set V -> V.

  Fixpoint fresh_list (G:set V) (n:nat) : list V :=
    match n with
      | 0 => nil
      | (S n) => let y := fresh G in y::fresh_list {y;G} n
    end.

  Lemma fresh_list_length (G:set V) n
  : length (fresh_list G n) = n.
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G, fresh G ∉ G.

  Definition fresh_set (G:set V) L : set V :=
    of_list (fresh_list G L).

  Lemma fresh_list_spec : forall (G:set V) n, disj (of_list (fresh_list G n)) G.
  Proof.
    intros. general induction n; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + rewrite <- H2 in H1. eauto.
      + specialize (H0 ({fresh G; G})).
        eapply H0; eauto.
        cset_tac.
  Qed.

  Lemma fresh_set_spec
  : forall (G:set V) L, disj (fresh_set G L) G.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_nodup (G: set V) n
    : NoDupA eq (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_spec.
    eapply InA_eq_of_list; eauto.
    cset_tac.
  Qed.

  Lemma fresh_list_ext n G G'
    : (forall G G', G [=] G' -> fresh G = fresh G')
      -> G [=] G'
      -> fresh_list G n = fresh_list G' n.
  Proof.
    intros EXT EQ. general induction n; simpl.
    - reflexivity.
    - f_equal. eauto.
      eapply IHn; eauto.
      erewrite EXT, EQ; eauto; reflexivity.
  Qed.

End FreshList.

Hint Resolve fresh_list_length : len.

Require Import LeastFresh.

Instance LeastFreshNat : LeastFresh.LeastFresh nat :=
  {
    least_fresh := @least_fresh_gen nat _ NaturalRepresentationNat _ _
  }.
Proof.
  - intros. eapply least_fresh_full_spec.
  - intros. eapply least_fresh_full_spec; eauto.
  - intros. eapply least_fresh_gen_ext; eauto.
Qed.



Lemma least_fresh_list_small X `{LeastFresh X} (G:set X) n
: forall i x, get (fresh_list least_fresh G n) i x -> asNat x < cardinal G + n.
Proof.
  general induction n; simpl in *; isabsurd.
  - invc H2.
    + clear IHn.
      pose proof (least_fresh_least G).
      eapply all_in_lv_cardinal in H2.
      omega.
    + exploit IHn; eauto.
      erewrite cardinal_2 with (s:=G) in H2. omega.
      eapply (least_fresh_spec). cset_tac.
Qed.

Lemma least_fresh_list_ext X `{LeastFresh X}  n (G:set X) G'
  : G [=] G'
    -> fresh_list least_fresh G n = fresh_list least_fresh G' n.
Proof.
  intros.
  eapply fresh_list_ext; eauto.
  eapply least_fresh_spec.
  eapply least_fresh_ext.
Qed.

Fixpoint nats_up_to (n:nat) :=
  match n with
    | S n => {n; nats_up_to n}
    | 0 => ∅
  end.

Lemma in_nats_up_to n m
: n < m -> n ∈ nats_up_to m.
Proof.
  intros. general induction H.
  - simpl. cset_tac; intuition.
  - inv H; simpl in * |- *; cset_tac; intuition.
Qed.

Lemma in_nats_up_to' n m
: n <= m -> n ∈ nats_up_to (m + 1).
Proof.
  intros. eapply in_nats_up_to. omega.
Qed.

Lemma nats_up_to_incl n m
: n <= m -> nats_up_to n ⊆ nats_up_to m.
Proof.
  intros. general induction H; eauto.
  simpl. rewrite IHle. cset_tac; intuition.
Qed.

Lemma least_fresh_list_small_nats_up_to G n
: of_list (fresh_list least_fresh G n) ⊆ nats_up_to (cardinal G + n).
Proof.
  eapply get_in_incl; intros.
  eapply in_nats_up_to.
  eapply least_fresh_list_small in H; eauto.
Qed.

Lemma nats_up_to_max n m
: nats_up_to (max n m) [=] nats_up_to n ∪ nats_up_to m.
Proof.
  general induction n; unfold max; simpl.
  - cset_tac.
  - destruct m; simpl.
    + clear_all; cset_tac.
    + rewrite IHn.
      decide (n < m).
      * rewrite max_r; eauto; try omega.
        assert (n ∈ nats_up_to m); eauto using in_nats_up_to.
        cset_tac.
      * assert (m <= n) by omega.
        rewrite max_l; eauto.
        cset_tac'. exfalso.
        assert (n <> a). intro. eapply n1; subst; eauto.
        idtac "improve".
        exploit (@in_nats_up_to a n); eauto.
        omega.
Qed.

Lemma nats_up_to_in x i
  : x < i <-> x ∈ nats_up_to i.
Proof.
  induction i; simpl.
  - split. omega. cset_tac.
  - decide (x = i); subst.
    + split. cset_tac. omega.
    + split; intros.
      -- cset_tac'. eapply H0. omega.
      -- cset_tac'.
Qed.


(*
Lemma inverse_on_update_fresh_list (D:set nat) (Z:list nat) (ϱ ϱ' : nat -> nat)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) ((length Z))) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto. intros.
  eapply fresh_list_nodup, fresh_spec. eauto with len.
  eapply fresh_list_spec, fresh_spec.
Qed.
 *)
