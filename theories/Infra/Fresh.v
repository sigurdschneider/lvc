Require Import CSet Le Arith.Compare_dec.
Require Import Plus Util Map Get LengthEq SafeFirst.

Set Implicit Arguments.

Definition fresh (s : set nat) : nat :=
  S(fold max s 0).

Lemma max_transpose
  : transpose eq max.
Proof.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x).
  rewrite Max.max_assoc. reflexivity.
Qed.

Lemma fresh_spec' (G:set nat)
  : forall (x:nat), x ∈ G -> x <= fold max G 0.
Proof.
  pattern G. pattern (fold max G 0). eapply fold_rec; intros.
  - cset_tac.
  - eapply H1 in H3. destruct H3.
    + pattern (fold max s'' 0). rewrite fold_2; eauto.
      * rewrite H3. pose proof (Max.le_max_l x0 (fold max s' 0)).
        eapply H4.
      * intuition.
      * eapply max_transpose.
    + pattern (fold max s'' 0). rewrite fold_2; eauto.
      * pose proof (Max.le_max_r x (fold max s' 0)).
        specialize (H2 _ H3). unfold max in H2. rewrite <- H4. eapply H2.
      * intuition.
      * eapply max_transpose.
Qed.

Lemma fresh_spec G : fresh G ∉ G.
Proof.
  intro. unfold fresh in H.
  pose proof (fresh_spec' H). omega.
Qed.

Lemma fresh_variable_always_exists (lv:set nat) n
: safe (fun x => x ∉ lv) n.
Proof.
  - decide (n > fold max lv 0).
    + econstructor; intro.
      exploit fresh_spec'; eauto. omega.
    + eapply safe_antitone with (n:=S (fold max lv 0)); [|omega].
      econstructor. intro. exploit fresh_spec'; eauto; omega.
Qed.

Definition least_fresh (lv:set nat) : nat.
  refine (@safe_first (fun x => x ∉ lv) _ 0 _).
  - eapply fresh_variable_always_exists.
Defined.

Lemma all_in_lv_cardinal (lv:set nat) n
: (forall m : nat, m < n -> m \In lv) -> cardinal lv >= n.
Proof.
  general induction n; simpl.
  - omega.
  - exploit (IHn (lv \ singleton n)).
    + intros. cset_tac'; omega.
    + assert (lv [=] {n; lv \ singleton n }). {
        exploit (H (n)); eauto.
        cset_tac.
      }
      rewrite H1.
      assert (n ∉ lv \ singleton n) by cset_tac.
      erewrite cardinal_2; eauto. omega.
Qed.

Lemma neg_pidgeon_hole (lv:set nat)
: (forall m : nat, m <= cardinal lv -> m \In lv) -> False.
Proof.
  intros. exploit (@all_in_lv_cardinal lv (S (cardinal lv))).
  intros; eapply H; eauto. omega. omega.
Qed.

Lemma least_fresh_full_spec G
  : least_fresh G ∉ G
    /\ least_fresh G <= cardinal G
    /\ forall m, m < least_fresh G -> m ∈ G.
Proof.
  unfold least_fresh.
  eapply safe_first_spec with (I:= fun n => le n (cardinal G) /\ forall m, m < n -> m ∈ G).
  - intros; dcr.
    assert (n ∈ G) by cset_tac; clear H0.
    split.
    + eapply all_in_lv_cardinal.
      intros. decide (m = n); subst; eauto.
      eapply H2. omega.
    + intros. decide (m = n); subst; eauto.
      eapply H2; omega.
  - intuition.
  - split; intros; omega.
Qed.

Lemma least_fresh_ext (G G':set nat)
: G [=] G'
  -> least_fresh G = least_fresh G'.
Proof.
  intros. unfold least_fresh.
  eapply safe_first_ext; eauto.
  split; intros.
  - rewrite <- H; eauto.
  - rewrite H; eauto.
Qed.

Lemma least_fresh_spec G
: least_fresh G ∉ G.
Proof.
  eapply least_fresh_full_spec.
Qed.

Lemma least_fresh_small G
: least_fresh G <= cardinal G.
Proof.
  eapply least_fresh_full_spec.
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

Section FreshList.

  Variable fresh : set nat -> nat.

  Fixpoint fresh_list (G:set nat) (n:nat) : list nat :=
    match n with
      | 0 => nil
      | (S n) => let y := fresh G in y::fresh_list {y;G} n
    end.

  Lemma fresh_list_length (G:set nat) n
  : length (fresh_list G n) = n.
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G, fresh G ∉ G.

  Definition fresh_set (G:set nat) L : set nat :=
    of_list (fresh_list G L).

  Lemma fresh_list_spec : forall (G:set nat) n, disj (of_list (fresh_list G n)) G.
  Proof.
    intros. general induction n; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + specialize (H ({fresh G; G})).
        eapply H; eauto.
        cset_tac.
  Qed.

  Lemma fresh_set_spec
  : forall (G:set nat) L, disj (fresh_set G L) G.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_nodup (G: set nat) n
    : NoDupA eq (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_spec.
    eapply InA_in. eapply H.
    cset_tac; eauto.
  Qed.

End FreshList.


Lemma fresh_list_ext n G G' f
  : (forall G G', G [=] G' -> f G = f G')
    -> G [=] G'
    -> fresh_list f G n = fresh_list f G' n.
Proof.
  intros EXT EQ. general induction n; simpl.
  - reflexivity.
  - f_equal; eauto using least_fresh_ext.
    eapply IHn; eauto.
    erewrite EXT, EQ; eauto; reflexivity.
Qed.


Hint Resolve fresh_list_length : len.

Section FreshListStable.

  Variable fresh : set nat -> nat -> nat.

  Fixpoint fresh_list_stable (G:set nat) (xl:list nat) : list nat :=
    match xl with
      | nil => nil
      | x::xl => let y := fresh G x in y::fresh_list_stable {y;G} xl
    end.

  Lemma fresh_list_stable_length (G:set nat) xl
  : length (fresh_list_stable G xl) = length xl.
  Proof.
    general induction xl; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G x, fresh G x ∉ G.

  Definition fresh_set_stable (G:set nat) L : set nat :=
    of_list (fresh_list_stable G L).

  Lemma fresh_list_stable_spec
    : forall (G:set nat) L, disj (of_list (fresh_list_stable G L)) G.
  Proof.
    intros. general induction L; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + specialize (H ({fresh G a; G})).
        eapply H; eauto.
        cset_tac.
  Qed.

  Lemma fresh_set_stable_spec
  : forall (G:set nat) L, disj (fresh_set_stable G L) G.
  Proof.
    unfold fresh_set. eapply fresh_list_stable_spec.
  Qed.

  Lemma fresh_list_stable_nodup (G: set nat) L
    : NoDupA eq (fresh_list_stable G L).
  Proof.
    general induction L; simpl; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_stable_spec.
    eapply InA_in. eapply H.
    cset_tac; eauto.
  Qed.

End FreshListStable.

Lemma fresh_list_stable_ext n G G' f
  : (forall x G G', G [=] G' -> f G x = f G' x)
    -> G [=] G'
    -> fresh_list_stable f G n = fresh_list_stable f G' n.
Proof.
  intros EXT EQ. general induction n; simpl.
  - reflexivity.
  - f_equal; eauto using least_fresh_ext.
    eapply IHn; eauto.
    erewrite EXT, EQ; eauto; reflexivity.
Qed.


Hint Resolve fresh_list_stable_length : len.

Lemma least_fresh_list_small G n
: forall i x, get (fresh_list least_fresh G n) i x -> x < cardinal G + n.
Proof.
  general induction n; simpl in *; isabsurd.
  - inv H.
    + exploit (least_fresh_small G). omega.
    + exploit IHn; eauto.
      erewrite cardinal_2 with (s:=G) in H0. omega.
      eapply (least_fresh_spec). cset_tac.
Qed.

Lemma least_fresh_list_ext n G G'
  : G [=] G'
    -> fresh_list least_fresh G n = fresh_list least_fresh G' n.
Proof.
  intros EQ. general induction n; simpl.
  - reflexivity.
  - f_equal; eauto using least_fresh_ext.
    eapply IHn.
    erewrite least_fresh_ext, EQ; eauto; reflexivity.
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
  eapply least_fresh_list_small; eauto.
Qed.

Lemma nats_up_to_max n m
: nats_up_to (max n m) [=] nats_up_to n ∪ nats_up_to m.
Proof.
  general induction n; simpl.
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

Lemma inverse_on_update_fresh_list (D:set nat) (Z:list nat) (ϱ ϱ' : nat -> nat)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) ((length Z))) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto. intros.
  eapply fresh_list_nodup, fresh_spec. eauto with len.
  eapply fresh_list_spec, fresh_spec.
Qed.

Record StableFresh :=
  {
    stable_fresh :> set nat -> nat -> nat;
    stable_fresh_spec : forall G x, stable_fresh G x ∉ G
  }.

Hint Resolve stable_fresh_spec.