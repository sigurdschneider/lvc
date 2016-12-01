Require Import CSet Le Arith.Compare_dec.

Require Import Plus Util Map Var Get.


Set Implicit Arguments.

Definition fresh (s : set var) : var :=
  S(fold max s 0).

Lemma fresh_spec' (G:set var)
  : forall (x:var), x ∈ G -> x <= fold max G 0.
Proof.
  pattern G. pattern (fold max G 0). eapply fold_rec; intros.
  fsetdec.
  eapply H1 in H3. destruct H3.
  pattern (fold max s'' 0). rewrite fold_2; eauto.
  rewrite H3. pose proof (Max.le_max_l x0 (fold max s' 0)).
  eapply H4.
  intuition.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x1).
  rewrite Max.max_assoc. reflexivity.
  pattern (fold max s'' 0). rewrite fold_2; eauto.
  pose proof (Max.le_max_r x (fold max s' 0)).
  specialize (H2 _ H3). unfold max in H2. rewrite <- H4. eapply H2.
  clear_all; intuition.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x1).
  rewrite Max.max_assoc. reflexivity.
Qed.

Lemma fresh_spec G : fresh G ∉ G.
Proof.
  intro. unfold fresh in H.
  pose proof (fresh_spec' H). omega.
Qed.

Section SafeFirst.

  Hypothesis Q : nat -> Prop.
  Inductive safe : nat -> Prop :=
  | safe_here n : Q n -> safe n
  | safe_after n : safe (S n) -> safe n.

  Lemma safe_antitone m n
  : safe n
    -> m < n
    -> safe m.
  Proof.
    intros. general induction H0; eauto using safe.
  Qed.

  Lemma exists_is_safe
  : (exists x, Q x) -> exists n, safe n.
  Proof.
    intros. destruct H; eexists; eauto using safe.
  Qed.

  Hypothesis comp  : forall n, Computable (Q n).

  Lemma safe_upward n
  : safe n -> ~ Q n -> safe (S n).
  Proof.
    intros; destruct H.
    - destruct (H0 H).
    - eapply H.
  Defined.

  Fixpoint safe_first n (s:safe n) : nat.
  refine (if [ Q n ] then n else safe_first (S n) _).
  destruct s; eauto. destruct (n0 H).
  Defined.

  Hypothesis P : nat -> Prop.
  Hypothesis I : nat -> Prop.
  Hypothesis PQ : forall n, P n -> Q n.
  Hypothesis Step : forall n, I n -> ~ Q n -> I (S n).
  Hypothesis Final : forall n , I n -> Q n -> P n.

  Fixpoint safe_first_spec n s
    : I n -> P (@safe_first n s).
  Proof.
    unfold safe_first.
    destruct s.
    - simpl. destruct (decision_procedure (Q n)); eauto.
    - cases; eauto.
  Qed.

End SafeFirst.

Fixpoint safe_first_ext P Q n
      (PC:forall n, Computable (P n))
      (QC:forall n, Computable (Q n))
      (PS:safe P n)
      (QS:safe Q n)
      (EXT:(forall x, P x <-> Q x)) {struct PS}
: safe_first PC PS = safe_first QC QS.
Proof.
  destruct PS; destruct QS; simpl; repeat cases; eauto;
  exfalso; firstorder.
Qed.

Lemma safe_impl (P Q: nat -> Prop) n
: safe P n -> (forall x, P x -> Q x) -> safe Q n.
Proof.
  intros. general induction H; eauto using safe.
Qed.

Lemma fresh_variable_always_exists (lv:set nat) n
: safe (fun x => x ∉ lv) n.
Proof.
  - decide (n > fold max lv 0).
    + econstructor; intro.
      exploit fresh_spec'; eauto. unfold var in *.
      omega.
    + eapply safe_antitone. instantiate (1:=S (fold max lv 0)).
      econstructor. intro.
      exploit fresh_spec'; eauto. unfold var in *. omega.
      omega.
Qed.

Definition least_fresh (lv:set var) : var.
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
: least_fresh G ∉ G /\ least_fresh G <= cardinal G /\ forall m, m < least_fresh G -> m ∈ G.
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

Lemma least_fresh_ext (G G':set var)
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

Definition fresh_stable (lv:set var) (x:var) : var :=
  if [x ∉ lv] then x else
    fresh lv.

Lemma fresh_stable_spec G x
      : fresh_stable G x ∉ G.
Proof.
  unfold fresh_stable. cases; eauto using fresh_spec.
Qed.

Section FreshList.

  Variable fresh : set var -> var.

  Fixpoint fresh_list (G:set var) (n:nat) : list var :=
    match n with
      | 0 => nil
      | S n => let x := fresh G in x::fresh_list (G ∪ {{x}}) n
    end.

  Lemma fresh_list_length (G:set var) n
  : length (fresh_list G n) = n.
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Lemma fresh_list_length2 (G:set var) n
  : n = length (fresh_list G n).
  Proof.
    general induction n; eauto. simpl. f_equal; eauto.
  Qed.

  Hypothesis fresh_spec : forall G, fresh G ∉ G.

  Definition fresh_set (G:set var) (n:nat) : set var :=
    of_list (fresh_list G n).

  Lemma fresh_list_spec : forall (G:set var) n, disj (of_list (fresh_list G n)) G.
  Proof.
    intros. general induction n; simpl; intros; eauto.
    - hnf; intros. cset_tac'.
      + specialize (H (G ∪ {{fresh G}})).
        eapply H; eauto.
        intuition (cset_tac; eauto).
  Qed.

  Lemma fresh_set_spec
  : forall (G:set var) n, disj (fresh_set G n) G.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_nodup (G: set var) n
    : NoDupA eq (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    econstructor; eauto. intro.
    eapply fresh_list_spec.
    eapply InA_in. eapply H.
    cset_tac; eauto.
  Qed.
End FreshList.

Hint Resolve fresh_list_length fresh_list_length2.

Lemma least_fresh_list_small G n
: forall i x, get (fresh_list least_fresh G n) i x -> x < cardinal G + n.
Proof.
  general induction n; simpl in *; isabsurd.
  - inv H. exploit (least_fresh_small G). omega.
    exploit IHn; eauto.
    erewrite cardinal_2 with (s:=G) in H0. omega.
    eapply least_fresh_spec.
    hnf; cset_tac; intuition.
Qed.

Lemma least_fresh_list_ext n G G'
: G [=] G'
  -> fresh_list least_fresh G n = fresh_list least_fresh G' n.
Proof.
  intros. general induction n; simpl; eauto.
  f_equal; eauto using least_fresh_ext.
  erewrite least_fresh_ext; eauto. eapply IHn.
  rewrite H; eauto.
Qed.

Fixpoint vars_up_to (n:nat) :=
  match n with
    | S n => {n; vars_up_to n}
    | 0 => ∅
  end.

Lemma in_vars_up_to n m
: n < m -> n ∈ vars_up_to m.
Proof.
  intros. general induction H.
  - simpl. cset_tac; intuition.
  - inv H; simpl in * |- *; cset_tac; intuition.
Qed.

Lemma in_vars_up_to' n m
: n <= m -> n ∈ vars_up_to (m + 1).
Proof.
  intros. eapply in_vars_up_to. omega.
Qed.

Lemma vars_up_to_incl n m
: n <= m -> vars_up_to n ⊆ vars_up_to m.
Proof.
  intros. general induction H; eauto.
  simpl. rewrite IHle. cset_tac; intuition.
Qed.

Lemma least_fresh_list_small_vars_up_to G n
: of_list (fresh_list least_fresh G n) ⊆ vars_up_to (cardinal G + n).
Proof.
  eapply get_in_incl; intros.
  eapply in_vars_up_to.
  eapply least_fresh_list_small; eauto.
Qed.

Lemma vars_up_to_max n m
: vars_up_to (max n m) [=] vars_up_to n ∪ vars_up_to m.
Proof.
  general induction n; simpl.
  - cset_tac.
  - destruct m; simpl.
    + clear_all; cset_tac.
    + rewrite IHn.
      decide (n < m).
      * rewrite max_r; eauto; try omega.
        assert (n ∈ vars_up_to m); eauto using in_vars_up_to.
        cset_tac.
      * assert (m <= n) by omega.
        rewrite max_l; eauto.
        cset_tac'. exfalso.
        assert (n <> a). intro. eapply n1; subst; eauto.
        idtac "improve".
        exploit (@in_vars_up_to a n); eauto.
        omega.
Qed.

Lemma inverse_on_update_fresh_list (D:set var) (Z:list var) (ϱ ϱ' : var -> var)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto. intros.
  eapply fresh_list_nodup, fresh_spec.
  eapply fresh_list_spec, fresh_spec.
Qed.
