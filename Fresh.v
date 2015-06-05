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
  pattern (fold max s'' 0). rewrite fold_2; eauto; try intuition.
  pose proof (Max.le_max_r x (fold max s' 0)).
  specialize (H2 _ H3). unfold max in H2. rewrite <- H4. eapply H2.
  hnf; intros. rewrite Max.max_assoc. rewrite (Max.max_comm x1).
  rewrite Max.max_assoc. reflexivity.
Qed.

Lemma fresh_spec G : fresh G ∉ G.
Proof.
  intro. unfold fresh in H.
  pose proof (fresh_spec' H). omega.
Qed.

Section SafeFirst.

  Hypothesis P : nat -> Prop.

  Inductive safe : nat -> Prop :=
  | safe_here n : P n -> safe n
  | safe_after n : safe (S n) -> safe n.

  Lemma safe_antitone m n
  : safe n
    -> m < n
    -> safe m.
  Proof.
    intros. general induction H0; eauto using safe.
  Qed.

  Lemma exists_is_safe
  : (exists x, P x) -> exists n, safe n.
  Proof.
    intros. destruct H; eexists; eauto using safe.
  Qed.

  Hypothesis comp  : forall n, Computable (P n).

  Lemma safe_upward n
  : safe n -> ~ P n -> safe (S n).
  Proof.
    intros; destruct H.
    - destruct (H0 H).
    - eapply H.
  Defined.

  Fixpoint safe_first n (s:safe n) : nat.
  refine (if [ P n ] then n else safe_first (S n) _).
  destruct s; eauto. destruct (_H H).
  Defined.


  Fixpoint safe_first_spec n s
  : P (@safe_first n s).
  Proof.
    unfold safe_first.
    destruct s.
    - simpl. destruct (decision_procedure (P n)); eauto.
    - destruct if; eauto.
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
  destruct PS; destruct QS; simpl.
  - destruct (decision_procedure (P n)), (decision_procedure (Q n)); eauto; intuition.
  - destruct if; destruct (decision_procedure (P n)); eauto; intuition. exfalso; firstorder.
  - destruct if; destruct (decision_procedure (Q n)); eauto; intuition. exfalso; firstorder.
  - repeat destruct if; intuition; exfalso; firstorder.
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

Lemma all_in_lv_cardinal (lv:set nat) n
: (forall m : nat, m < n -> m \In lv) -> cardinal lv >= n.
Proof.
  general induction n; simpl.
  - omega.
  - exploit (IHn (lv \ {{n}})).
    intros. cset_tac; intuition. invc H1. omega.
    assert (lv [=] {n; lv \ {{n}} }).
    exploit (H (n)); eauto.
    cset_tac; intuition. decide (n = a); subst; intuition.
    invc H1; eauto.
    rewrite H0. erewrite cardinal_2; eauto. omega. cset_tac; intuition.
Qed.


Lemma neg_pidgeon_hole (lv:set nat)
: (forall m : nat, m <= cardinal lv -> m \In lv) -> False.
Proof.
  intros. exploit (@all_in_lv_cardinal lv (S (cardinal lv))).
  intros; eapply H; eauto. omega. omega.
Qed.


(* This definition is handy in the folling proof *)
Inductive le (n : nat) : nat -> Prop :=
  le_n : le n n | le_S : forall m : nat, le (S n) m -> le n m.

Lemma le_is_le n m
: le n m <-> n <= m.
Proof.
  split; intros.
  - general induction H; eauto.
    inv H; omega.
  - general induction H; eauto using le.
    inv IHle; eauto using le.
    clear H0 H.
    general induction IHle; eauto using le.
Qed.

Lemma small_fresh_variable_exists (lv:set nat) n
: (forall m, m < n -> m ∈ lv)
  -> le n (cardinal lv)
  -> safe (fun x => x ∉ lv /\ x <= cardinal lv) n.
Proof.
  intros. general induction H0.
  - decide (cardinal lv ∈ lv).
    + exfalso; eapply neg_pidgeon_hole; eauto.
      intros. decide (m = cardinal lv).
      * subst; eauto.
      * eapply H; intros. omega.
    + econstructor 1; eauto.
  - decide (n ∈ lv).
    * exploit (IHle).
      intros. decide (m = n).
      subst; eauto.
      eapply H; eauto. omega. eauto.
      econstructor 2; eauto.
    * econstructor 1. split; eauto.
      eapply le_is_le in H0. omega.
Qed.

Instance le_dec x y : Computable (x <= y).
eapply le_dec.
Defined.

Definition least_fresh (lv:set var) : var.
  refine (@safe_first (fun x => x ∉ lv /\ x <= cardinal lv) _ _ _).
  - intros; eauto. hnf. decide (n ∉ lv /\ n <= cardinal lv); eauto.
  - instantiate (1:=0). eapply small_fresh_variable_exists.
    intros. omega. eapply le_is_le; omega.
Defined.

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

Lemma least_fresh_full_spec G
: least_fresh G ∉ G /\ least_fresh G <= cardinal G.
Proof.
  unfold least_fresh.
  eapply safe_first_spec.
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

Definition fresh_stable (lv:set var) (x:var) : var :=
  if [x ∉ lv] then x else
    fresh lv.

Lemma fresh_stable_spec G x
      : fresh_stable G x ∉ G.
Proof.
  unfold fresh_stable. destruct if; eauto using fresh_spec.
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

  Lemma fresh_list_spec : forall (G:set var) n, (of_list (fresh_list G n)) ∩ G [=] ∅.
  Proof.
    intros. general induction n; simpl; split; intros; try now (cset_tac; intuition).
    - cset_tac; intuition.
      + invc H; eauto.
      + specialize (H0 (G ∪ {{fresh G}})).
        intuition (cset_tac; eauto).
  Qed.

  Lemma fresh_set_spec
  : forall (G:set var) n, (fresh_set G n) ∩ G [=] ∅.
  Proof.
    unfold fresh_set. eapply fresh_list_spec.
  Qed.

  Lemma fresh_list_unique (G: set var) n
    : unique (fresh_list G n).
  Proof.
    general induction n; simpl; eauto.
    split; eauto. intro.
    eapply (not_in_empty (fresh G)).
    eapply fresh_list_spec.
    cset_tac. eapply InA_in; eauto.
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
    erewrite cardinal_2 with (s:=G) in X. omega.
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
  - cset_tac; intuition.
  - destruct m; simpl.
    + cset_tac; intuition.
    + rewrite IHn.
      decide (n < m).
      * rewrite max_r; eauto; try omega.
        assert (n ∈ vars_up_to m); eauto using in_vars_up_to.
        cset_tac; intuition.
        cset_tac; intuition.
      * rewrite max_l; eauto. assert (m <= n) by omega.
        cset_tac; intuition; eauto. cset_tac; intuition.
        decide (n = a); subst; intuition.
        right. left. eapply in_vars_up_to. omega. omega.
Qed.

Lemma inverse_on_update_fresh_list (D:set var) (Z:list var) (ϱ ϱ' : var -> var)
 : inverse_on (D \ of_list Z) ϱ ϱ'
  -> inverse_on D (update_with_list Z (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) ϱ)
                 (update_with_list (fresh_list fresh (lookup_set ϱ (D \ of_list Z)) (length Z)) Z ϱ').
Proof.
  intros. eapply inverse_on_update_fresh; eauto.
  eapply fresh_list_unique, fresh_spec.
  eapply fresh_list_spec, fresh_spec.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
