Require Import Util CSet Fresh.

Set Implicit Arguments.

Record inf_subset :=
  {
    inf_subset_P :> nat -> bool;
    inf_subset_inf : forall x, exists y, inf_subset_P y /\ y > x
  }.

Hint Resolve inf_subset_inf.

Record inf_partition :=
  { part_1 : inf_subset;
    part_2 : inf_subset;
    part_disj : forall x, part_1 x -> part_2 x -> False;
    part_cover : forall x, part_1 x + part_2 x;
  }.

Fixpoint even (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n) => even n
  end.

Lemma even_or_successor x
  : even x \/ even (1 + x).
Proof.
  induction x; eauto.
  destruct IHx; eauto.
Qed.

Definition even_inf_subset : inf_subset.
Proof.
  refine (Build_inf_subset even _).
  - intros. destruct (even_or_successor (S x)); eauto.
    eexists (2+x); simpl; split; eauto.
Defined.

Definition odd := (fun x => negb (even x)).

Lemma even_not_even x
  : even x = negb (even (S x)).
Proof.
  general induction x; eauto.
  - simpl even at 2.
    destruct (even x); destruct (even (S x)); simpl in *; intuition.
Qed.

Definition odd_inf_subset : inf_subset.
Proof.
  refine (Build_inf_subset odd _).
  - unfold odd. intros.
    destruct (even_or_successor x); eauto.
    + eexists (S x). rewrite <- even_not_even.
      split; eauto.
    + eexists (S (S x)); simpl.
      rewrite even_not_even in H. eauto.
Defined.

Definition even_part : inf_partition.
Proof.
  refine (Build_inf_partition even_inf_subset odd_inf_subset _ _).
  - intros.
    unfold even_inf_subset in H. simpl in H.
    unfold odd_inf_subset in H0. simpl in H0.
    unfold odd in H0. unfold negb in H0. cases in H0; eauto.
  - intros.
    unfold even_inf_subset, odd_inf_subset, odd, negb; simpl.
    cases; eauto.
Qed.

Require Import SafeFirst.

Lemma fresh_variable_always_exists_in_inf_subset (lv:set nat) (p:inf_subset) n
: safe (fun x => x ∉ lv /\ p x) n.
Proof.
  - decide (n > SetInterface.fold max lv 0).
    + decide (p n).
      * econstructor. split; eauto.
        intro. exploit fresh_spec'; eauto.
        intros. omega.
      * edestruct (inf_subset_inf p n); dcr.
        eapply (@safe_antitone _ _ x);[|omega].
        econstructor; split; eauto.
        intro. exploit fresh_spec'; eauto. omega.
    + decide (p (S (SetInterface.fold max lv 0))).
      * eapply safe_antitone. instantiate (1:=S (SetInterface.fold max lv 0)).
        econstructor. split; eauto. intro.
        exploit fresh_spec'; eauto. omega.
        omega.
      * edestruct (inf_subset_inf p (S (SetInterface.fold Init.Nat.max lv 0)));
          dcr.
        eapply (@safe_antitone _ _ x);[|omega].
        econstructor; split; eauto.
        intro. exploit fresh_spec'; eauto. omega.
Qed.

Definition least_fresh_P (p:inf_subset) (lv:set nat) : nat.
  refine (@safe_first (fun x => x ∉ lv /\ p x) _ 0 _).
  - eapply fresh_variable_always_exists_in_inf_subset.
Defined.

Lemma least_fresh_P_full_spec p G
  : least_fresh_P p G ∉ G
    /\ (forall m, p m ->  m < least_fresh_P p G -> m ∈ filter p G)
    /\ p (least_fresh_P p G).
Proof.
  unfold least_fresh_P.
  eapply safe_first_spec with
  (I:= fun n => forall m, p m -> m < n -> m ∈ filter p G).
  - intros; dcr. rewrite de_morgan_dec, <- in_dneg in H0.
    destruct H0; dcr.
    + decide (m = n); subst; eauto.
      * cset_tac.
      * exploit (H m); eauto. omega.
    + decide (m = n); subst; eauto.
      * cset_tac.
      * exploit (H m); eauto. omega.
  - intros. cset_tac.
  - intros; omega.
Qed.

Lemma least_fresh_P_ext p (G G' : ⦃nat⦄)
  : G [=] G' -> least_fresh_P p G = least_fresh_P p G'.
Proof.
  intros. unfold least_fresh_P; eauto.
  eapply safe_first_ext. intros. rewrite H. reflexivity.
Qed.

Definition stable_fresh_P (isub:inf_subset) : StableFresh.
  refine (Build_StableFresh (fun lv _ => least_fresh_P isub lv) _ _).
  - intros. eapply least_fresh_P_full_spec.
  - intros. eapply least_fresh_P_ext; eauto.
Defined.

Lemma semantic_branch (P Q:Prop) `{Computable Q}
  : P \/ Q -> ((~ Q /\ P) \/ Q).
Proof.
  decide Q; clear H; intros; intuition.
Qed.

Definition least_fresh_part (p:inf_partition) (G:set nat) x :=
  if part_1 p x then least_fresh_P (part_1 p) G
  else least_fresh_P (part_2 p) G.

Lemma least_fresh_part_fresh p G x
  : least_fresh_part p G x ∉ G.
Proof.
  unfold least_fresh_part; cases; eauto.
  - eapply least_fresh_P_full_spec.
  - eapply least_fresh_P_full_spec.
Qed.

Lemma least_fresh_part_1 (p:inf_partition) G x
  : part_1 p x
    -> part_1 p (least_fresh_part p G x).
Proof.
  unfold least_fresh_part; intros; cases.
  eapply least_fresh_P_full_spec.
Qed.

Lemma least_fresh_part_2 (p:inf_partition) G x
  : part_2 p x
    -> part_2 p (least_fresh_part p G x).
Proof.
  unfold least_fresh_part; intros. cases.
  - exfalso. eapply part_disj; eauto.
  - eapply least_fresh_P_full_spec.
Qed.

Lemma least_fresh_part_ext p (G G' : ⦃nat⦄) x
  : G [=] G' -> least_fresh_part p G x = least_fresh_part p G' x.
Proof.
  intros. unfold least_fresh_part; cases; eauto using least_fresh_P_ext.
Qed.

Definition stable_fresh_part (p:inf_partition) : StableFresh.
  refine (Build_StableFresh (least_fresh_part p) _ _).
  - intros. eapply least_fresh_part_fresh.
  - intros. eapply least_fresh_part_ext; eauto.
Defined.

Lemma least_fresh_list_part_ext p n G G'
  : G [=] G'
    -> fresh_list_stable (stable_fresh_part p) G n = fresh_list_stable (stable_fresh_part p) G' n.
Proof.
  eapply fresh_list_stable_ext.
  intros. eapply least_fresh_part_ext; eauto.
Qed.

Lemma fresh_list_stable_P_ext p G L L'
  : ❬L❭ = ❬L'❭
    -> of_list (fresh_list_stable (stable_fresh_P p) G L)
              ⊆ of_list (fresh_list_stable (stable_fresh_P p) G L').
Proof.
  intros. hnf; intros ? In.
  general induction H; simpl in *; eauto.
  - cset_tac.
Qed.

Lemma fresh_list_stable_P_ext_eq p G L L'
  : ❬L❭ = ❬L'❭
    -> of_list (fresh_list_stable (stable_fresh_P p) G L)
              [=] of_list (fresh_list_stable (stable_fresh_P p) G L').
Proof.
  split; intros.
  - eapply fresh_list_stable_P_ext; eauto.
  - eapply fresh_list_stable_P_ext; [symmetry|]; eauto.
Qed.
