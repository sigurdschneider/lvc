Require Import CSet Le Arith.Compare_dec.
Require Import Plus Util Map Get Take LengthEq SafeFirst.
Require Export StableFresh Fresh Range InfinitePartition.

Set Implicit Arguments.

Inductive FreshGen (Fi : Type) :=
  {
    fresh :> Fi -> nat -> nat * Fi;
    fresh_list : Fi -> list nat -> list nat * Fi;
    domain : Fi -> set nat;
    domain_add : Fi -> set nat -> Fi
  }.

Inductive FreshGenSpec Fi (FG:FreshGen Fi) : Prop :=
  {
    fresh_spec : forall i x, fst (fresh FG i x) ∉ domain FG i;
    fresh_domain_spec : forall i x, {fst (fresh FG i x); (domain FG i)}
                                 ⊆ domain FG (snd (fresh FG i x));
    fresh_list_disj : forall i Z, disj (domain FG i) (of_list (fst (fresh_list FG i Z)));
    fresh_list_domain_spec : forall i Z, of_list (fst (fresh_list FG i Z)) ∪ domain FG i
                                            ⊆ domain FG (snd (fresh_list FG i Z));
    fresh_list_nodup : forall i Z, NoDupA eq (fst (fresh_list FG i Z));
    fresh_list_len : forall i Z, ❬fst (fresh_list FG i Z)❭ = ❬Z❭;
    domain_add_spec : forall i G, G ∪ domain FG i ⊆ domain FG (domain_add FG i G)
  }.

Create HintDb fresh discriminated.


Definition FG_fast : FreshGen nat :=
  @Build_FreshGen nat
                  (fun n _ => (n, S n))
                  (fun n Z => (range n ❬Z❭, n + ❬Z❭))
                  nats_up_to
                  (fun n s => max n (S (fold Init.Nat.max s 0))).


Lemma FGS_fast : FreshGenSpec FG_fast.
  econstructor; simpl.
  - intros. rewrite <- nats_up_to_in. omega.
  - reflexivity.
  - intros; hnf; intros.
    eapply nats_up_to_in in H.
    eapply in_range_x in H0 as [? ?]. omega.
  - intros. cset_tac'.
    + rewrite <- nats_up_to_in in *.
      eapply in_range_x in H0. omega.
    + rewrite <- nats_up_to_in in *. omega.
  - intros. eapply range_nodup.
  - eauto with len.
  - simpl. cset_tac'.
    eapply nats_up_to_in.
    + rewrite <- Max.le_max_r.
      eapply fresh_spec' in H0. omega.
    + eapply nats_up_to_in in H0.
      eapply nats_up_to_in.
      rewrite <- Max.le_max_l. eauto.
Qed.

Definition next_even (n:nat) := if [even n] then n else S n.

Lemma next_even_even n
  : even (next_even n).
Proof.
  unfold next_even; cases; eauto.
  edestruct (even_or_successor n); eauto.
Qed.

Lemma even_add x y
  : even x
    -> even y
    -> even (x + y).
Proof.
  revert y. pattern x.
  eapply size_induction with (f:=id); intros.
  destruct x0; simpl; eauto.
  destruct x0; simpl; eauto.
  eapply H; eauto. unfold id. omega.
Qed.

Lemma even_max x y
  : even x
    -> even y
    -> even (max x y).
Proof.
  intros.
  decide (x < y).
  - rewrite max_r; try omega; eauto.
  - rewrite max_l; try omega; eauto.
Qed.

Lemma even_mult2 x
  : even (2 * x).
Proof.
  pattern x.
  eapply size_induction with (f:=id); intros.
  destruct x0; simpl; eauto.
  destruct x0; simpl; eauto. rewrite plus_comm. simpl.
  rewrite <- plus_assoc. simpl.
  exploit (H x0).
  - unfold id. omega.
  - simpl in H0. setoid_rewrite plus_comm in H0 at 2. simpl in *. eauto.
Qed.

Definition FG_even_fast : FreshGen {n | even n}.
  refine
    (@Build_FreshGen {n | even n}
                  (fun n _ => (proj1_sig n, exist _ (S (S (proj1_sig n))) _))
                  (fun n Z => let z := 2 * ❬Z❭ in
                     (plus (proj1_sig n) ⊝ mult 2 ⊝ range 0 ❬Z❭, exist _ (proj1_sig n + z) _))
                  (fun n => nats_up_to (proj1_sig n))
                  (fun n s =>
                     exist _ (max (proj1_sig n) (next_even (S (fold Init.Nat.max s 0)))) _)).
  - simpl. destruct n. eauto.
  - destruct n. subst z.
    eapply even_add; eauto.
    eapply even_mult2.
  - destruct n. eapply even_max; eauto using next_even_even.
Defined.

Lemma NoDup_inj A `{OrderedType A} B `{OrderedType B} (L:list A) (f:A -> B)
      `{Proper _ (_eq ==> _eq) f}
  : NoDupA _eq L
    -> injective_on (of_list L) f
    -> NoDupA _eq (f ⊝ L).
Proof.
  intros ND INJ.
  general induction ND; simpl in *; eauto using NoDupA.
  econstructor; eauto using injective_on_incl with cset.
  intro. eapply InA_in in H3.
  eapply H0. eapply of_list_map in H3; eauto. cset_tac'.
  eapply INJ in H4; eauto with cset.
Qed.

Lemma FGS_even_fast : FreshGenSpec FG_even_fast.
  econstructor; simpl.
  - intros. rewrite <- nats_up_to_in. omega.
  - intros [] _; simpl. cset_tac.
  - intros; hnf; intros.
    eapply nats_up_to_in in H.
    eapply of_list_map in H0; eauto.
    cset_tac'.
    eapply of_list_map in H0; eauto.
    cset_tac'.
    eapply in_range_x in H0 as [? ?]. omega.
  - intros. cset_tac'.
    + eapply of_list_map in H0; eauto. cset_tac'.
      eapply of_list_map in H; eauto. cset_tac'.
      eapply in_range_x in H as [? ?].
      rewrite <- nats_up_to_in in *. simpl in *. omega.
    + rewrite <- nats_up_to_in in *. omega.
  - intros. rewrite map_map.
    exploit (@NoDup_inj nat _ nat _ (range 0 ❬Z❭)); swap 1 4.
    eapply H.
    eapply range_nodup.
    hnf; intros. invc H1. hnf. omega.
    eauto.
  - eauto with len.
  - simpl. cset_tac'.
    eapply nats_up_to_in.
    + rewrite <- Max.le_max_r. unfold next_even.
      simpl in *.
      eapply fresh_spec' in H0.
      cases; eauto. omega. omega.
    + eapply nats_up_to_in in H0.
      eapply nats_up_to_in.
      rewrite <- Max.le_max_l. eauto.
Qed.
