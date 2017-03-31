Require Import List Map Env AllInRel Exp MoreList.
Require Import Take TakeSet.

Set Implicit Arguments.

(* pick *)

Definition pick (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) : ⦃X⦄
  := s ∪ set_take (k - cardinal s) (t \ s)
.

Lemma incl_pick (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  s ⊆ pick k s t
.
Proof.
  unfold pick. cset_tac.
Qed.

Lemma pick_incl (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  pick k s t ⊆ s ∪ t
.
Proof.
  unfold pick. rewrite set_take_incl. cset_tac.
Qed.

Lemma pick_card (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  k <= cardinal (s ∪ t)
  -> k <= cardinal (pick k s t)
.
Proof.
  intros card. unfold pick. rewrite union_cardinal.
  - unfold set_take. rewrite cardinal_of_list_nodup; [|apply take_dupFree].
    assert (s ∪ t [=] s ∪ t \ s) as seteq by cset_tac.
    rewrite seteq in card. rewrite union_cardinal in card; [|clear;cset_tac].
    rewrite take_length_le; eauto.
    + omega.
    + rewrite elements_length. omega.
  - intros. rewrite set_take_incl. cset_tac.
Qed.

Lemma pick_card' (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  cardinal s <= k -> cardinal (pick k s t) <= k
.
Proof.
  intros card. unfold pick. rewrite union_cardinal.
  - unfold set_take.  rewrite cardinal_of_list_nodup; [|apply take_dupFree].
    decide (k - cardinal s <= cardinal (t \ s)).
    + rewrite take_length_le; eauto.
      * omega.
      * rewrite elements_length. eauto.
    + rewrite take_length_ge; eauto.
      * rewrite elements_length. omega.
      * rewrite elements_length. omega.
  - intros. rewrite set_take_incl. cset_tac.
Qed.
  

Lemma pick_eq (X:Type) `{OrderedType X} k (s t : ⦃X⦄)
  : cardinal s + cardinal (t \ s) <= k -> pick k s t [=] s ∪ t
.
Proof.
  intros card. apply incl_eq; [|apply pick_incl].
  unfold pick. unfold set_take.
  rewrite take_eq_ge.
  - rewrite of_list_elements. cset_tac.
  - rewrite elements_length. unfold ">=". apply Nat.le_add_le_sub_r.
    omega.
Qed.


Lemma pick_eq' (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) :
  k <= cardinal s
  -> pick k s t [=] s
.
Proof.
  intros card. unfold pick. replace (k - cardinal s) with 0 by omega.
  cbn. clear; cset_tac.
Qed.


(* pick_kill *)
             
Definition pick_kill (X:Type) `{OrderedType X} (k:nat) (s t u v : ⦃X⦄) : ⦃X⦄
  := pick (cardinal s + cardinal t - k) ((s \ (u ∪ v)) ∪ (s ∩ t)) (s ∩ v \ u)
.

Lemma incl_pick_kill (X:Type) `{OrderedType X} (k:nat) (s t u v : ⦃X⦄) :
  ((s \ (u ∪ v)) ∪ (s ∩ t)) ⊆ pick_kill k s t u v
.
Proof.
  eapply incl_pick.
Qed.


Lemma pick_kill_incl (X:Type) `{OrderedType X} (k : nat) (s t u v : ⦃X⦄) :
  pick_kill k s t u v ⊆ (s ∩ t) ∪ (s \ u)
.
Proof.
  unfold pick_kill. rewrite pick_incl. cset_tac.
Qed.

Lemma pick_kill_card (X:Type) `{OrderedType X} (k : nat) (s t u v : ⦃X⦄) :
  cardinal (s ∩ u \ t) + cardinal t <= k
  -> cardinal s + cardinal t - k <= cardinal (pick_kill k s t u v)
.
Proof.
  intros card.
  assert (s ∩ u \ t [=] s \ (((s \ (u ∪ v)) ∪ (s ∩ t)) ∪ (s ∩ v \ u))) as seteq by cset_tac.
  rewrite seteq in card. rewrite cardinal_difference' in card; [|clear;cset_tac].
  eapply pick_card. omega.
Qed.


Lemma pick_kill_eq (X:Type) `{OrderedType X} (k:nat) (s t u v : ⦃X⦄) :
  let w := s \ (u ∪ v) ∪ (s ∩ t) in 
  cardinal (s \ w ∪ t) <= k
  -> pick_kill k s t u v [=] s \ (u ∪ v) ∪ (s ∩ t)
.
Proof.
  intros w card. subst w.
  rewrite union_cardinal in card; [|clear;cset_tac].
  unfold pick_kill. apply pick_eq'.
  assert (forall l m n o : nat, (l - o) + m <= n -> l + m - n <= o) as nateq by (intros;omega).
  apply nateq. rewrite <-cardinal_difference'; [|clear;intros;intro N;cset_tac].
  eauto.
Qed.

(* pick_killx *)

Definition pick_killx (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) : ⦃X⦄
  := pick (S (cardinal s) - k) (s \ t) (s ∩ t)
.

Lemma incl_pick_killx (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) :
  s \ t ⊆ pick_killx k s t
.
Proof.
  eapply incl_pick.
Qed.

Lemma pick_killx_incl (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) :
  pick_killx k s t ⊆ s
.
Proof.
  unfold pick_killx. rewrite pick_incl. clear;cset_tac.
Qed.

Lemma pick_killx_card (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) :
  S (cardinal s) - k <= cardinal (s \t ∪ (s ∩ t))
  -> S (cardinal s) - k  <= cardinal (pick_killx k s t)
.
Proof.
  intros card.
  unfold pick_killx. rewrite <-pick_card; eauto.
Qed.

Lemma pick_killx_eq (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄) :
  S (cardinal s) - k <= cardinal (s \ t)
  -> pick_killx k s t [=] (s \ t)
.
Proof.
  apply pick_eq'.
Qed.


(* pick_load *)

Definition pick_load (X:Type) `{OrderedType X} (k:nat)  (r m sp l fv : ⦃X⦄) : ⦃X⦄
  := let l' := l ∩ (sp ∩ r ∪ m) in
     (fv ∩ r ∩ l') ∪ pick (k - cardinal (fv ∩ r)) (fv \ r) (l' \ (fv ∩ r))
.


Lemma incl_pick_load (X:Type) `{OrderedType X} (k:nat)  (r m sp l fv : ⦃X⦄) :
  fv ∩ r ∩ (l ∩ (sp ∩ r ∪ m)) ∪ fv \ r ⊆ pick_load k r m sp l fv
.
Proof.
  unfold pick_load. rewrite <-incl_pick. reflexivity.
Qed.

Lemma pick_load_eq (X:Type) `{OrderedType X} (k:nat)  (r m sp l fv : ⦃X⦄) :
  sp ⊆ r
  -> l ⊆ sp ∪ m
  -> fv \ r ⊆ l
  -> cardinal (fv ∪ l) <= k
  -> pick_load k r m sp l fv [=] l
.
Proof.
  intros spr lspm fvrl card.
  assert (sp ∩ r [=] sp) as speq by (apply inter_subset_equal; eauto).
  assert (l ∩ (sp ∩ r ∪ m) [=] l) as leq
      by (apply inter_subset_equal in lspm; rewrite speq, lspm; eauto).
  unfold pick_load.
  rewrite pick_eq.
  - rewrite leq. clear - fvrl. cset_tac.
  - rewrite leq. rewrite <-union_cardinal.
    + apply Nat.le_add_le_sub_r.
      rewrite <-union_cardinal.
      * rewrite subset_cardinal; eauto. clear; cset_tac.
      * clear. intros. intro N. cset_tac.
    + clear. intros. intro N. cset_tac.
Qed.
      
     

(*
Lemma pick_load_card (X:Type) `{OrderedType X} (k:nat) (r m sp l fv : ⦃X⦄) :
  cardinal (pick_load k r m sp l fv) <= k
.
                                                                              
  *)         


Lemma pick_load_incl (X:Type) `{OrderedType X} (k:nat) (r m sp l fv : ⦃X⦄) :
  pick_load k r m sp l fv ⊆ (sp ∩ r) ∪ m ∪ (fv \ r)
.
Proof.
  unfold pick_load. rewrite pick_incl. cset_tac.
Qed.

Lemma pick_load_card (X:Type) `{OrderedType X} (k:nat) (r m sp l fv : ⦃X⦄) :
  cardinal fv <= k -> cardinal (pick_load k r m sp l fv) <= k - cardinal (fv ∩ r \ (l ∩ (sp ∪ m)))
.
Proof.
  assert (fv ∩ r \ (l ∩ (sp ∪ m)) [=] (fv ∩ r) \ (l ∩ (sp ∩ r ∪ m))) as seteq by (clear; cset_tac).
  intros card. unfold pick_load. rewrite union_cardinal.
  - rewrite pick_card'; eauto. 
    + apply Nat.le_add_le_sub_r. setoid_rewrite plus_comm at 2. rewrite <-plus_assoc.
      rewrite seteq.
      rewrite <-union_cardinal; [|clear;intros;intro N;cset_tac].
      setoid_rewrite <-set_decomp with (s:=fv ∩ r).
      assert (cardinal (fv ∩ r) <= k).
      { rewrite subset_cardinal; eauto. clear;cset_tac. }
      omega.
    + apply Nat.le_add_le_sub_r. rewrite <-union_cardinal; [|clear;cset_tac].
      rewrite union_comm, <-set_decomp. eauto.
  - clear. intros. intro N. dcr. rewrite pick_incl in H1. cset_tac. 
Qed.

  