Require Import List Map Env AllInRel Exp MoreList.
Require Import Take TakeSet.

Set Implicit Arguments.

(* pick_kill' *)

Definition pick_kill' (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) : ⦃X⦄
  := s ∪ set_take (k - cardinal s) (t \ s)
.

Lemma incl_pick_kill' (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  s ⊆ pick_kill' k s t
.
Proof.
  unfold pick_kill'. cset_tac.
Qed.

Lemma pick_kill'_incl (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  pick_kill' k s t ⊆ s ∪ t
.
Proof.
  unfold pick_kill'. rewrite set_take_incl. cset_tac.
Qed.

Lemma pick_kill'_card (X:Type) `{OrderedType X} (k : nat) (s t : ⦃X⦄) :
  k <= cardinal (s ∪ t)
  -> k <= cardinal (pick_kill' k s t)
.
Proof.
  intros card. unfold pick_kill'. rewrite union_cardinal.
  - unfold set_take. rewrite cardinal_of_list_nodup; [|apply take_dupFree].
    assert (s ∪ t [=] s ∪ t \ s) as seteq by cset_tac.
    rewrite seteq in card. rewrite union_cardinal in card; [|clear;cset_tac].
    rewrite take_length_le; eauto.
    + omega.
    + rewrite elements_length. omega.
  - intros. rewrite set_take_incl. cset_tac.
Qed.


(* pick_kill *)
             
Definition pick_kill (X:Type) `{OrderedType X} (k:nat) (s t u v : ⦃X⦄) : ⦃X⦄
  := pick_kill' (cardinal s + cardinal t - k) ((s \ (u ∪ v)) ∪ (s ∩ t)) (s ∩ v \ u)
.

Lemma incl_pick_kill (X:Type) `{OrderedType X} (k:nat) (s t u v : ⦃X⦄) :
  ((s \ (u ∪ v)) ∪ (s ∩ t)) ⊆ pick_kill k s t u v
.
Proof.
  eapply incl_pick_kill'.
Qed.


Lemma pick_kill_incl (X:Type) `{OrderedType X} (k : nat) (s t u v : ⦃X⦄) :
  pick_kill k s t u v ⊆ (s ∪ v) \ u ∪ (s ∩ t)
.
Proof.
  unfold pick_kill. rewrite pick_kill'_incl. cset_tac.
Qed.

Lemma pick_kill_card (X:Type) `{OrderedType X} (k : nat) (s t u v : ⦃X⦄) :
  cardinal (s ∩ u \ t) + cardinal t <= k
  -> cardinal s + cardinal t - k <= cardinal (pick_kill k s t u v)
.
Proof.
  intros card.
  assert (s ∩ u \ t [=] s \ (((s \ (u ∪ v)) ∪ (s ∩ t)) ∪ (s ∩ v \ u))) as seteq by cset_tac.
  rewrite seteq in card. rewrite cardinal_difference' in card; [|clear;cset_tac].
  eapply pick_kill'_card. omega.
Qed.
  
(* pick_killx *)

Definition pick_killx (X:Type) `{OrderedType X} (k:nat) (x:X) (s t : ⦃X⦄) : ⦃X⦄
  := pick_kill' (cardinal {x; s} - k) (s \ t) (s ∩ t)
.

Lemma incl_pick_killx (X:Type) `{OrderedType X} (k:nat) (x:X) (s t : ⦃X⦄) :
  s \ t ⊆ pick_killx k x s t
.
Proof.
  eapply incl_pick_kill'.
Qed.

Lemma pick_killx_incl (X:Type) `{OrderedType X} (k:nat) (x:X) (s t : ⦃X⦄) :
  pick_killx k x s t ⊆ s
.
Proof.
  unfold pick_killx. rewrite pick_kill'_incl. clear;cset_tac.
Qed.



