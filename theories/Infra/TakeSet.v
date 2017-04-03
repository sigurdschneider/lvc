Require Import Take CSet.


Lemma in_take_list X `{OrderedType X} (l: list X) (n: nat) (x:X) :
InA _eq x (take n l) -> InA _eq x l.
Proof.
revert n.
induction l; destruct n; simpl; eauto; intros G.
- inv G.
- inv G.
  + constructor; eauto.
  + apply InA_cons_tl. eauto.
Qed.

Lemma take_dupFree_list X `{OrderedType X} ( l : list X ) (n : nat) :
NoDupA _eq l -> NoDupA _eq (take n l).
Proof.
intro noDup. revert n.
induction noDup; destruct n; simpl; eauto using NoDupA.
econstructor; eauto.
- intros no. apply in_take_list in no. contradiction.
Qed.

Lemma take_dupFree X `{OrderedType X} ( s : set X ) (n:nat) :
NoDupA _eq (take n (elements s)).
Proof.
apply take_dupFree_list. apply elements_3w.
Qed.


Lemma take_list_incl X `{OrderedType X} (n : nat) (L:list X) :
        of_list (take n L) ⊆ of_list L.
Proof.
  general induction L; destruct n; simpl; eauto with cset.
Qed.

Lemma take_set_incl X `{OrderedType X} (n : nat) (s : set X) :
        of_list (take n (elements s)) ⊆ s.
Proof.
  rewrite take_list_incl.
  hnf; intros. eapply elements_iff. cset_tac.
Qed.

Lemma take_of_list_cardinal X `{OrderedType X} n (l : list X)
: cardinal (of_list (take n l)) <= n.
Proof.
revert n. induction l; intro n.
- rewrite take_nil. simpl. rewrite empty_cardinal. omega.
- destruct n; simpl.
  + rewrite empty_cardinal. omega.
  + rewrite add_cardinal. rewrite IHl. omega.
Qed.

Set Implicit Arguments.

Definition set_take (X:Type) `{OrderedType X} (k:nat) (s:⦃X⦄)
  := of_list (take k (elements s))
.

Definition set_take_prefer (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄)
  := of_list (take k (elements t ++ elements (s \ t)))
.

Definition set_take_avoid (X:Type) `{OrderedType X} (k:nat) (s t : ⦃X⦄)
  := of_list (take k (elements (s \ t) ++ elements (s ∩ t)))
.



Lemma set_take_incl (X:Type) `{OrderedType X} (k:nat) (s:⦃X⦄)
  : set_take k s ⊆ s
.
Proof.
  apply take_set_incl.
Qed.


Lemma set_take_prefer_incl (X:Type) `{OrderedType X} k (s t:⦃X⦄)
  : set_take_prefer k s t ⊆ s ∪ t
.
Proof.
  decide (k < cardinal t); unfold set_take_prefer; try rewrite <-elements_length in *;
    [rewrite take_app_le|rewrite take_app_ge]; [|omega| |omega].
  - rewrite take_set_incl. cset_tac.
  - rewrite of_list_app.
    apply union_incl_split; [rewrite of_list_elements|rewrite take_set_incl]; cset_tac.
Qed.

Lemma set_take_eq (X:Type) `{OrderedType X} k (s :⦃X⦄) :
  cardinal s <= k -> set_take k s [=] s
.
Proof.
  intros card. unfold set_take. rewrite take_eq_ge.
  - rewrite of_list_elements. eauto.
  - rewrite elements_length. eauto.
Qed.

      

Lemma set_take_avoid_incl (X:Type) `{OrderedType X} k (s t:⦃X⦄)
  : set_take_avoid k s t ⊆ s
.
Proof.
  decide (k < cardinal (s \ t)); unfold set_take_avoid; try rewrite <-elements_length in *;
    [rewrite take_app_le|rewrite take_app_ge]; [|omega| |omega].
  - rewrite take_set_incl. cset_tac.
  - rewrite of_list_app.
    apply union_incl_split; [rewrite of_list_elements|rewrite take_set_incl]; cset_tac.
Qed.


Lemma set_take_prefer_card_incl (X:Type) `{OrderedType X} k (s t:⦃X⦄)
  : cardinal t <= k -> t ⊆ set_take_prefer k s t
.
Proof.
  intros card.
  unfold set_take_prefer; rewrite <-elements_length in card. rewrite take_app_ge; eauto.
  rewrite of_list_app, of_list_elements, union_comm. cset_tac.
Qed.

Lemma set_take_avoid_incl2 (X:Type) `{OrderedType X} k (s t:⦃X⦄)
  : k <= cardinal (s \ t) -> set_take_avoid k s t ⊆ s \ t
.
Proof.
  intros card.
  unfold set_take_avoid. rewrite <-elements_length in card. rewrite take_app_le; eauto.
  apply set_take_incl.
Qed.

Lemma set_take_prefer_eq (X:Type) `{OrderedType X} k (s t : ⦃X⦄)
  : cardinal s <= k -> t ⊆ s -> set_take_prefer k s t [=] s
.
Proof.
  intros card sub. apply incl_eq.
  - unfold set_take_prefer. rewrite take_app_ge.
    + rewrite of_list_app, of_list_elements. rewrite take_eq_ge.
      * rewrite of_list_elements. cset_tac.
      * rewrite !elements_length. rewrite cardinal_difference'; eauto. omega.
    + rewrite elements_length. unfold ">=". rewrite subset_cardinal;eauto.
  - setoid_rewrite <-union_subset_equal at 4; eauto. rewrite set_take_prefer_incl. cset_tac.
Qed.


Lemma set_take_avoid_disj (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  cardinal (s \ t) >= k
  -> disj (set_take_avoid k s t) t
.
Proof.
  intros card x inS inT. unfold set_take_avoid in inS.
  rewrite take_app_le in inS.
  - rewrite take_set_incl in inS. cset_tac.
  - rewrite elements_length. eauto.
Qed.


Lemma set_take_cardinal_eq (X:Type) `{OrderedType X} k (s : ⦃X⦄) :
  k <= cardinal s
  -> cardinal (set_take k s) = k
.
Proof.
  intros card. unfold set_take. rewrite card_in_of_list.
  - rewrite take_length_le; eauto. rewrite elements_length; eauto.
  - apply take_dupFree.
Qed.
  

Definition set_take_least_avoid (X:Type) `{OrderedType X} k (s t : ⦃X⦄) : ⦃X⦄
  :=
    s \ t ∪ set_take (k - cardinal (s \ t)) (s ∩ t)
.

Lemma set_take_least_avoid_incl (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  set_take_least_avoid k s t ⊆ s
.
Proof.
  unfold set_take_least_avoid. rewrite set_take_incl. cset_tac.
Qed.


Lemma incl_set_take_least_avoid (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  s \ t ⊆ set_take_least_avoid k s t
.
Proof.
  unfold set_take_least_avoid. cset_tac.
Qed.

Lemma set_take_least_avoid_eq (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  k <= cardinal (s \ t)
  -> set_take_least_avoid k s t [=] s \ t
.
Proof.
  intros card. unfold set_take_least_avoid. 
  replace (k - cardinal (s \ t)) with 0 by omega. cbn. cset_tac.
Qed.

Lemma set_take_size (X:Type) `{OrderedType X} k (s : ⦃X⦄) :
  cardinal (set_take k s) <= k
.
Proof.
  unfold set_take. rewrite cardinal_of_list_nodup; [|apply take_dupFree]. decide (cardinal s <= k).
  - rewrite take_length_ge; rewrite elements_length; omega.
  - rewrite take_length_le; eauto. rewrite elements_length; omega.
Qed.

Lemma set_take_least_avoid_size (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  k <= cardinal s
  -> k <= cardinal (set_take_least_avoid k s t)
.
Proof.
  intros card. unfold set_take_least_avoid.
  rewrite union_cardinal.
  - unfold set_take. rewrite cardinal_of_list_nodup; [|apply take_dupFree]. rewrite take_length_le.
    + omega. 
    + rewrite elements_length. apply Nat.le_sub_le_add_r. rewrite <-union_cardinal; [|cset_tac].
      rewrite <-subset_cardinal; eauto. cset_tac.
  - intros. rewrite set_take_incl. cset_tac.
Qed.


Lemma set_take_prefer_size (X:Type) `{OrderedType X} k (s t : ⦃X⦄) :
  cardinal (set_take_prefer k s t) <= k
.
Proof.
  unfold set_take_prefer. rewrite cardinal_of_list_nodup.
  - decide (length (elements t ++ elements (s \ t))  <= k).
    + rewrite take_length_ge; eauto.
    + rewrite take_length_le; eauto. omega.
  - apply take_dupFree_list. apply NoDupA_app; eauto.
    + apply elements_3w.
    + apply elements_3w.
    + intros. apply <-elements_iff in H0. apply <-elements_iff in H1. cset_tac.
Qed.
