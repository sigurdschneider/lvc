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
  rewrite IHL. reflexivity.
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