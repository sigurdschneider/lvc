Require Import List Map Env AllInRel Exp MoreList.
Require Import IL.
Require Import Liveness.Liveness LabelsDefined.


Set Implicit Arguments.

Definition one_or_empty_if k X `{OrderedType X} (s:set X) : set X
  := if [cardinal s >= k] then
      match choose s with
      | Some x => singleton x
      | None => ∅
      end
    else
      ∅.

Lemma one_or_empty_of_incl k X `{OrderedType X} (s:set X)
  : one_or_empty_if k s ⊆ s.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  exploit choose_1; eauto. cset_tac.
Qed.

Lemma one_or_empty_cardinal_ge k X `{OrderedType X} (s:set X)
  : k > 0 -> cardinal s >= k -> cardinal (one_or_empty_if k s) = 1.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  - intros; exfalso.
    exploit choose_2; eauto.
    exploit cardinal_1; eauto. omega.
  - intros; omega.
Qed.

Lemma one_or_empty_cardinal_lt k X `{OrderedType X} (s:set X)
  : cardinal s < k -> one_or_empty_if k s = ∅.
Proof.
  unfold one_or_empty_if. repeat cases; eauto with cset.
  - intros; exfalso. omega.
Qed.


Definition one_or_empty_if' k X `{OrderedType X} (s t:set X) : set X
  := if [cardinal s >= k] then
      match choose (s ∩ t) with
      | Some x => singleton x
      | None => match choose s with
               | Some x => singleton x
               | None => ∅
               end
      end
    else
      ∅.

      
Lemma one_or_empty_of_incl' k X `{OrderedType X} (s t:set X)
  : one_or_empty_if' k s t ⊆ s.
Proof.
  unfold one_or_empty_if'. repeat cases; eauto with cset.
  - exploit choose_1; eauto. cset_tac.
  - symmetry in Heq0. apply choose_1 in Heq0. cset_tac.
Qed.

Lemma one_or_empty_cardinal_ge' k X `{OrderedType X} (s t:set X)
  : k > 0 -> cardinal s >= k -> cardinal (one_or_empty_if' k s t) = 1.
Proof.
  unfold one_or_empty_if'. repeat cases; eauto with cset.
  - intros; exfalso.
    exploit choose_2; eauto.
    exploit cardinal_1; eauto. omega.
  - intros; omega.
Qed.

Lemma one_or_empty_cardinal_lt' k X `{OrderedType X} (s t:set X)
  : cardinal s < k -> one_or_empty_if' k s t = ∅.
Proof.
  unfold one_or_empty_if'. repeat cases; eauto with cset.
  - intros; exfalso. omega.
  - intros; exfalso. omega.
Qed.
