Require Import Util CSet IL Annotation AnnP MapSep InfinitePartition.

Set Implicit Arguments.

Definition bounded_in (X : Type) `{OrderedType X} (D : ⦃X⦄) (k : nat)
  : ⦃X⦄ -> Prop
  := fun a => cardinal (D ∩ a) <= k .

Lemma filter_meet_idem X `{OrderedType X} (p:X -> bool) `{Proper _ (_eq ==> eq) p} s
  : SetInterface.filter p s ∩ s [=] SetInterface.filter p s.
Proof.
  split; cset_tac.
Qed.

Lemma bounded_in_part_bounded  (p:inf_subset) (VD:set var) k lv
      (BND:bounded_in VD k lv)
      (AP : For_all (fun x : nat => p x) VD)
      (Incl : lv ⊆ VD)
  : part_bounded p k lv.
Proof.
  unfold part_bounded, bounded_in in *.
  rewrite <- (@filter_incl _ _ p) in Incl; eauto.
  rewrite <- Incl in BND. rewrite filter_meet_idem in BND; eauto.
Qed.

Lemma ann_P_bounded_in_part_bounded (p:inf_subset) k lv (VD:set var)
      (AN:ann_P (bounded_in VD k) lv)
      (AP:For_all (inf_subset_P p) VD)
      (Incl:ann_P (fun x => x ⊆ VD) lv)
  : ann_P (part_bounded p k) lv.
Proof.
  general induction AN; inv Incl; simpl in *;
    econstructor; eauto using bounded_in_part_bounded.
Qed.