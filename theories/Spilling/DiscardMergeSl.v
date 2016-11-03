Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.



Definition discard_sl := mapAnn (fun (a : (* = mapAnn ? snd *)
      set var * set var * option (list (set var * set var)))
                                           => match a with (_,_,rm) => rm end).




Definition slot_merge slot := List.map (fun (RM : set var * set var)
                                           => fst RM ∪ map slot (snd RM)).






Lemma slot_merge_app
      (L1 L2: list (set var * set var))
      (slot : var -> var)
  :
    slot_merge slot L1 ++ slot_merge slot L2
      = slot_merge slot (L1 ++ L2)
.
Proof.
  intros.
  unfold slot_merge.
  rewrite List.map_app; eauto.
Qed.



Definition discard_merge_sl (slot : var -> var) :=
mapAnn (fun (a : set var * set var * option (list (set var * set var)))
         => match a with
            | (_,_,None)
              => None
            | (_,_,Some rms)
              => Some (slot_merge slot rms)
           end).


Lemma discard_merge_sl_step
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    discard_merge_sl slot sl =
    match sl with
    | ann0 (_,_,None)
      => ann0 None
    | ann1 (_,_,None) sl1
      => ann1 None (discard_merge_sl slot sl1)
    | ann2 (Sp,L,None) sl1 sl2
      => ann2 None (discard_merge_sl slot sl1)
                   (discard_merge_sl slot sl2)
    | annF (_,_,None) F sl2
      => annF None (discard_merge_sl slot ⊝ F)
                   (discard_merge_sl slot sl2)
    | ann0 (_,_,Some rm)
      => ann0 (Some (slot_merge slot rm))
    | ann1 (_,_,Some rm) sl1
      => ann1 (Some (slot_merge slot rm)) (discard_merge_sl slot sl1)
    | ann2 (_,_,Some rm) sl1 sl2
      => ann2 (Some (slot_merge slot rm)) (discard_merge_sl slot sl1)
                   (discard_merge_sl slot sl2)
    | annF (_,_,Some rm) F sl2
      => annF (Some (slot_merge slot rm)) (discard_merge_sl slot ⊝ F)
                   (discard_merge_sl slot sl2)
    end.
Proof.
  induction sl; destruct a as [spl rm]; induction rm;
    unfold discard_merge_sl; fold discard_merge_sl; simpl; destruct spl;
      reflexivity.
Qed.
