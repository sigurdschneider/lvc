Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling SpillUtil.

Set Implicit Arguments.


Notation "'lvness_fragment'" := (ann (option (list ⦃var⦄))).


Definition add_anns
           (X : Type)
           (an : X)
           (n : nat)
           (a : ann X)
  : ann X
  := iter n a (fun b => ann1 an b)
.


Lemma add_anns_zero
      (X : Type)
      (an : X)
      (a : ann X)
  :
    add_anns an 0 a = a
.
Proof.
  unfold add_anns.
  simpl.
  reflexivity.
Qed.


Lemma add_anns_S
      (X : Type)
      (an : X)
      (n : nat)
      (a : ann X)
  :
    add_anns an (S n) a = ann1 an (add_anns an n a)
.
Proof.
  unfold add_anns.
  general induction n;
    simpl; eauto.
Qed.

Definition slot_merge
           (slot : var -> var)
  : list (⦃var⦄ * ⦃var⦄) -> list ⦃var⦄
  := List.map (fun (RM : set var * set var)
               => fst RM ∪ map slot (snd RM))
.



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
  rewrite map_app; eauto.
Qed.

Definition transf_spill_ann
           (slot : var -> var)
           (rm : option (list (⦃var⦄ * ⦃var⦄) + ⦃var⦄))
  : option (list ⦃var⦄)
  :=
    match rm with
    | ⎣ inl rms ⎦ => ⎣ slot_merge slot rms ⎦
    | ⎣ inr _ ⎦ => ⎣⎦
    | ⎣⎦ => ⎣⎦
    end
.


Fixpoint do_spill_rm
         (slot : var -> var)
         (sl : spilling)
  : lvness_fragment
  :=
    add_anns None (count sl)
             (let rm' := transf_spill_ann slot (getRm sl) in
              match sl with
              | ann0 _
                => ann0 rm'

              | ann1 _ sl0
                => ann1 rm' (do_spill_rm slot sl0)

              | ann2 _ sl1 sl2
                => ann2 rm' (do_spill_rm slot sl1) (do_spill_rm slot sl2)

              | annF _ slF sl2
                => annF rm' (do_spill_rm slot ⊝ slF) (do_spill_rm slot sl2)
              end
             )
.

Lemma do_spill_rm_s
      (slot : var -> var)
      (sl : spilling)
  :
    do_spill_rm slot sl
    = add_anns None (count sl) (do_spill_rm slot (setTopAnn sl (∅,∅,snd (getAnn sl))))
.
Proof.
  unfold do_spill_rm.
  destruct sl;
    unfold count;
    simpl;
    rewrite empty_cardinal;
    simpl;
    eauto.
Qed.


(*

Definition discard_merge_sl
           (slot : var -> var)
  : spilling -> ann (option (list (set var)))
  :=
    mapAnn (fun (a : set var * set var * option (list (set var * set var)))
            => option_map (slot_merge slot) (snd a))
.


Fixpoint wrap_ann
         (X : Type)
         (wrap : ann X -> ann X)
         (a : ann X)
  : ann X
  :=
    wrap
    match a with
    | ann0 an => ann0 an
    | ann1 an a1 => ann1 an (wrap_ann wrap a1)
    | ann2 an a1 a2 => ann2 an (wrap_ann wrap a1) (wrap_ann wrap a2)
    | annF an aF a1 => annF an (wrap_ann wrap ⊝ aF) (wrap_ann wrap a1)
    end
.


Definition do_spill_rm
           (slot : var -> var)
           (sl : spilling)
  : ann (option (list (set var)))
  := discard_merge_sl slot
                      (wrap_ann
                         (fun sl => add_anns (∅,∅,None)
                                           (count sl)
                                            sl)
                          sl)
.
*)


Lemma do_spill_rm_empty
      (slot : var -> var)
      (sl : spilling)
  :
    count sl = 0
    -> do_spill_rm slot sl
      = let rm' := transf_spill_ann slot (getRm sl) in
        match sl with
        | ann0 _
          => ann0 rm'

        | ann1 _ sl1
          => ann1 rm'
                  (do_spill_rm slot sl1)

        | ann2 _ sl1 sl2
          => ann2 rm'
                  (do_spill_rm slot sl1)
                  (do_spill_rm slot sl2)
        | annF _ slF sl2
          => annF rm'
                  ((do_spill_rm slot) ⊝ slF)
                  ( do_spill_rm slot sl2)
        end
.
Proof.
  intros count_zero.
  unfold do_spill_rm.
  destruct sl;
    rewrite count_zero;
    rewrite add_anns_zero;
    destruct a;
    destruct o;
    simpl;
    fold do_spill_rm;
    reflexivity.
Qed.