Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation AutoIndTac Liveness.Liveness LabelsDefined.
Require Import SpillSound SpillUtil.

Set Implicit Arguments.

(** * DoSpillRm *)

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
           (RM : set var * set var)
  := fst RM ∪ map slot (snd RM).


Lemma add_anns_add
      (X : Type)
      (n m : nat)
      (x : X)
      (an : ann X)
  :
    add_anns x (n + m) an = add_anns x n (add_anns x m an)
.
Proof.
  general induction n;
    simpl; eauto.
  repeat rewrite add_anns_S.
  rewrite IHn.
  reflexivity.
Qed.



Lemma slot_merge_app
      (L1 L2: list (set var * set var))
      (slot : var -> var)
  :
    slot_merge slot ⊝ L1 ++ slot_merge slot ⊝ L2
      = slot_merge slot ⊝ (L1 ++ L2)
.
Proof.
  intros.
  unfold slot_merge.
  rewrite List.map_app; eauto.
Qed.

Fixpoint do_spill_rm
         (slot : var -> var)
         (sl : spilling)
  :=
    add_anns ∅ (count sl)
             (
              match sl with
              | ann0 _
                => ann0 ∅

              | ann1 _ sl0
                => ann1 ∅ (do_spill_rm slot sl0)

              | ann2 _ sl1 sl2
                => ann2 ∅ (do_spill_rm slot sl1) (do_spill_rm slot sl2)

              | annF a slF sl2
                => annF ∅ (@setTopAnn _ ⊜ (do_spill_rm slot ⊝ slF) (slot_merge slot ⊝ (snd a)))
                       (do_spill_rm slot sl2)
              end
             )
.

Lemma do_spill_rm_s
      (slot : var -> var)
      (sl : spilling)
  :
    do_spill_rm slot sl
    = add_anns ∅ (count sl) (do_spill_rm slot (setTopAnn sl (∅,∅,snd (getAnn sl))))
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

Lemma do_spill_rm_s_Sp
      (slot : var -> var)
      (sl : spilling)
  :
    do_spill_rm slot sl
    = add_anns ∅ (cardinal (getSp sl)) (do_spill_rm slot (clear_Sp sl))
.
Proof.
  rewrite <- count_clearL.
  unfold clear_L.
  unfold do_spill_rm.
  unfold count.
  rewrite getAnn_setTopAnn.
  simpl.
  rewrite add_anns_add.

  destruct sl;
    rewrite add_anns_add;
    simpl;
    rewrite empty_cardinal;
    simpl;
    eauto.
Qed.

Lemma do_spill_rm_empty
      (slot : var -> var)
      (sl : spilling)
  :
    count sl = 0
    -> do_spill_rm slot sl
      = match sl with
        | ann0 _
          => ann0 ∅

        | ann1 _ sl1
          => ann1 ∅
                  (do_spill_rm slot sl1)

        | ann2 _ sl1 sl2
          => ann2 ∅
                  (do_spill_rm slot sl1)
                  (do_spill_rm slot sl2)
        | annF a slF sl2
          => annF ∅ (@setTopAnn _ ⊜ (do_spill_rm slot ⊝ slF) (slot_merge slot ⊝ (snd a)))
                       (do_spill_rm slot sl2)
        end
.
Proof.
  intros count_zero.
  unfold do_spill_rm.
  destruct sl;
    rewrite count_zero;
    rewrite add_anns_zero;
    destruct a;
    destruct p;
    simpl;
    fold do_spill_rm; simpl; eauto.
Qed.