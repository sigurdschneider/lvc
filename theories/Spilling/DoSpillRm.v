Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import SpillUtil.





Fixpoint do_spill_rm'
         (slot : var -> var)
         (n : nat)
         (sl: ann (set var * set var * option (list (set var * set var ))))
         {struct sl}
  : ann (set var * set var * option (list (set var * set var)))
  :=
    let rm := snd (getAnn sl) in
    (fix add_nones n
        :=
    match n with
    | 0 =>
        match sl with
        | ann0 a => sl
        | ann1 a sl_s
          => ann1 a (do_spill_rm' slot (count sl_s) sl_s)
        | ann2 a sl_s sl_t
          => ann2 a (do_spill_rm' slot (count sl_s) sl_s)
                    (do_spill_rm' slot (count sl_t) sl_t)
        | annF a sl_F sl_t
          => annF a ((fun sl_s => do_spill_rm' slot (count sl_s) sl_s) ⊝ sl_F)
                    (do_spill_rm' slot (count   sl_t) sl_t)
        end
    | S n =>
        ann1 (∅,∅,None) (add_nones n)
    end) n
.



Definition do_spill_rm
           (slot : var -> var)
           (sl : ann (set var * set var * option (list (set var * set var))))
  := do_spill_rm' slot (count sl) sl.



Lemma do_spill_rm_s
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
      (n : nat)
  :
    do_spill_rm' slot (S n) sl
    = ann1 (∅,∅,None) (do_spill_rm' slot n sl)
.
Proof.
  unfold do_spill_rm' at 1.
  destruct sl;
    simpl;
    reflexivity.
Qed.




Lemma do_spill_rm_zero
      (slot : var -> var)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    do_spill_rm' slot 0 sl
    = match sl with
       | ann0 (Sp, L, rm) => ann0 (Sp, L, rm)
       | ann1 (Sp, L, rm) sl_s => ann1 (Sp, L, rm) (do_spill_rm slot sl_s)
       | ann2 (Sp, L, rm) sl_s sl_t =>
           ann2 (Sp, L, rm) (do_spill_rm slot sl_s) (do_spill_rm slot sl_t)
       | annF (Sp, L, rm) sl_F sl_t =>
           annF (Sp, L, rm) (do_spill_rm slot ⊝ sl_F) (do_spill_rm slot sl_t)
       end
.
Proof.
  unfold do_spill_rm'.
  induction sl; fold do_spill_rm';
    destruct a;
    destruct p;
    reflexivity.
Qed.