Require Import List Map Env AllInRel Exp MoreList.
Require Import IL Annotation.
Require Import Liveness.Liveness.
Require Import ExpVarsBounded SpillSound OneOrEmpty.
Require Import Take TakeSet PickLK.


Set Implicit Arguments.

(** * Repair Spill_Live *)

Fixpoint rep_spilli (sl : spilling) (lv : ann ⦃var⦄) : spilling
  :=
    match sl, lv with
    | ann0 _ , ann0 _ => sl
    | ann1 an sl', ann1 LV lv'
      => ann1 an (rep_spilli sl' lv')
    | ann2 an sl1 sl2, ann2 LV lv1 lv2
      => ann2 an (rep_spilli sl1 lv1) (rep_spilli sl2 lv2)
    | annF (Sp,L,rms) sl_F sl_t, annF LV lv_F lv_t
      => annF (Sp,L,(fun rm als => (als ∩ fst rm, als ∩ snd rm)) ⊜ rms (getAnn ⊝ lv_F))
             (rep_spilli ⊜ sl_F lv_F)
             (rep_spilli sl_t lv_t)
    | _,_ => ann0 (getAnn sl)
    end
.


Lemma rep_spilli_sound ZL Lv s lv k R R' M M' (Λ Λ' : list (⦃var⦄*⦃var⦄)) sl :
  live_sound Imperative ZL Lv s lv
  -> spill_sound k ZL Λ  (R,M) s sl
  -> PIR2 _eq Λ' ((fun rm LV => (LV ∩ fst rm, LV ∩ snd rm)) ⊜ Λ Lv)
  -> R' [=] getAnn lv ∩ R
  -> M' [=] getAnn lv ∩ M
  -> spill_sound k ZL Λ' (R',M') s (rep_spilli sl lv)
.
Proof.
  intros lvSnd spillSnd pir2 Req Meq. general induction spillSnd; invc lvSnd.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - inv_get. eapply PIR2_nth_2 in pir2 as [blk' [get_blk' blk'_eq]]; swap 1 2.
    + eapply zip_get; eauto. 
    + eapply SpillApp with (R_f:=fst blk') (M_f:=snd blk'); invc blk'_eq; cbn; eauto.
      * rewrite <-H4, H13. clear; cset_tac.
      * rewrite <-H5, H14. clear; cset_tac.
  - cbn. econstructor; eauto.
    + eauto with len.
    + eauto with len.
    + intros. inv_get. cbn. exploit H4; eauto. rewrite subset_cardinal; eauto. clear; cset_tac.
    + intros. inv_get. eapply H6.
                    
         