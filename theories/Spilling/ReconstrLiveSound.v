Require Import List Map Env AllInRel Exp AppExpFree.
Require Import IL Annotation InRel AutoIndTac Liveness LabelsDefined.
Require Import Spilling DoSpill DoSpillRm.
Require Import SpillUtil ReconstrLive.

Set Implicit Arguments.

Lemma reconstr_live_sound_s
      (slot : var -> var)
      (ZL : list params)
      (G M : set var)
      (Λ : list (set var * set var))
      (Lv : list (set var))
      (s : stmt)
      (sl : ann (set var * set var * option (list (set var * set var))))
  :
    let sl0 := setTopAnn sl (∅,∅,snd (getAnn sl)) in
    (forall G' M', live_sound Imperative ZL Lv
                     (do_spill slot M' s sl0)
                     (reconstr_live (slot_merge slot Λ) ZL G'
                                    (do_spill slot M' s sl0)
                                    (do_spill_rm slot sl0)))
   -> live_sound Imperative ZL Lv
                (do_spill slot M s sl)
                (reconstr_live (slot_merge slot Λ) ZL G
                               (do_spill slot M s sl)
                               (do_spill_rm slot sl)).
Proof.
  intros sl0 sls.
  subst sl0.

  rewrite do_spill_extract_writes.
  rewrite do_spill_rm_s.

  (* prepare induction *)
  remember (elements (getSp sl)) as elSp.
  remember (elements (getL  sl)) as elL.
  assert (count sl = length elSp + length elL) as count_sl.
  {
    unfold count.
    rewrite HeqelSp.
    rewrite HeqelL.
    do 2 rewrite elements_length.
    reflexivity.
  }
  rewrite count_sl.
  clear count_sl HeqelSp.
  revert G M.
  induction elSp;
    intros G M;
    fold do_spill.
  - simpl.
    revert G.
    clear HeqelL.
    induction elL;
      intros G;
      fold do_spill.
    + simpl.
      unfold add_anns.
      simpl.
      erewrite do_spill_Equal_M; eauto.
      clear.
      cset_tac.
    + unfold length.
      rewrite add_anns_S.
      rewrite write_loads_s.
      constructor; eauto; fold reconstr_live.
      * simpl.
        apply live_exp_sound_incl with (lv':=singleton (slot a)).
        -- econstructor.
           econstructor.
           cset_tac.
        -- clear.
           cset_tac.
      * clear.
        cset_tac.
      * apply reconstr_live_G.
        cset_tac.
  - replace (length (a::elSp) + length elL) with (S (length elSp + length elL))
      by (simpl ; reflexivity).
    rewrite add_anns_S.
    rewrite write_spills_s.
    constructor; eauto; fold reconstr_live.
    * simpl.
      apply live_exp_sound_incl with (lv':=singleton a).
      -- econstructor.
         econstructor.
         cset_tac.
      -- clear.
         cset_tac.
    * clear.
      cset_tac.
    * apply reconstr_live_G.
      cset_tac.
Qed.
