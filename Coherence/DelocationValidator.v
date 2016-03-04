Require Import AllInRel Util Map Env EnvTy Exp IL Annotation Coherence Bisim DecSolve.
Require Import Liveness Restrict Delocation Indexwise.

Set Implicit Arguments.
Unset Printing Records.

Lemma trs_dec DL ZL s ans_lv ans
  : {trs DL ZL s ans_lv ans} +
    {~ trs DL ZL s ans_lv ans}.
Proof.
  revert DL ZL ans_lv ans.
  sind s. destruct s; destruct ans; try dec_solve;
  destruct ans_lv; try dec_solve.
  + destruct a; edestruct (IH s (ltac:(eauto)) (restrict DL (a0\{{x}})) ZL ans_lv ans); try dec_solve.
  + destruct a; subst; try dec_solve;
    destruct (IH s1 (ltac:(eauto)) DL ZL ans_lv1 ans1); try dec_solve;
    destruct (IH s2 (ltac:(eauto)) DL ZL ans_lv2 ans2); try dec_solve.
  + destruct (get_dec DL (counted l)) as [[[G'|]]|];
    destruct (get_dec ZL (counted l)) as [[Za ?]|];
    try destruct a;
    try decide (G' ⊆ a0);
    try decide (of_list (Za) ⊆ a0);
    subst; try dec_solve; try inv an; try inv an_lv; eauto.
  + decide (a = nil);
    subst; try dec_solve; try inv an; try inv an_lv; eauto.
  + destruct a; edestruct (IH s (ltac:(eauto)) (restrict DL (a0\{{x}})) ZL ans_lv ans); try dec_solve.
  + decide (length s = length a);
    decide (length s = length sa);
    decide (length s = length sa0); try dec_solve.
    destruct (IH s0 (ltac:(eauto)) (mkGlobals s a sa0 ++ DL) (a ++ ZL) ans_lv ans); try dec_solve.
    edestruct (indexwise_R4_dec
                 (R:=fun lvs Zs Za' ans' => trs (restrict (mkGlobals s a sa0 ++ DL)
                                                         (getAnn lvs \ of_list (fst Zs ++ Za')))
                                               (a ++ ZL) (snd Zs) lvs ans')
                 (LA:=sa0)
                 (LB:=s)
                 (LC:=a)
                 (LD:=sa)); intros; eauto.
    hnf; intros. eapply IH; eauto.
    dec_solve. dec_solve.
Defined.

Instance trs_dec_inst DL ZL s lv Y
: Computable (trs DL ZL s lv Y).
Proof.
  try (now right; intro A; eapply trs_annotation in A; dcr; eauto).
  hnf; eauto using trs_dec.
Defined.
