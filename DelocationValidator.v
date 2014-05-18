Require Import AllInRel Util Map Env EnvTy Exp IL Annotation Coherence Bisim DecSolve Liveness Restrict Delocation.

Set Implicit Arguments.
Unset Printing Records.

Lemma trs_dec DL ZL s ans_lv ans
  : {trs DL ZL s ans_lv ans} +
    {~ trs DL ZL s ans_lv ans}.
Proof.
  general induction s; destruct ans; destruct ans_lv; isabsurd; try dec_solve.
  + destruct a; edestruct (IHs (restrict DL (a0\{{x}})) ZL ans_lv ans); try dec_solve.
  + destruct a; subst; try dec_solve;
    destruct (IHs1 DL ZL ans_lv1 ans1); try dec_solve;
    destruct (IHs2 DL ZL ans_lv2 ans2); try dec_solve.
  + destruct (get_dec DL (counted l)) as [[[G'|]]|];
    destruct (get_dec ZL (counted l)) as [[Za ?]|];
    try destruct a;
    try decide (G' ⊆ a0);
    try decide (of_list (Za) ⊆ a0);
    subst; try dec_solve; try inv an; try inv an_lv; eauto.
  + decide (a = nil);
    subst; try dec_solve; try inv an; try inv an_lv; eauto.
  + edestruct (IHs1 (restrict (Some (getAnn ans_lv1 \ of_list (Z++a))::DL) (getAnn ans_lv1 \ of_list (Z++a))) (a::ZL) ans_lv1 ans1); eauto;
    edestruct (IHs2 (Some (getAnn ans_lv1 \ of_list (Z++a)) :: DL) (a :: ZL) ans_lv2 ans2); decide (of_list a ⊆ getAnn ans_lv1);
    eauto; try dec_solve.
Defined.

Instance trs_dec_inst DL ZL s lv Y
: Computable (trs DL ZL s lv Y).
Proof.
  try (now right; intro A; eapply trs_annotation in A; dcr; eauto).
  hnf; eauto using trs_dec.
Defined.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
