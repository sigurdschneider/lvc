Require Import AllInRel Util Map Env EnvTy Exp IL Annotation Coherence Bisim DecSolve.
Require Import Liveness Restrict Allocation Indexwise.

Set Implicit Arguments.
Unset Printing Records.

(** ** Coherence is decidable *)

Definition srd_dec DL s a
  : Computable (srd DL s a).
Proof.
  hnf. revert DL a.
  sinduction s; simpl.
  + edestruct a as [|lv a'| |]; try dec_solve.
    edestruct (X x0); try dec_solve; eauto.
  + edestruct a as [?|?|lv als alt|]; try dec_solve.
    edestruct (X x1), (X x2); try dec_solve; eauto.
  + destruct a;
    destruct (get_dec DL (counted l)) as [[[G'|] ?]|?];
    try dec_solve.
  + destruct a; try dec_solve.
  + edestruct a as [|lv a'| |]; try dec_solve.
    edestruct (X x0); try dec_solve; eauto.
  + destruct a as [?|?|lv als alt| ]; try dec_solve.
    decide (length s = length sa); try dec_solve.
    edestruct (X x) with (DL:=oglobals s sa++DL); eauto; try dec_solve.
    edestruct (indexwise_R_dec'
                 (R:=fun x y => srd (restrict (oglobals s sa ++ DL) (getAnn y \ of_list (fst x))) (snd x) y) (LA:=s) (LB:=sa));
      try dec_solve.
    intros. eapply X; eauto.
    Grab Existential Variables. eauto. eauto. eauto. eauto.
Defined.

(** ** local injectivity is decidable *)

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  revert ϱ lv an.
  sind s; intros; destruct s; destruct lv; try (now exfalso; inv an).
  + decide(injective_on a ϱ); try dec_solve.
    edestruct (IH s); eauto; try dec_solve. inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct (IH s1); eauto; try inv an; eauto; try dec_solve;
    edestruct (IH s2); eauto; try inv an; eauto; try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve.
  + decide(injective_on a ϱ); try dec_solve;
    edestruct (IH s); eauto; try dec_solve; inv an; eauto.
  + decide(injective_on a ϱ); try dec_solve.
    decide(length s = length sa); try dec_solve.
    edestruct (IH s0); eauto; try inv an; eauto; try dec_solve.
    edestruct (indexwise_R_dec' (R:=fun x y => locally_inj ϱ (snd x) y) (LA:=s) (LB:=sa));
      try dec_solve.
    intros. eapply IH; eauto. inv an; eauto.
Defined.

Instance locally_inj_dec_inst (ϱ:env var) (s:stmt) (lv:ann (set var))
         `{Computable (annotation s lv)}
  : Computable (locally_inj ϱ s lv).
Proof.
  destruct H as [].
  hnf; eauto using locally_inj_dec.
  right; intro; eauto using locally_inj_annotation.
Defined.
