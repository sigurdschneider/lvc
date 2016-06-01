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
  + edestruct a as [|lv a'| |]; [dec_right| | dec_right| dec_right].
    edestruct (X x0); [ eauto | dec_solve | dec_right].
  + edestruct a as [?|?|lv als alt|]; [dec_right| dec_right| | dec_right].
    edestruct (X x1), (X x2); eauto; [ | dec_right| |dec_right ]; dec_solve.
  + destruct a; [ | dec_right | dec_right | dec_right].
    destruct (get_dec DL (counted l)) as [[[G'|] ?]|?]; [| dec_right | dec_right].
    dec_solve.
  + destruct a; [ | dec_right | dec_right | dec_right]. dec_solve.
  + edestruct a as [|lv a'| |]; [dec_right| | dec_right| dec_right].
    edestruct (X x0); eauto; [| dec_right]. dec_solve; eauto.
  + destruct a as [?|?|lv als alt| ]; [dec_right| dec_right| dec_right|].
    ensure (length s = length sa).
    edestruct (X x) with (DL:=Some ⊝ (getAnn ⊝ sa) \\ (fst ⊝ s) ++ DL); eauto; [ |dec_right].
    edestruct (indexwise_R_dec'
                 (R:=fun x y =>
                       srd (restr (getAnn y \ of_list (fst x))
                                  ⊝ (Some ⊝ (getAnn ⊝ sa) \\ (fst ⊝ s) ++ DL))
                           (snd x) y) (LA:=s) (LB:=sa)).
    intros. eapply X; eauto.
    dec_solve. dec_right.
    Grab Existential Variables. eauto. eauto. eauto. eauto.
Defined.

(** ** local injectivity is decidable *)


Local Hint Extern 1 =>
match goal with
  [ H : annotation _ _ |- annotation _ _ ] => inv H; eassumption
end.

Definition locally_inj_dec (ϱ:env var) (s:stmt) (lv:ann (set var)) (an:annotation s lv)
  : {locally_inj ϱ s lv} + {~ locally_inj ϱ s lv}.
Proof.
  revert ϱ lv an.
  sind s; intros; destruct s; destruct lv; try solve [ exfalso; inv an ].
  + ensure (injective_on a ϱ).
    edestruct (IH s); eauto. dec_solve. dec_right.
  + ensure (injective_on a ϱ).
    edestruct (IH s1); eauto; [|dec_right].
    edestruct (IH s2); eauto; [|dec_right]. dec_solve.
  + ensure (injective_on a ϱ); dec_solve.
  + ensure (injective_on a ϱ); dec_solve.
  + ensure (injective_on a ϱ).
    edestruct (IH s); eauto; [| dec_right]. dec_solve.
  + ensure (injective_on a ϱ).
    ensure (length s = length sa).
    edestruct (IH s0); eauto; [| dec_solve].
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
