Require Import Util SizeInduction Get.
Require Import AnalysisForwardSSA Subterm CSet MapAgreement RenamedApart.
Require Import Infra.PartialOrder Infra.Lattice Infra.WithTop.
Require Import LabelsDefined Annotation.
Require Import ConstantPropagation ConstantPropagationAnalysis.

Local Arguments proj1_sig {A} {P} e.
Local Arguments length {A} e.
Local Arguments forward {sT} {Dom} {H} {H0} {H1} ftransform ZL st ST d.

Lemma option_R_inv x y
  : @OptionR.option_R (withTop Val.val) (withTop Val.val)
         (@poEq (withTop Val.val)
                (@withTop_PO Val.val Val.int_eq Val.Equivalence_eq_int' Val.int_eq_dec)) x y
    -> x = y.
Proof.
  intros. inv H; eauto.
  inv H0; eauto.
  do 2 f_equal. eauto.
Qed.


Lemma cp_forward_agree sT ZL AE G s (ST:subTerm s sT) ra
  (RA:renamedApart s ra)
  : agree_on poLe (G \ snd (getAnn ra))
             (domenv AE)
             (domenv (forward constant_propagation_transform ZL s ST AE)).
Proof.
  general induction RA; simpl in *.
  - destruct e.
    + pose proof (IHRA sT ZL (domupd AE x (op_eval (domenv AE) e)) G
                       (subTerm_EQ_Let eq_refl ST)); eauto.
      pe_rewrite. set_simpl.
      etransitivity; eauto.
      eapply agree_on_incl; eauto with cset.
      hnf; intros.
      unfold domupd, domenv; simpl.
      cases; lud; cset_tac'; reflexivity.
    + pose proof (IHRA sT ZL (domupd AE x (Some Top)) G
                       (subTerm_EQ_Let eq_refl ST)); eauto.
      pe_rewrite. set_simpl.
      etransitivity; eauto.
      eapply agree_on_incl; eauto with cset.
      hnf; intros.
      unfold domupd, domenv; simpl.
      lud; cset_tac'; reflexivity.
  - pe_rewrite. set_simpl.
    repeat cases; eauto using agree_on_incl with cset.
    + admit.
    + admit.
  - reflexivity.
  - admit.

Qed.

Definition cp_sound sT AE Cp ZL s (ST:subTerm s sT)
  : poEq (forward constant_propagation_transform ZL s ST AE) AE
    -> labelsDefined s (length ZL)
    -> cp_sound (domenv AE) Cp s.
Proof.
  intros EQ LD.
  general induction LD; simpl in *.
  - destruct e; simpl.
    + specialize (EQ x).
      admit.

    + econstructor; eauto.
      simpl. admit.
  - let_case_eq; try let_pair_case_eq; subst; simpl in *;
      repeat cases in EQ; simpl in *;
        econstructor; intros; eauto;
          try rewrite COND in *; simpl in *;
            try rewrite Val.val2bool_true in *;
            try rewrite Val.val2bool_false in *;
            isabsurd.
    + admit.
    + admit.
    + eapply IHLD1; eauto. admit.
    + eapply IHLD2; eauto. admit.
  - econstructor.
  - (* invariant with ZL and Cp *) admit.
  - econstructor.
    + intros.
      eapply H0 with (ZL0:=fst ⊝ F ++ ZL); eauto with len.
      admit.
    + eapply IHLD with (ZL0:=fst ⊝ F ++ ZL); eauto with len.
Admitted.
