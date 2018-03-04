Require Import Val Var IL RenameApart Alpha Sim.

Definition alpha_ex_ili : stmt := stmtFun ((nil, stmtReturn (Var 1))::nil)
                                     (stmtIf (Var 1)
                                             (stmtLet 1 (Operation (Con val_false))
                                                      (stmtApp (LabI 0) nil))
                                             (stmtLet 1 (Operation (Con val_true))
                                                      (stmtApp (LabI 0) nil))).

Definition alpha_ex_ili_ren : stmt := stmtFun ((nil, stmtReturn (Var 1))::nil)
                                     (stmtIf (Var 1)
                                             (stmtLet 1 (Operation (Con val_false))
                                                      (stmtApp (LabI 0) nil))
                                             (stmtLet 2 (Operation (Con val_true))
                                                      (stmtApp (LabI 0) nil))).

Lemma alpha_eq
  : alpha id id alpha_ex_ili alpha_ex_ili_ren.
Proof.
  repeat (econstructor; simpl; intros; inv_get; simpl).
Qed.

Example no_alpha_ili L (E:onv val) (EQ:E 1%positive = Some val_false)
        (EQ2:E 2%positive <> Some val_one)
  : ~ sim bot3 Sim
      (L, E, alpha_ex_ili)
      (L, E, alpha_ex_ili_ren).
Proof.
  intro.
  eapply sim_terminate' in H as [? ?]; dcr; swap 1 2; swap 2 4.
  - eapply star2_silent. econstructor.
    eapply star2_silent. econstructor 4. simpl; eauto.
    eapply val2bool_false.
    eapply star2_silent. econstructor. reflexivity.
    eapply star2_silent. econstructor; simpl; eauto using get.
    simpl. eapply star2_refl.
  - reflexivity.
  - stuck2.
  - inv H0. not_normal H2.
    inv H1.
    inv H5. simpl in *. congruence.
    inv H4. simpl in *.
    assert (v = val_false) by congruence. subst. rewrite val2bool_false in *. congruence.
    inv H6. simpl in *. congruence.
    inv H7. simpl in *.
    inv H8. simpl in *. congruence.
    inv H9. simpl in *. clear_trivial_eqs. simpl in *.
    inv H10. simpl in *.
    + assert (v = val_false) by congruence. subst.
      lud. clear_trivial_eqs.
      assert (val_true = val_false) by congruence.
      eapply val_true_false_neq; eauto.
    + inv H11.
Qed.