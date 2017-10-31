Require Import Util CSet CMap MapDefined SetOperations OUnion OptionR.
Require Import IL InRel4 RenamedApart LabelsDefined Restrict.
Require Import Annotation Liveness.Liveness Coherence Delocation.
Require Import Sim SimTactics.

(*  IL_Types. *)

Set Implicit Arguments.
Unset Printing Records.
Unset Printing Abstraction Types.

Inductive approx
  : list params -> list (set var) -> list (option (set var)) -> list params -> list I.block -> list I.block
    -> params -> set var -> option (set var) -> params -> I.block -> I.block -> Prop :=
  blk_approxI o (Za Z':list var) ZL Lv DL ZAL s ans ans_lv ans_lv' n L1 L2
              (RD:forall G, o = Some G ->
                       live_sound Imperative (@List.app _ ⊜ ZL ZAL) Lv (compile ZAL s ans) ans_lv'
                       /\ trs (restr G ⊝ DL) s ans_lv ans)
  : approx ZL Lv DL ZAL L1 L2 Z' (getAnn ans_lv') o Za (I.blockI Z' s n) (I.blockI (Z'++Za) (compile ZAL s ans) n).

Lemma approx_restrict ZL Lv DL ZAL L L' G
  : inRel approx ZL Lv DL ZAL L L'
    -> inRel approx ZL Lv (restr G ⊝ DL) ZAL L L'.
Proof.
  eapply inRel_map_A3.
  intros. inv H. econstructor; eauto with len.
  intros. destruct a3; simpl in *; isabsurd.
  cases in H0; isabsurd.
  exploit RD; eauto; dcr.
  split; eauto.
  rewrite restrict_idem; eauto.
Qed.

Lemma delocation_sim DL ZL ZAL L L' (E E':onv val) s ans Lv' ans_lv ans_lv'
  (RD: trs DL s ans_lv ans)
  (EA: inRel approx ZL Lv' DL ZAL L L')
  (EQ: (@feq _ _ eq) E E')
  (LV': live_sound Imperative (app (A:=var) ⊜ ZL ZAL) Lv' (compile ZAL s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E')
  : sim bot3 Bisim (L, E, s) (L', E', compile ZAL s ans).
Proof.
  revert_all. pcofix delocation_sim; intros.
  inv RD; invt live_sound; simpl.
  - destruct e.
    + remember (op_eval E e). symmetry in Heqo.
      pose proof Heqo. rewrite EQ in H0.
      destruct o.
      * pone_step. simpl in *.
        right; eapply delocation_sim; eauto using approx_restrict with len.
        -- rewrite EQ; reflexivity.
        -- eapply defined_on_update_some. eapply defined_on_incl; eauto.
      * pno_step.
    + remember (omap (op_eval E) Y); intros. symmetry in Heqo.
      pose proof Heqo. erewrite omap_agree in H0. Focus 2.
      intros. rewrite EQ. reflexivity.
      destruct o.
      * pextern_step; try congruence.
        -- right; eapply delocation_sim; eauto using approx_restrict with len.
           hnf; intros. lud; eauto.
           eauto using defined_on_update_some, defined_on_incl.
        -- right; eapply delocation_sim; eauto using approx_restrict with len.
           hnf; intros. lud; eauto.
           eauto using defined_on_update_some, defined_on_incl.
      * pno_step.
  - remember (op_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H1.
    destruct o.
    case_eq (val2bool v); intros.
    + pone_step. right; eapply delocation_sim; eauto using defined_on_incl.
    + pone_step. right; eapply delocation_sim; eauto using defined_on_incl.
    + pno_step.
  - pno_step. simpl. rewrite EQ; eauto.
  - simpl counted in *. inv_get.
    erewrite get_nth in *; eauto.
    case_eq (omap (op_eval E) Y); intros.
    + inv_get.
      assert (❬Y❭ = ❬x❭). {
        len_simpl. omega.
      }
      inRel_invs. inv H12; simpl in *.
      edestruct (omap_var_defined_on x0); eauto.
      eapply get_in_incl. intros.
      exploit H9; eauto using get_app_right. inv H8; eauto.
      pone_step. rewrite omap_app.
      erewrite omap_agree with (g:=op_eval E). rewrite H1.
      simpl. rewrite H6. reflexivity. intros. rewrite EQ; eauto.
      simpl. exploit RD0; eauto; dcr.
      right; eapply delocation_sim; eauto using approx_restrict with len.
      * rewrite EQ. rewrite List.map_app.
        rewrite update_with_list_app; eauto with len.
        rewrite (omap_self_update _ _ H6); reflexivity.
      * eapply defined_on_update_list; eauto with len.
        eapply defined_on_incl; eauto.
    + pno_step.
      rewrite omap_app in def. monad_inv def.
      erewrite omap_agree in H1. erewrite H1 in EQ0. congruence.
      intros. rewrite EQ. reflexivity.
  - pone_step.
    assert (length F = length als).
    rewrite <- H7. eauto with len.
    rewrite fst_compileF_eq in H6; eauto with len.
    rewrite <- zip_app in H6; eauto with len.
    right; eapply delocation_sim; eauto 20 with len.
    + repeat rewrite zip_app; eauto 30 with len.
      econstructor; eauto.
      eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
      * intros; inv_get.
        exploit H8; eauto.
        unfold I.mkBlock. unfold compileF in H15. inv_get. simpl in *.
        eapply blk_approxI. eauto 20 with len.
        intros. invc H10. split; eauto.
        rewrite fst_compileF_eq in H5; eauto with len.
        rewrite <- zip_app in H5; eauto with len.
    + simpl in *. eapply defined_on_incl; eauto.
Qed.

Lemma correct' E s ans ans_lv ans_lv'
  (RD: trs nil s ans_lv ans)
  (LV': live_sound Imperative nil nil (compile nil s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E)
  : sim bot3 Bisim (nil, E, s) (nil, E, compile nil s ans).
Proof.
  eapply (@delocation_sim nil nil nil nil nil); eauto using @inRel; reflexivity.
Qed.

Lemma correct E s ans ans_lv
  (RD: trs nil s ans_lv ans)
  (LV': live_sound Imperative nil nil s ans_lv)
  (EDEF: defined_on (getAnn ans_lv) E)
  (APL:  additionalParameters_live nil s ans_lv ans)
  : sim bot3 Bisim (nil, E, s) (nil, E, compile nil s ans).
Proof.
  eapply (@delocation_sim nil nil nil nil nil); eauto using @inRel.
  - reflexivity.
  - eapply live_sound_compile; eauto.
Qed.
