Require Import Util CSet CMap MapDefined SetOperations OUnion OptionR.
Require Import IL InRel4 RenamedApart LabelsDefined Restrict.
Require Import Annotation Liveness Coherence Delocation.
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
                       /\ trs (restr G ⊝ DL) ZAL s ans_lv ans)
  : length DL = length ZL
  -> length ZL = length Lv
  -> approx ZL Lv DL ZAL L1 L2 Z' (getAnn ans_lv') o Za (I.blockI Z' s n) (I.blockI (Z'++Za) (compile ZAL s ans) n).

Lemma approx_restrict ZL Lv DL ZAL L L' G
  : inRel approx ZL Lv DL ZAL L L'
    -> inRel approx ZL Lv (restr G ⊝ DL) ZAL L L'.
Proof.
  eapply inRel_map_A3.
  intros. inv H. econstructor; eauto with len.
  intros. destruct a3; simpl in *; isabsurd.
  cases in H2; isabsurd.
  exploit RD; eauto; dcr.
  split; eauto.
  rewrite restrict_idem; eauto.
Qed.

Lemma delocation_sim DL ZL ZAL L L' (E E':onv val) s ans Lv' ans_lv ans_lv'
  (RD: trs DL ZAL s ans_lv ans)
  (EA: inRel approx ZL Lv' DL ZAL L L')
  (EQ: (@feq _ _ eq) E E')
  (LV': live_sound Imperative (app (A:=var) ⊜ ZL ZAL) Lv' (compile ZAL s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E')
  (LEN1: length DL = length ZL)
  (LEN2: length ZL = length Lv')
  : sim Bisim (L, E, s) (L', E', compile ZAL s ans).
Proof.
  revert_all. cofix; intros.
  inv RD; invt live_sound; simpl.
  - destruct e.
    + remember (op_eval E e). symmetry in Heqo.
      pose proof Heqo. rewrite EQ in H0.
      destruct o.
      * one_step. simpl in *.
        eapply delocation_sim; eauto using approx_restrict with len.
        -- rewrite EQ; reflexivity.
        -- eapply defined_on_update_some. eapply defined_on_incl; eauto.
      * no_step.
    + remember (omap (op_eval E) Y); intros. symmetry in Heqo.
      pose proof Heqo. erewrite omap_agree in H0. Focus 2.
      intros. rewrite EQ. reflexivity.
      destruct o.
      * extern_step; try congruence.
        -- eapply delocation_sim; eauto using approx_restrict with len.
           hnf; intros. lud; eauto.
           eauto using defined_on_update_some, defined_on_incl.
        -- eapply delocation_sim; eauto using approx_restrict with len.
           hnf; intros. lud; eauto.
           eauto using defined_on_update_some, defined_on_incl.
      * no_step.
  - remember (op_eval E e). symmetry in Heqo.
    pose proof Heqo. rewrite EQ in H1.
    destruct o.
    case_eq (val2bool v); intros.
    + one_step. eapply delocation_sim; eauto using defined_on_incl.
    + one_step. eapply delocation_sim; eauto using defined_on_incl.
    + no_step.
  - no_step. simpl. rewrite EQ; eauto.
  - simpl counted in *.
    erewrite get_nth in *; eauto.
    case_eq (omap (op_eval E) Y); intros.
    + inv_get.
      assert (❬Y❭ = ❬x❭). {
        repeat rewrite app_length in H8.
        rewrite map_length in H8. omega.
      }
      inRel_invs. inv H12; simpl in *.
      edestruct (omap_var_defined_on Za); eauto.
      eapply get_in_incl. intros.
      exploit H10; eauto using get_app_right. inv H14; eauto.
      one_step. rewrite omap_app.
      erewrite omap_agree with (g:=op_eval E). rewrite H1.
      simpl. rewrite H9. reflexivity. intros. rewrite EQ; eauto.
      simpl. exploit RD0; eauto; dcr.
      eapply delocation_sim; eauto using approx_restrict with len.
      * rewrite EQ. rewrite List.map_app.
        rewrite update_with_list_app; eauto with len.
        rewrite (omap_self_update _ _ H9); reflexivity.
      * eapply defined_on_update_list; eauto with len.
        eapply defined_on_incl; eauto.
    + no_step.
      rewrite omap_app in def. monad_inv def.
      erewrite omap_agree in H1. erewrite H1 in EQ0. congruence.
      intros. rewrite EQ. reflexivity.
  - one_step.
    assert (length F = length als).
    rewrite <- H7. eauto with len.
    rewrite fst_compileF_eq in H6; eauto with len.
    rewrite <- zip_app in H6; eauto with len.
    eapply delocation_sim; eauto 20 with len.
    + repeat rewrite zip_app; eauto 30 with len.
      econstructor; eauto.
      eapply mutual_approx; eauto 20 using mkBlock_I_i with len.
      * intros; inv_get.
        exploit H8; eauto.
        unfold I.mkBlock. unfold compileF in H15. inv_get. simpl in *.
        eapply blk_approxI; eauto 20 with len.
        intros. invc H15. split; eauto.
        rewrite fst_compileF_eq in H10; eauto with len.
        rewrite <- zip_app in H10; eauto with len.
    + simpl in *. eapply defined_on_incl; eauto.
Qed.

Lemma correct E s ans ans_lv ans_lv'
  (RD: trs nil nil s ans_lv ans)
  (LV': live_sound Imperative nil nil (compile nil s ans) ans_lv')
  (EDEF: defined_on (getAnn ans_lv') E)
  : sim Bisim (nil, E, s) (nil, E, compile nil s ans).
Proof.
  eapply (@delocation_sim nil nil nil nil nil); eauto using @inRel; reflexivity.
Qed.