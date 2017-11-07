Require Import Util IL SmallStepRelations BlockType.

Lemma plus2_app_shift_F L E f Y σ L1 (SM:smaller L)
  : plus2 step (L, E, stmtApp (LabI f) Y) nil σ
    -> plus2 step (L1 ++ L, E, stmtApp (LabI (❬L1❭ + f)) Y) nil σ.
Proof.
  intros Step. eapply plus2_destr_nil in Step as [? ?]; dcr.
  inv H0; simpl in *.
  eapply star2_plus2.
  + single_step. eapply get_app_right; eauto. reflexivity.
  + simpl. exploit SM; eauto. simpl in *.
    orewrite (❬L1❭ + f - F.block_n blk = ❬L1❭ + (f - F.block_n blk)).
    rewrite drop_app. eauto.
Qed.

Lemma plus2_app_shift_I (L:I.labenv) E f Y σ L1 (SM:smaller L)
  : plus2 step (L, E, stmtApp (LabI f) Y) nil σ
    -> plus2 step (L1 ++ L, E, stmtApp (LabI (❬L1❭ + f)) Y) nil σ.
Proof.
  intros Step. eapply plus2_destr_nil in Step as [? ?]; dcr.
  inv H0; simpl in *.
  eapply star2_plus2.
  + single_step. eapply get_app_right; eauto. reflexivity.
  + simpl. exploit SM; eauto. simpl in *.
    orewrite (❬L1❭ + f - I.block_n blk = ❬L1❭ + (f - I.block_n blk)).
    rewrite drop_app. eauto.
Qed.

Lemma activated_inv_F (L:F.labenv) E s
  : activated (L, E, s)
    -> exists x xf Y s', s = stmtLet x (Call xf Y) s'.
Proof.
  intros [? [? ?]]; invt @step.
  eauto.
Qed.

Lemma activated_inv_I (L:I.labenv) E s
  : activated (L, E, s)
    -> exists x xf Y s', s = stmtLet x (Call xf Y) s'.
Proof.
  intros [? [? ?]]; invt @step.
  eauto.
Qed.

Lemma activated_labenv_F E s (L L':F.labenv)
  : activated (L, E, s)
    -> activated (L', E, s).
Proof.
  intros [? [? ?]]. invt @step.
  do 2 eexists. econstructor; eauto.
  Grab Existential Variables.
  eapply v.
Qed.

Lemma activated_labenv_I E s (L L':I.labenv)
  : activated (L, E, s)
    -> activated (L', E, s).
Proof.
  intros [? [? ?]]. invt @step.
  do 2 eexists. econstructor; eauto.
  Grab Existential Variables.
  eapply v.
Qed.

Lemma normal2_labenv_F E s (L L':F.labenv)
  : normal2 step (L, E, s)
    -> (forall n b b', get L n b -> get L' n b' -> ❬block_Z b❭ = ❬block_Z b'❭)
    -> ❬L'❭ = ❬L❭
    -> normal2 step (L', E, s).
Proof.
  intros. hnf; intros. eapply H.
  destruct H2 as [? [? ?]].
  eexists x.
  inv H2; simpl in *; inv_get; eexists; try single_step.
  econstructor; eauto. exploit H0; eauto. rewrite H4. eauto.
Qed.

Lemma normal2_labenv_I E s (L L':I.labenv)
  : normal2 step (L, E, s)
    -> (forall n b b', get L n b -> get L' n b' -> ❬block_Z b❭ = ❬block_Z b'❭)
    -> ❬L'❭ = ❬L❭
    -> normal2 step (L', E, s).
Proof.
  intros. hnf; intros. eapply H.
  destruct H2 as [? [? ?]].
  eexists x.
  inv H2; simpl in *; inv_get; eexists; try single_step.
  econstructor; eauto. exploit H0; eauto. rewrite H4. eauto.
Qed.
