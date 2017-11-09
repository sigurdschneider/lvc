Require Import Util MapDefined LengthEq Map CSet AutoIndTac AllInRel.
Require Import Var Val Exp Envs IL SimF.

Set Implicit Arguments.
Unset Printing Records.

(** * Program Equivalence *)

Instance SR : PointwiseProofRelationF (nat) := {
   ParamRelFP G Z Z' := ❬Z❭ = ❬Z'❭ /\ ❬Z❭ = G;
   ArgRelFP E E' G VL VL' := VL = VL' /\ length VL = G;
}.

Definition bisimeq r t s s' :=
    forall L L' E, labenv_sim t (sim r) SR (@length _ ⊝ F.block_Z ⊝ L') L L'
            -> ❬L❭ = ❬L'❭
            -> sim r t (L:F.labenv, E, s) (L', E, s').

(** ** Reflexivity *)

Lemma bisimeq_refl s t
  : forall L L' E r,
    labenv_sim t (sim r) SR (@length _ ⊝ block_Z ⊝ L') L L'
    -> sim r t (L, E, s) (L', E, s).
Proof.
  sind s; destruct s; simpl in *; intros.
  - destruct e.
    + eapply (sim_let_op il_statetype_F); eauto.
    + eapply (sim_let_call il_statetype_F); eauto.
  - eapply (sim_cond il_statetype_F); eauto.
  - edestruct (get_dec L' (counted l)) as [[b]|]; [ inv_get | ].
    + eapply labenv_sim_app; eauto.
      simpl.
      intros; split; intros; dcr; inv_get; simpl in *; subst; try cases; eauto with len.
    + pno_step. edestruct H; eauto. len_simpl. inv_get.
  - pno_step.
  - pone_step. left.
    eapply (IH s); eauto with len.
    rewrite !map_app. intros.
    eapply labenv_sim_extension_ptw; eauto with len.
    + intros; hnf; intros; inv_get; eauto.
      simpl in *; dcr; subst. get_functional.
      eapply IH; eauto with len. rewrite !map_app; eauto.
    + hnf; intros; simpl in *; subst; inv_get; simpl; eauto.
Qed.

Lemma labenv_sim_refl t r L
  : sawtooth L
    -> labenv_sim t (sim r) SR (@length _ ⊝ F.block_Z ⊝ L) L L.
Proof.
  intros. hnf; dcr; do 4 try split; eauto with len.
  - intros [] []; intros; simpl in *; subst; inv_get; split; eauto.
  - split. hnf; intros; simpl in *; inv_get; eauto.
    hnf; intros; simpl in *. destruct f, f'; simpl in *; subst.
    get_functional; dcr; subst; inv_get.
    pone_step; simpl; eauto with len.
    left. eapply sim_refl.
Qed.

Lemma labenv_sim_sym L L'
  : labenv_sim Bisim (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L') L L'
    -> labenv_sim Bisim (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L) L' L.
Proof.
  intros []; intros; dcr; do 4 (try split; eauto with len).
  - hnf; intros. destruct f,f'; simpl in *; subst.
    exploit (H2 (LabI n0) (LabI n0)); eauto. simpl in *. dcr; subst; eauto.
    inv_get. eauto.
  - split.
    + hnf; intros; simpl in *; inv_get; eauto.
    + hnf; intros.
      eapply bisim_sym. simpl in *; dcr; subst.
      destruct f, f'; simpl in *; subst.
      eapply H6; eauto. simpl. eauto with len.
Qed.


Lemma bisimeq_sym s1 s2
  : bisimeq bot3 Bisim s1 s2
    -> bisimeq bot3 Bisim s2 s1.
Proof.
  intros. hnf; intros.
  eapply bisim_sym. eapply H; eauto.
  eapply labenv_sim_sym; eauto.
Qed.

Lemma bisimeq_trans t s1 s2 s3
  : bisimeq bot3 t s1 s2
    -> bisimeq bot3 t s2 s3
    -> bisimeq bot3 t s1 s3.
Proof.
  intros. hnf; intros.
  eapply sim_trans with (S2:=F.state). eauto.
  eapply H0; eauto.
  intros. eapply labenv_sim_refl; eauto.
  eapply H1; eauto.
Qed.

Lemma labenv_sim_trans t (L1 L2 L3:F.labenv)
  : labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L2) L1 L2
    -> labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L3) L2 L3
    -> labenv_sim t (sim bot3) SR (@length _ ⊝ F.block_Z ⊝ L3) L1 L3.
Proof.
  intros.
  assert (❬L1❭ = ❬L2❭). {
    destruct H; dcr. rewrite <- H. eauto with len.
  }
  assert (❬L2❭ = ❬L3❭). {
    destruct H0; dcr. rewrite <- H0. eauto with len.
  }
  hnf; dcr; do 4 try split; eauto with len.
  - destruct H, H0; dcr; eauto.
  - eapply H.
  - hnf; intros; simpl in *; destruct f,f'; simpl in *; subst; inv_get.
    simpl. destruct x.
    destruct H as [_ [_ [_ [PA1 _]]]]. destruct H0 as [_ [_ [_ [PA2 _]]]].
    exploit (PA1 (LabI n0) (LabI n0)); eauto; simpl in *; dcr; subst.
    exploit (PA2 (LabI n0) (LabI n0)); eauto; simpl in *; dcr; subst.
    split; omega.
  - split.
    + hnf; intros; simpl in *; inv_get; eauto.
    + hnf; intros; simpl in *. destruct f, f'; simpl in *; subst.
      inv_get; dcr; subst; simpl in *.
      eapply sim_trans with (S2:=F.state).
      eapply labenv_sim_app; eauto.
      Focus 2.
      eapply labenv_sim_app; eauto.
      intros; simpl in *; dcr; repeat subst; repeat get_functional.
      split; intros; eauto with len. cases; split; eauto. congruence.
      intros; simpl in *; dcr. destruct x; simpl in *.
      repeat subst; repeat get_functional.
      split; intros; eauto. eexists; split; eauto. split; eauto with len.
      split; eauto with len. congruence.
      cases; eauto. split; intros. congruence.
      eauto with len.
Qed.
