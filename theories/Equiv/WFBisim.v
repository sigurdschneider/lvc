Require Import List paco2.
Require Import Util IL.
Require Export SmallStepRelations StateType Sim.
Require Import Terminating.
Require Import NonParametricBiSim.

Set Implicit Arguments.
Unset Printing Records.

CoInductive indexBisim X R `{Terminating X R}
            {S} `{StateType S} {S'} `{StateType S'}  : X -> S -> S' -> Prop :=
  | IndexBisimSilent x (σ1 σ1':S) (σ2 σ2':S') :
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> indexBisim x σ1' σ2'
      -> indexBisim x σ1 σ2
  | IndexBisimExtern x (pσ1 σ1:S) (pσ2 σ2:S') :
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ indexBisim x σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ indexBisim x σ1' σ2')
      -> indexBisim x pσ1 pσ2
  | IndexBisimTerm x (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> indexBisim x σ1 σ2
  | IndexBisimStutter x y (σ1 σ1':S) (σ2 σ2':S')
    : R x y
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> indexBisim y σ1' σ2'
      -> indexBisim x σ1 σ2.

Arguments indexBisim [X] [R] {H} [S] {H0} [S'] {H1} _ _ _.

(** *** Bisimulation is an reflexive and symmetric *)
Lemma bisim_refl {S} `{StateType S} (σ:S) X R `{Terminating X R} (x:X)
      : indexBisim x σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply IndexBisimExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply IndexBisimSilent; eauto using plus2O.
  - eapply IndexBisimTerm; eauto using star2_refl.
Qed.

Lemma bisim_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
      : bisim σ σ' -> bisim σ' σ.
Proof.
  revert σ σ'. cofix; intros.
  inv H1.
  - eapply BisimSilent; eauto.
  - eapply BisimExtern; eauto; intros.
    edestruct H7; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.
  - eapply BisimTerm; eauto using star2_refl.
Qed.

(** ** Relationship of bisimulation to the parametric definition *)

Lemma bisim_indexBisim {S} `{StateType S} {S'} `{StateType S'} X R `{Terminating X R} x
  : forall (σ:S) (σ':S'), bisim σ σ' -> indexBisim x σ σ'.
Proof.
  cofix CIH; intros. invt bisim.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H7; eauto; dcr; eauto.
    + intros. edestruct H8; eauto; dcr; eauto.
  - econstructor 3; eauto.
Qed.

Lemma indexBisim_inv {S} `{StateType S} {S'} `{StateType S'} X R `{Terminating X R}
      x (σ1:S) (σ2:S')
  : indexBisim x σ1 σ2
    -> (exists x σ1' σ2',
          plus2 step σ1 nil σ1' /\
          plus2 step σ2 nil σ2' /\
          indexBisim x σ1' σ2')
      \/ (exists x σ1' σ2',
            star2 step σ1 nil σ1' /\
            star2 step σ2 nil σ2' /\
            activated σ1' /\
            activated σ2' /\
            (forall evt σ1'', step σ1' evt σ1'' ->
                         exists σ2'', step σ2' evt σ2'' /\ indexBisim x σ1'' σ2'') /\
            (forall evt σ2'', step σ2' evt σ2'' ->
                         exists σ1'', step σ1' evt σ1'' /\ indexBisim x σ1'' σ2''))
      \/ (exists σ1' σ2',
            star2 step σ1 nil σ1' /\
            star2 step σ2 nil σ2' /\
            result σ1' = result σ2' /\
            normal2 step σ1' /\
            normal2 step σ2').
Proof.
  intros.
  pose proof (H1 x). general induction H3.
  inv H4; eauto 20.
  edestruct H0 as [? | [? | ?]]; eauto; dcr.
  - left. eexists x0, x1, x2.
    eauto using star2_plus2_plus2_silent.
  - right; left.
    eexists x0, x1, x2;
      repeat split; eauto using star2_trans_silent.
  - right; right.
    eexists x0, x1;
      repeat split; eauto using star2_trans_silent.
Qed.

Lemma indexBisim_bisim {S} `{StateType S} {S'} `{StateType S'} X R `{Terminating X R} x
  : forall (σ:S) (σ':S'), indexBisim x σ σ' -> bisim σ σ'.
Proof.
  revert x. cofix CIH; intros.
  eapply indexBisim_inv in H2.
  destruct H2 as [|[|]]; dcr.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H7; eauto; dcr; eauto.
    + intros. edestruct H9; eauto; dcr; eauto.
  - econstructor 3; eauto.
Qed.
