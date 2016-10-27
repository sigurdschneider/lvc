Require Import List paco2.
Require Import Util IL.
Require Export SmallStepRelations StateType Sim.

Set Implicit Arguments.
Unset Printing Records.

(** * Non-parametric Definitions of Simulation and Bisimulation *)
(** ** Bisimulation *)
(** A characterization of bisimulation equivalence on states;
    works only for internally deterministic semantics. *)

CoInductive bisim {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | BisimSilent (σ1 σ1':S) (σ2 σ2':S') :
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> bisim σ1' σ2'
      -> bisim σ1 σ2
  | BisimExtern (pσ1 σ1:S) (pσ2 σ2:S') :
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ bisim σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ bisim σ1' σ2')
      -> bisim pσ1 pσ2
  | BisimTerm (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> bisim σ1 σ2.

Arguments bisim [S] {H} [S'] {H0} _ _.

(** *** Bisimulation is an reflexive and symmetric *)
Lemma bisim_refl {S} `{StateType S} (σ:S)
      : bisim σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply BisimExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply BisimSilent; eauto using plus2O.
  - eapply BisimTerm; eauto using star2_refl.
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

Lemma bisim_simp t {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), bisim σ σ' -> sim bot3 t σ σ'.
Proof.
  pcofix CIH; intros. invt bisim; pfold; eauto using sim_gen.
  - unfold upaco3. econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr; eauto.
    + intros. edestruct H7; eauto; dcr; eauto.
Qed.

Lemma simp_bisim {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), sim bot3 Bisim σ σ' -> bisim σ σ'.
Proof.
  cofix CIH; intros.
  assert (sim_gen (upaco3 (sim_gen (S:=S) (S':=S')) bot3) Bisim σ σ').
  punfold H1.
  inv H2; pclearbot.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H7; eauto; dcr; pclearbot; eauto.
    + intros. edestruct H8; eauto; dcr; pclearbot; eauto.
  - econstructor 3; eauto.
Qed.

(** *** Transitivity *)

Lemma bisim_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : bisim σ1 σ2
    -> bisim σ2 σ3
    -> bisim σ1 σ3.
Proof.
  intros. eapply simp_bisim.
  eapply bisim_simp in H2.
  eapply bisim_simp in H3.
  eapply (Sim.sim_trans H2 H3).
Qed.

(** ** Simulation *)

CoInductive sim {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | SimSilent (σ1 σ1':S) (σ2 σ2':S') :
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> sim σ1' σ2'
      -> sim σ1 σ2
  | SimExtern (pσ1 σ1:S) (pσ2 σ2:S') :
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ sim σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ sim σ1' σ2')
      -> sim pσ1 pσ2
  | SimTerm (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim σ1 σ2
  | SimErr (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim σ1 σ2.

Arguments bisim [S] {H} [S'] {H0} _ _.

(** *** Simulation is an reflexive *)

Lemma sim_refl {S} `{StateType S} (σ:S)
      : sim σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply SimExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply SimSilent; eauto using plus2O.
  - eapply SimTerm; eauto using star2_refl.
Qed.

(** ** Relationship of simulation to the parametric definition *)

Lemma sim_simp {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), sim σ σ' -> Sim.sim bot3 Sim σ σ'.
Proof.
  pcofix CIH; intros. inv H2; pfold; eauto using sim_gen.
  - econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr; eauto 10.
    + intros. edestruct H7; eauto; dcr; eauto 10.
Qed.

Lemma simp_sim t {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), Sim.sim bot3 t σ σ' -> sim σ σ'.
Proof.
  cofix CIH; intros.
  assert (sim_gen (upaco3 (sim_gen (S:=S) (S':=S')) bot3) t σ σ').
  punfold H1.
  inversion H2; pclearbot.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H7; eauto; dcr; pclearbot; eauto.
    + intros. edestruct H8; eauto; dcr; pclearbot; eauto.
  - econstructor 4; eauto.
  - econstructor 3; eauto.
Qed.

(** *** Transitivity *)

Lemma sim_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim σ1 σ2
    -> sim σ2 σ3
    -> sim σ1 σ3.
Proof.
  intros. eapply simp_sim.
  eapply sim_simp in H2.
  eapply sim_simp in H3.
  eapply (Sim.sim_trans H2 H3).
Qed.

Arguments sim_trans [S1] {H} σ1 [S2] {H0} σ2 [S3] {H1} σ3 _ _.


(** Receptive and determinate according to CompCertTSO (Sevcík 2013) *)

Definition same_call (e e':extern) := extern_fnc e = extern_fnc e' /\ extern_args e = extern_args e'.

Definition receptive S `{StateType S} :=
  forall σ σ' ext, step σ (EvtExtern ext) σ'
              -> forall ext', same_call ext ext' -> exists σ'', step σ (EvtExtern ext') σ''.

Arguments receptive S [H].

Definition determinate S `{StateType S} :=
  forall σ σ' σ'' ext ext', step σ (EvtExtern ext) σ'
              -> step σ (EvtExtern ext') σ'' -> same_call ext ext'.

Arguments determinate S [H].

Lemma bisimExternDet {S} `{StateType S} {S'} `{StateType S'} (pσ1:S) (pσ2:S') (σ1:S) (σ2:S')
      (RCPT:receptive S) (DET:determinate S')
: star2 step pσ1 nil σ1
  -> star2 step pσ2 nil σ2
  -> activated σ1
  -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ bisim σ1' σ2')
  -> bisim pσ1 pσ2.
Proof.
  intros.
  econstructor 2; eauto.
  - inv H3. dcr. edestruct H4; eauto. firstorder.
  - intros. inv H3. dcr. exploit H4; eauto; dcr.
    destruct evt.
    + exploit DET. eauto. eapply H5.
      exploit RCPT; eauto. dcr.
      exploit H4. eapply H11. dcr.
      eexists; split. eapply H11.
      exploit step_externally_determined. Focus 3.
      instantiate (2:=σ2') in H8. rewrite H8. eapply H14.
      eauto. eauto.
    + exfalso. exploit step_internally_deterministic; eauto; dcr. congruence.
Qed.
