Require Import List paco2.
Require Import Util IL.
Require Export SmallStepRelations StateType Sim NonParametricBiSim.

(** ** Relationship of bisimulation to the parametric definition *)

Lemma bisim_simp t {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), bisim σ σ' -> Sim.sim bot3 t σ σ'.
Proof.
  pcofix CIH; intros. invt bisim; pfold; eauto using sim_gen.
  - unfold upaco3. econstructor 2; eauto.
    + intros. edestruct H6; eauto; dcr; eauto.
    + intros. edestruct H7; eauto; dcr; eauto.
Qed.

Lemma simp_bisim {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), Sim.sim bot3 Bisim σ σ' -> bisim σ σ'.
Proof.
  cofix CIH; intros.
  assert (sim_gen (upaco3 (sim_gen (S:=S) (S':=S')) bot3) Bisim σ σ').
  punfold H1.
  inv H2; pclearbot.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + intros. edestruct H7; eauto; dcr; pclearbot; eauto.
    + intros. edestruct H8; eauto; dcr; pclearbot; eauto.
  - exfalso; eauto.
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

(** ** Relationship of simulation to the parametric definition *)

Lemma sim_simp {S} `{StateType S} {S'} `{StateType S'}
  : forall (σ:S) (σ':S'), sim σ σ' -> Sim.sim bot3 Sim σ σ'.
Proof.
  pcofix CIH; intros. inv H2; pfold; eauto using sim_gen.
  - econstructor 2; eauto.
    + simpl. intros; exfalso; eauto.
    + intros. edestruct H6; eauto; dcr; eauto 10.
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
