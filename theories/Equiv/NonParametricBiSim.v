Require Import List paco2.
Require Import Util IL.
Require Import SmallStepRelations StateType.

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

Lemma bisim_expansion_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S')
  : bisim σ1' σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> bisim σ1 σ2.
Proof.
  intros SIM ? ?.
  inversion SIM; subst;
    eauto using bisim, star2_plus2_plus2_silent, star2_trans_silent.
Qed.

Lemma bisim_reduction_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S')
  : bisim σ1 σ2
    -> star2 step σ1 nil σ1'
    -> bisim σ1' σ2.
Proof.
  intros Sim Star. eapply star2_star2n in Star. destruct Star as [n StarN].
  revert σ1 σ1' σ2 Sim StarN.
  size induction n.
  inv Sim.
  - invc StarN; eauto; relsimpl.
    eapply star2_star2n in H2. destruct H2 as [n' H2].
    edestruct (star2n_reach H9 H2); eauto. eapply H.
    + eapply bisim_expansion_closed; eauto using star2n_star2, plus2_star2.
    + eapply H1; try eapply H9. omega.
      eapply bisim_expansion_closed;
        eauto using star2n_star2, plus2_star2.
  - eapply star2n_star2 in StarN; relsimpl; eauto using bisim.
  - eapply star2n_star2 in StarN; relsimpl; eauto using bisim.
Qed.

Lemma bisim_reduction_closed_both {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S')
  : bisim σ1 σ2
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> bisim σ1' σ2'.
Proof.
  intros. eapply bisim_reduction_closed; eauto.
  eapply bisim_sym. eapply bisim_reduction_closed; eauto.
  eapply bisim_sym. eauto.
Qed.


Lemma bisim_terminate {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2:S2)
: star2 step σ1 nil σ1'
  -> normal2 step σ1'
  -> bisim σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ normal2 step σ2' /\ result σ1' = result σ2'.
Proof.
  intros. general induction H1.
  - inv H3; subst.
    + exfalso. eapply H2. inv H1; do 2 eexists; eauto.
    + exfalso. eapply star2_normal in H1; eauto. subst.
      eapply (activated_normal _ H5); eauto.
    + eapply star2_normal in H4; eauto; subst.
      eexists; split; eauto.
  - destruct y; isabsurd. simpl.
    eapply IHstar2; eauto.
    eapply bisim_reduction_closed; eauto using star2, star2_silent.
Qed.

Lemma bisim_activated {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> bisim σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\
                 (bisim σ1'' σ2''))
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\
                 (bisim σ1' σ2'')).
Proof.
  intros.
  inv H2; subst.
  -  exfalso. edestruct (plus2_destr_nil H3); dcr.
     destruct H1 as [? []].
     exploit (step_internally_deterministic _ _ _ _ H7 H1); dcr; congruence.
  - assert (σ1 = σ0). {
      eapply activated_star_eq; eauto.
    }
    subst σ1.
    eexists σ3; split; eauto.
  - exfalso. refine (activated_normal_star _ H1 _ _); eauto using star2.
Qed.
