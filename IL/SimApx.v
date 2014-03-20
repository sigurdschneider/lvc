Require Import List Infra.Relations.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL Sim.

Set Implicit Arguments.
Unset Printing Records.

CoInductive simapx {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | simS (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *) plus step σ1 σ1' -> plus step σ2 σ2' -> simapx σ1' σ2' -> simapx σ1 σ2
  | simE (σ1 σ1':S) (σ2 σ2':S') 
    : result σ1' = result σ2'
      -> star step σ1 σ1'
      -> star step σ2 σ2'
      -> normal step σ1'
      -> normal step σ2' -> simapx σ1 σ2
  | simErr (σ1 σ1':S) (σ2:S') 
    : result σ1' = None
      -> star step σ1 σ1'
      -> normal step σ1' -> simapx σ1 σ2.

(** Simulation is an equivalence relation *)
Lemma simapx_refl {S} `{StateType S} (σ:S)
      : simapx σ σ.
Proof.
  revert σ. cofix.  
  intros. destruct (step_dec σ). inv H0.
  eapply simS; eauto using plusO.
  eapply simE; eauto using star_refl.
Qed.

(** Transitivity is not obvious *)

Definition apxbehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') :=
  (diverges step σ1 -> diverges step σ2) 
  /\ (forall v, terminatesWith σ1 (Some v) -> terminatesWith σ2 (Some v)).

Lemma apxbehave_reduction_closed {S} `{StateType S} {S'} `{StateType S'} 
      (σ1 σ1':S) (σ2 σ2':S')
  : apxbehave σ1 σ2
    -> star step σ1 σ1' 
    -> star step σ2 σ2'
    -> apxbehave σ1' σ2'.
Proof.
  intros.
  destruct H1. split; intros.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
Qed.

Lemma simapx_codiverge' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> diverges step σ1 -> diverges (plus step) σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros.
  inv H1. eapply DivergesI; eauto. eapply simapx_codiverge'; eauto.
  eapply div_ext_plus; eauto. eapply step_functional.
  exfalso. eapply normal_terminates in H6. 
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
  exfalso. eapply normal_terminates in H5. 
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
Qed.

Lemma simapx_codiverge {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> diverges step σ1 -> diverges step σ2.
Proof.
  intros. eapply div_plus. eapply (simapx_codiverge' H1 H2).
Qed.

Lemma codiverge_simapx {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: diverges step σ1 -> diverges step σ2 -> simapx σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1; inv H2.
  eapply simS; eauto using plus.
Qed.

Lemma simapx_step_closed {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2:S')
 : simapx σ1 σ2 -> step σ1 σ1' -> simapx σ1' σ2.
Proof.
  revert σ1 σ1' σ2. cofix; intros.
  inv H1. destruct H3. inv H5. 
  eapply simS. rewrite step_functional; eauto.
  eapply plus_trans; eauto. eassumption.
  eapply simE. eauto. rewrite step_functional; eauto. 
  eapply star_trans; eauto using plus_star.
  eauto. eauto. 
  eapply simErr; eauto. rewrite step_functional; eauto.
  eapply simS. rewrite step_functional; eauto. eassumption. eauto. 
  eapply simE. eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto. eauto. eauto. eauto.
  eapply simErr; eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto.
Qed.

Lemma simapx_coterminatesWith {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 -> forall v, terminatesWith σ1 (Some v) -> terminatesWith σ2 (Some v).
Proof.
  intros. general induction H2. rewrite Heqo.
  + inv H3. exfalso. eapply H1. destruct H0; firstorder. 
    destruct H4. eapply terminatesWith_star; eauto. econstructor; eauto.
    congruence. admit. admit.
  + eapply IHterminatesWith. 
    pose proof (simapx_step_closed _ H3 H0). eauto. reflexivity.
Qed.

Lemma coterminatesWith_simapx {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') v
: terminatesWith σ1 v -> terminatesWith σ2 v -> simapx σ1 σ2.
Proof. 
  intros. 
  eapply terminatesWith_star_normal in H1.
  eapply terminatesWith_star_normal in H2.
  destruct H1, H2; dcr.
  eapply simE; eauto using star. rewrite H6, H8; reflexivity.
Qed.
(*
Lemma sim_apxbehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: simapx σ1 σ2 <-> apxbehave σ1 σ2.
Proof.
  split. unfold cobehave; split; intros.
  + pose proof (simapx_codiverge H1 H2); eauto.
  + eapply (simapx_coterminatesWith H1); eassumption.
  + revert_all. cofix; intros. 
    destruct (step_dec σ1) as [[]|]; destruct (step_dec σ2) as [[]|].
    - eapply simS; try eapply plusO; try eassumption. 
      eapply sim_apxbehave. eapply apxbehave_reduction_closed; eauto using star.
    - pose proof (normal_terminates H3).
      eapply terminatesWith_terminates in H4; destruct H4. 
      destruct x0.
      assert (terminatesWith σ1 (Some v)). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x0). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
Qed.

Lemma cobehave_trans {S} `{StateType S} {S'} `{StateType S'} {S''} `{StateType S''} 
(σ1:S) (σ2:S') (σ3:S'')
: cobehave σ1 σ2 -> cobehave σ2 σ3 -> cobehave σ1 σ3.
Proof. 
  unfold cobehave; intros. destruct H2, H3; firstorder.
Qed.

Lemma sim_trans {S1} `{StateType S1} {S2} `{StateType S2} {S3} `{StateType S3}
      (σ1:S1) (σ2:S2) (σ3:S3)
  : sim σ1 σ2 -> sim σ2 σ3 -> sim σ1 σ3.
Proof.
  intros. 
  rewrite sim_cobehave in H2. 
  rewrite sim_cobehave in H3. 
  rewrite sim_cobehave. 
  pose proof (cobehave_trans H2 H3); eauto.
Qed.
*)

(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lyn")) ***
*** End: ***
*)

