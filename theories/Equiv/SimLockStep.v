Require Import Util Option AllInRel Get.
Require Export paco2 SmallStepRelations StateType Sim.

Set Implicit Arguments.
Unset Printing Records.

Inductive sim_gen_lock
          {S} `{StateType S} {S'} `{StateType S'} (r: S -> S' -> Prop)  : S -> S' -> Prop :=
  | SimLockSilent (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      step σ1 EvtTau σ1'
      -> step σ2 EvtTau σ2'
      -> r σ1' σ2'
      -> sim_gen_lock r σ1 σ2
  | SimLockExtern (σ1:S) (σ2:S') : (* result σ1 = result σ2 -> *)
      activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ r σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ r σ1' σ2')
      -> sim_gen_lock r σ1 σ2
  | SimLockTerm (σ1:S) (σ2:S')
    : result σ1 = result σ2
      -> normal2 step σ1
      -> normal2 step σ2
      -> sim_gen_lock r σ1 σ2.

Arguments sim_gen_lock [S] {H} [S'] {H0} r _ _.

Hint Constructors sim_gen_lock.

Definition sim_bot {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
  := paco2 (@sim_gen_lock S _ S' _) bot2 σ1 σ2.

Hint Unfold sim_bot.

Definition sim_lock {S} `{StateType S} {S'} `{StateType S'} r (σ1:S) (σ2:S')
  := paco2 (@sim_gen_lock S _ S' _) r σ1 σ2.
Hint Unfold sim_lock.

Lemma sim_gen_lock_mon {S} `{StateType S} {S'} `{StateType S'}
: monotone2 (@sim_gen_lock S _ S' _).
Proof.
  hnf; intros. inv IN; eauto using @sim_gen_lock.
  - econstructor 2; eauto; intros.
    edestruct H3; eauto; dcr. eexists; eauto.
    edestruct H4; eauto; dcr. eexists; eauto.
Qed.

Arguments sim_gen_lock_mon [S] {H} [S'] {H0} [x0] [x1] r r' IN LE.

Hint Resolve sim_gen_lock_mon : paco.

Lemma sim_mon S `{StateType S} S' `{StateType S'}
      (r r':rel2 S (fun (_ : S) => S'))
  : (forall (x1:S) (x2 : S'), r x1 x2 -> r' x1 x2)
    -> forall (x:S) (y : S'), sim_lock r x y -> sim_lock r' x y.
Proof.
  intros. eapply paco2_mon; eauto.
Qed.

Hint Resolve sim_mon.

Lemma sim_bisim {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S') t
      : sim_lock bot2 σ σ' -> sim bot3 t σ σ'.
Proof.
  revert σ σ'. pcofix CIH.
  intros. pinversion H2; subst.
  - pfold. eapply SimSilent; eauto 20 using plus2O.
  - pfold. eapply SimExtern; intros; eauto using star2_refl.
    + edestruct H4; eauto; dcr; pclearbot; eauto 20.
    + edestruct H5; eauto; dcr; pclearbot; eauto 20.
  - pfold. eapply SimTerm; eauto using star2_refl.
Qed.

(** ** Reflexivity, Symmetry *)

Lemma sim_lock_refl {S} `{StateType S} (σ:S) r
      : sim_lock r σ σ.
Proof.
  revert σ.
  pcofix CIH.
  intros. destruct (step_dec σ) as [[[] []]|].
  - pfold. eapply SimLockExtern; intros; eauto using star2_refl; eexists; eauto.
  - pfold. eapply SimLockSilent; eauto using plus2O.
  - pfold. eapply SimLockTerm; eauto using star2_refl.
Qed.


Lemma bisim_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim_lock bot2 σ σ' -> sim_lock bot2 σ' σ.
Proof.
  revert σ σ'. pcofix CIH.
  intros. pinversion H2; subst.
  - pfold. eapply SimLockSilent; eauto using plus2O.
  - pfold. eapply SimLockExtern; intros; eauto using star2_refl.
    + edestruct H5; eauto; dcr; pclearbot; eauto 20.
    + edestruct H4; eauto; dcr; pclearbot; eauto 20.
  - pfold. eapply SimLockTerm; eauto using star2_refl.
Qed.
