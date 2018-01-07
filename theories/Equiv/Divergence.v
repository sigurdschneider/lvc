Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType NonParametricBiSim.

Set Implicit Arguments.
Unset Printing Records.

(** * Divergence *)

CoInductive diverges S `{StateType S} : S -> Prop :=
| DivergesI σ σ'
  : step σ EvtTau σ'
    -> diverges σ'
    -> diverges σ.

Lemma diverges_reduction_closed S `{StateType S} (σ σ':S)
: diverges σ -> star2 step σ nil σ'  -> diverges σ'.
Proof.
  intros. general induction H1; eauto using diverges.
  invt diverges; relsimpl. eauto.
Qed.

Lemma diverges_never_activated S `{StateType S} (σ:S)
: activated σ -> diverges σ -> False.
Proof.
  intros. invt diverges; relsimpl.
Qed.

Lemma diverges_never_terminates S `{StateType S} (σ:S)
: normal2 step σ -> diverges σ -> False.
Proof.
  intros. invt diverges; relsimpl.
Qed.

Lemma neither_diverges S `{StateType S} (σ:S)
  (H0 : ~ (exists σ' : S, star2 step σ nil σ' /\ normal2 step σ'))
  (H1 : ~ (exists σ' : S, star2 step σ nil σ' /\ activated σ'))
  : diverges σ.
Proof.
  revert σ H0 H1. cofix f.
  intros. destruct (@step_dec _ H σ).
  - inv H2; dcr.
    destruct x.
    + exfalso. eapply H1; eexists σ; split; eauto using star2_refl.
      do 2 eexists; eauto.
    + econstructor. eauto. eapply f; intro; dcr.
      * eapply H0; eexists; split; eauto. eapply star2_silent; eauto.
      * eapply H1; eexists; split; eauto. eapply star2_silent; eauto.
  - exfalso. eapply H0; eexists σ; split; eauto using star2_refl.
Qed.


(** ** Bisimilarity preserves silent divergence *)

Lemma bisim_sound_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: bisim σ σ' -> diverges σ -> diverges σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1.
  - eapply plus2_destr_nil in H4. dcr.
    econstructor. eauto.
    eapply COH; eauto.
    eapply bisim_reduction_closed_both; try eapply H1;
      eauto using star2_refl, star2_silent.
  - eapply diverges_reduction_closed in H3.
    + exfalso. eapply (diverges_never_activated H5); eauto.
    + eapply H2.
  - eapply diverges_reduction_closed in H4.
    + exfalso. eapply (diverges_never_terminates H6); eauto.
    + eapply H2.
Qed.

(** ** Silently diverging programs are bisimlar *)

Lemma bisim_complete_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: diverges σ -> diverges σ' -> bisim σ σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1; inv H2.
  econstructor. econstructor; eauto. econstructor; eauto.
  eapply COH; eauto.
Qed.

Require Import paco1.

Inductive div_gen S `{StateType S} (r:S -> Prop) : S -> Prop :=
| DivergesIGen σ σ'
  : step σ EvtTau σ'
    -> r σ'
    -> div_gen r σ.

Definition div {S} `{StateType S} r (σ1:S)
  := paco1 (@div_gen S _ ) r σ1.

Hint Unfold div.

Lemma div_diverges {S} `{StateType S} (σ:S)
  : div bot1 σ <-> diverges σ.
Proof.
  split; intros.
  - revert σ H0. cofix CIH. intros.
    destruct H0. destruct SIM.
    econstructor; eauto.
    eapply CIH. edestruct LE; eauto. isabsurd.
  - revert σ H0. pcofix CIH; intros.
    destruct H1. pfold. econstructor; eauto.
Qed.
