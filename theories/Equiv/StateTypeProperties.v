Require Import StateType SmallStepRelations Divergence.
Require Import Classical_Prop Coq.Logic.Epsilon.
Set Implicit Arguments.

Lemma three_possibilities S `{StateType S} (σ:S)
: (exists σ', star2 step σ nil σ' /\ normal2 step σ')
  \/ (exists σ', star2 step σ nil σ' /\ activated σ')
  \/ diverges σ.
Proof.
  destruct (classic (exists σ' : S, star2 step σ nil σ' /\ normal2 step σ')); eauto; right.
  destruct (classic (exists σ' : S, star2 step σ nil σ' /\ activated σ')); eauto; right.
  eapply neither_diverges; eauto.
Qed.

Require Import Coq.Logic.ClassicalDescription.

Lemma three_possibilities_strong S `{StateType S} (σ:S)
: { σ' : S | star2 step σ nil σ' /\ normal2 step σ' }
  + { σ' : S & { p : star2 step σ nil σ' &
                     { ext : extern & { σ'' : S | step σ' (EvtExtern ext) σ'' } } } }
  + diverges σ.
Proof.
  destruct (excluded_middle_informative (exists σ' : S, star2 step σ nil σ' /\ normal2 step σ')); eauto.
  - eapply constructive_indefinite_description in e. eauto.
  - destruct (excluded_middle_informative (exists σ' : S, star2 step σ nil σ' /\ activated σ')).
    + eapply constructive_indefinite_description in e.
      left; right. destruct e. eexists x; eauto. dcr; eauto.
      eapply constructive_indefinite_description in H1. destruct H1.
      eapply constructive_indefinite_description in e. destruct e.
      eauto.
    + right. revert σ n n0. cofix f.
      intros. destruct (@step_dec _ H σ).
      * inv H0; dcr.
        destruct x.
        -- exfalso. eapply n0; eexists σ; split; eauto using star2_refl.
           do 2 eexists; eauto.
        -- econstructor. eauto. eapply f; intro; dcr.
           ++ eapply n; eexists; split; eauto. eapply star2_silent; eauto.
           ++ eapply n0; eexists; split; eauto. eapply star2_silent; eauto.
      * exfalso. eapply n; eexists σ; split; eauto using star2_refl.
Qed.
