Require Import List.
Require Export Util Relations Val Exp AutoIndTac Relations2 Events StateType.

Set Implicit Arguments.

Definition activated {S} `{StateType S} (σ:S) :=
  exists ext σ', step σ (EvtExtern ext) σ'.

Lemma activated_star_reach S `{StateType S} (σ σ' σ'':S)
: activated σ''
  -> star2 step σ nil σ''
  -> star2 step σ nil σ'
  -> star2 step σ' nil σ''.
Proof.
  intros. general induction H2; eauto.
  - destruct y, yl; isabsurd. inv H3.
    + exfalso. destruct H1.
      assert (EvtExtern x = EvtTau).
      edestruct H1.
      eapply step_internally_deterministic; eauto. congruence.
    + rewrite H4. destruct y,yl;isabsurd.
      assert (x'0 = x').
      eapply step_internally_deterministic; eauto. subst.
      eauto.
Qed.

Lemma activated_normal S `{StateType S} (σ:S)
  : activated σ
    -> normal2 step σ
    -> False.
Proof.
  intros. inv H0. eapply H1. eexists. eapply H2.
Qed.


Arguments activated_normal [S] [H] σ _ _.

Lemma both_activated S `{StateType S} (σ1 σ2 σ3:S)
: star2 step σ1 nil σ2
  -> star2 step σ1 nil σ3
  -> activated σ2
  -> activated σ3
  -> σ2 = σ3.
Proof.
  intros. general induction H0.
  - inv H1; eauto.
    + exfalso. destruct H2 as [? []].
      destruct y; isabsurd.
      exploit step_internally_deterministic.
      eapply H4. eapply H2. dcr; congruence.
  - inv H2.
    + exfalso. destruct H4 as [? []].
      destruct y; isabsurd.
      exploit step_internally_deterministic.
      eapply H. eapply H4. dcr; congruence.
    + destruct y,y0,yl,yl0; isabsurd.
      eapply IHstar2; eauto.
      assert (x'0 = x').
      eapply step_internally_deterministic; eauto.
      subst; eauto.
Qed.

Lemma activated_star_eq S `{StateType S} (σ1 σ2:S)
: star2 step σ1 nil σ2
  -> activated σ1
  -> σ1 = σ2.
Proof.
  intros. general induction H0; eauto.
  - exfalso. destruct H2 as [? []].
    destruct y; isabsurd.
    exploit step_internally_deterministic.
    eapply H. eapply H2. dcr; congruence.
Qed.


Lemma activated_normal_star S `{StateType S} (σ σ' σ'':S)
  : star2 step σ nil σ'
    -> activated σ'
    -> star2 step σ nil σ''
    -> normal2 step σ''
    -> False.
Proof.
  intros.
  exploit activated_star_reach; eauto. inv X.
  - eauto using activated_normal.
  - eapply H3. do 2 eexists; eauto.
Qed.


Lemma no_activated_tau_step {S} `{StateType S} (σ σ':S)
 :  activated σ
  -> step σ EvtTau σ'
  -> False.
Proof.
  intros. destruct H0 as [? [? ?]].
  eapply step_internally_deterministic in H0; eauto.
  dcr; congruence.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
