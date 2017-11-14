Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType StateTypeProperties.
Require Import NonParametricBiSim Divergence TraceEquiv.

Set Implicit Arguments.
Unset Printing Records.

(** * Trace Equivalence (maximal traces) *)

CoInductive stream (A : Type) : Type :=
| sil : stream A
| sons : A -> stream A -> stream A.

Arguments sil [A].

Infix ":+:" := sons (at level 60, right associativity) : stream_scope.
Delimit Scope stream_scope with stream.

Open Scope stream_scope.

CoInductive coproduces {S} `{StateType S} : S -> stream extevent -> Prop :=
| CoProducesExtern (σ σ' σ'':S) evt L :
    star2 step σ nil σ'
      -> activated σ'
      -> step σ' evt σ''
      -> coproduces σ'' L
      -> coproduces σ (sons (EEvtExtern evt) L)
| CoProducesSilent (σ:S) :
    diverges σ
    -> coproduces σ sil
| CoProducesTerm (σ:S) (σ':S) r
  : result σ' = r
    -> star2 step σ nil σ'
    -> normal2 step σ'
    -> coproduces σ (sons (EEvtTerminate r) sil).

(** ** Several closedness properties *)

Lemma coproduces_reduction_closed_step S `{StateType S} (σ σ':S) L
: coproduces σ L -> step σ EvtTau σ'  -> coproduces σ' L.
Proof.
  intros. inv H0.
  - exploit activated_star_reach. eapply H3. eauto.
    eapply (star2_step EvtTau); eauto. econstructor.
    econstructor. eapply H6. eauto. eauto. eauto.
  - econstructor. eapply diverges_reduction_closed; eauto.
    eapply (star2_step EvtTau); eauto. econstructor.
  - relsimpl.
    econstructor; eauto.
Qed.

Lemma coproduces_reduction_closed S `{StateType S} (σ σ':S) L
: coproduces σ L -> star2 step σ nil σ'  -> coproduces σ' L.
Proof.
  intros. general induction H1; eauto using coproduces. eauto.
  destruct yl, y; simpl in *; try congruence.
  eapply IHstar2; eauto.
  eapply coproduces_reduction_closed_step; eauto.
Qed.

Lemma coproduces_expansion_closed_step S `{StateType S} (σ σ':S) L
: coproduces σ' L -> step σ EvtTau σ'  -> coproduces σ L.
Proof.
  intros. inv H0.
  - econstructor; eauto.
    eapply star2_trans_silent; eauto using star2_silent, star2_refl.
  - econstructor; eauto. econstructor; eauto.
  - econstructor; eauto using star2_silent, star2_refl.
Qed.


(** ** Bisimilarity is sound for maximal traces *)
Lemma bisim_coproduces S `{StateType S} S' `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, coproduces sigma L -> coproduces σ' L.
Proof.
  revert sigma σ'. cofix COH; intros.
  inv H2.
  - assert (bisim σ'0 σ'). {
      eapply bisim_reduction_closed.
      eauto. eauto.
    }
    exploit (bisim_activated H4 H7). dcr.
    edestruct H11. eauto. dcr.
    econstructor; try eapply H10. eauto. eauto.
    eapply COH; eauto.
  - econstructor. eapply (bisim_sound_diverges H1); eauto.
  - exploit (bisim_terminate H4 H5 H1).
    dcr.
    econstructor; eauto.
Qed.

(** ** Prefix trace equivalence coincides with maximal trace equivalence. *)

Lemma produces_coproduces' S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ L <-> prefix σ' L)
  -> (forall T, coproduces σ T -> coproduces σ' T).
Proof.
  revert σ σ'.
  cofix f; intros.
  inv H2.
  - assert (prefix σ (EEvtExtern evt::nil)).
    eapply prefix_star_activated; eauto. econstructor 4.
    eapply H1 in H7.
    eapply prefix_extevent in H7. dcr.
    econstructor. eauto. eauto. eauto. eapply f; try eapply H6.
    eapply (prefix_preserved _ _ _ H1); eauto.
  - exploit (produces_diverges H1 H3).
    econstructor. eauto.
  - assert (prefix σ (EEvtTerminate (result σ'0)::nil)).
    econstructor 3; eauto. eapply H1 in H3.
    eapply prefix_terminates in H3. dcr.
    econstructor 3; eauto.
Qed.

Lemma produces_coproduces S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ L <-> prefix σ' L)
  -> (forall T, coproduces σ T <-> coproduces σ' T).
Proof.
  split; eapply produces_coproduces'; eauto. symmetry; eauto.
Qed.

(** ** Bisimilarity is complete for prefix trace equivalence. *)

CoFixpoint tr S `{StateType S} (σ:S) : stream extevent.
Proof.
  destruct (three_possibilities_strong σ) as [[|]|].
  - destruct s.
    eapply (sons (EEvtTerminate (result x)) sil).
  - destruct s as [? [? ?]]. destruct s. destruct s.
    eapply (sons (EEvtExtern (EvtExtern x1)) (tr S H x2)).
  - eapply sil.
Defined.

Definition stream_match A (s:stream A) :=
  match s with
  | sil => sil
  | sons a b => sons a b
  end.

Lemma stream_id A (s:stream A)
  : s = stream_match s.
Proof.
  destruct s. reflexivity. reflexivity.
Qed.

Lemma coproduces_total S `{StateType S} (σ:S)
  : coproduces σ (tr σ).
Proof.
  revert σ.
  cofix f; intros.
  rewrite stream_id. simpl.
  destruct (three_possibilities_strong σ) as [[|]|].
  - destruct s. econstructor. reflexivity. eauto. eauto.
  - destruct s. destruct s. destruct s. destruct s.
    econstructor; eauto.
    do 2 eexists; eauto.
  - econstructor; eauto.
Qed.

Lemma coproduces_prefix S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : (forall T, coproduces σ T -> coproduces σ' T)
      -> forall L, prefix σ L -> prefix σ' L.
Proof.
  intros. general induction H2.
  - eapply IHprefix; eauto using coproduces_expansion_closed_step.
  - assert (coproduces σ (sons (EEvtExtern evt) (tr σ'))). {
      econstructor 1; eauto using star2_silent, star2_refl.
      eapply coproduces_total.
    }
    eapply H4 in H5. inv H5.
    eapply prefix_star_activated; eauto.
    eapply IHprefix.
    intros.
    assert (coproduces σ (sons (EEvtExtern evt) T)). {
      econstructor 1; eauto using star2_silent, star2_refl.
    }
    eapply H4 in H7. inv H7.
    relsimpl.
    exploit (step_externally_determined _ _ _ _ H11 H17). subst. eauto.
  - assert (coproduces σ (sons (EEvtTerminate (result σ')) sil)). {
      econstructor; eauto.
    }
    eapply H4 in H0. inv H0.
    econstructor 3; eauto.
  - econstructor 4.
Qed.

Lemma coproduces_prefix_iff S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : (forall T, coproduces σ T <-> coproduces σ' T)
    -> forall L, prefix σ L <-> prefix σ' L.
Proof.
  split; eapply coproduces_prefix; firstorder.
Qed.

Lemma coproduces_terminates S `{StateType S} (σ:S) r T
:  coproduces σ (sons (EEvtTerminate r) T)
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = r /\ T = sil.
Proof.
  intros. inv H0.
  - eexists; intuition; eauto.
Qed.

Lemma diverges_coproduces_only_sil S `{StateType S} (σ:S)
: diverges σ -> (forall T, coproduces σ T -> T = sil).
Proof.
  intros. inv H1.
  - exfalso.
    eapply diverges_reduction_closed in H0; eauto.
    eapply @diverges_never_activated in H0; eauto.
  - reflexivity.
  - exfalso.
    eapply diverges_reduction_closed in H0; eauto.
    eapply @diverges_never_terminates in H0; eauto.
Qed.

Lemma coproduces_sil_diverges S `{StateType S} (σ:S)
: coproduces σ sil -> diverges σ.
Proof.
  intros. inv H0. eauto.
Qed.

Lemma coproduces_one_trace_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S') T
: coproduces σ T -> coproduces σ' T -> diverges σ -> diverges σ'.
Proof.
  intros. eapply diverges_coproduces_only_sil in H1; eauto. subst.
  inv H2. eauto.
Qed.

Lemma coproduces_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, coproduces σ L <-> coproduces σ' L)
  -> diverges σ -> diverges σ'.
Proof.
  intros.
  assert (coproduces σ sil). {
    econstructor; eauto.
  }
  eapply H1 in H3.
  inv H3. eauto.
Qed.

Lemma coproduced_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, coproduces σ L <-> coproduces σ' L)
  -> bisim σ σ'.
Proof.
  intros. eapply prefix_bisim.
  eapply coproduces_prefix_iff. eauto.
Qed.
