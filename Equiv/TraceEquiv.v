Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export EventsActivated StateType paco Equiv Bisim Sim.

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
  destruct yl, y; simpl in *; try congruence.
  inv H2.
  exploit step_internally_deterministic.
  eapply H. eapply H3. dcr; subst.
  eapply IHstar2; eauto.
Qed.

Lemma diverges_never_activated S `{StateType S} (σ:S)
: activated σ -> diverges σ -> False.
Proof.
  intros. inv H0. inv H1. dcr.
  exploit step_internally_deterministic.
  eapply H3. eapply H5. dcr; congruence.
Qed.

Lemma diverges_never_terminates S `{StateType S} (σ:S)
: normal2 step σ -> diverges σ -> False.
Proof.
  intros. inv H1. eapply H0. firstorder.
Qed.

Lemma bisim_sound_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: bisim σ σ' -> diverges σ -> diverges σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1.
  - eapply plus2_destr_nil in H4. dcr.
    econstructor. eauto.
    eapply COH; eauto.
    eapply bisim'_bisim.
    eapply bisim'_reduction_closed.
    eapply bisim_bisim'. eapply H1. econstructor.
    eapply (S_star2 EvtTau); eauto. econstructor.
  - eapply diverges_reduction_closed in H3.
    + exfalso. eapply (diverges_never_activated H5); eauto.
    + eapply H2.
  - eapply diverges_reduction_closed in H4.
    + exfalso. eapply (diverges_never_terminates H6); eauto.
    + eapply H2.
Qed.

Lemma bisim_complete_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: diverges σ -> diverges σ' -> bisim σ σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1; inv H2.
  econstructor. econstructor; eauto. econstructor; eauto.
  eapply COH; eauto.
Qed.


(** * Three equivalent notions of program equivalence **)

(** ** Prefix Trace Equivalence (partial traces) **)

(** A prefix is a list of [extevent] *)

Inductive extevent :=
  | EEvtExtern (evt:event)
  | EEvtTerminate (res:option val).

(** A relation that assigns prefixes to states *)

Inductive prefix {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesPrefixSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> prefix σ' L
      -> prefix σ  L
  | producesPrefixExtern (σ:S) (σ':S) evt L :
      activated σ
      -> step σ evt σ'
      -> prefix σ' L
      -> prefix σ (EEvtExtern evt::L)
  | producesPrefixTerm (σ:S) (σ':S) r
    : result σ' = r
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> prefix σ (EEvtTerminate r::nil)
  | producesPrefixPrefix (σ:S)
    : prefix σ nil.

(** *** Closedness under silent reduction/expansion *)

Lemma prefix_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   prefix σ' L -> prefix σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma prefix_star2_silent' {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   prefix σ L -> prefix σ' L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    eapply IHstar2; eauto.
    inv H2.
    + exploit step_internally_deterministic. eapply H. eapply H3.
      dcr; subst. eauto.
    + exfalso. inv H3; dcr.
      exploit step_internally_deterministic. eapply H. eapply H7. dcr; congruence.
    + exploit star2_reach_silent_step; eauto. eapply H1.
      destruct X; subst. exfalso. eapply H5; firstorder.
      econstructor 3; eauto.
    + econstructor 4.
Qed.

(** *** Bisimilarity is sound for prefix inclusion *)

Lemma bisim_prefix' {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
: bisim sigma σ' -> forall L, prefix sigma L -> prefix σ' L.
Proof.
  intros. general induction H2.
  - eapply bisim_bisim' in H3.
    eapply IHprefix; eauto.
    eapply bisim'_bisim. eapply bisim'_reduction_closed_1; eauto.
    eapply (S_star2 _ _ H0). eapply star2_refl.
  - eapply bisim_bisim' in H4.
    eapply bisim'_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    destruct evt.
    + eapply prefix_star2_silent; eauto.
      edestruct H6; eauto. destruct H8.
      econstructor 2. eauto. eapply H8.
      eapply IHprefix; eauto.
      eapply bisim'_bisim. eapply H9.
    + exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply bisim_bisim' in H4. eapply bisim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 3; [ | eauto | eauto]. congruence.
  - econstructor 4.
Qed.

Lemma bisim_prefix {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, prefix sigma L <-> prefix σ' L.
Proof.
  split; eapply bisim_prefix'; eauto.
  eapply bisim_sym; eauto.
Qed.

(** *** The only prefix is empty if and only if the state diverges *)

Lemma produces_only_nil_diverges S `{StateType S} (σ:S)
: (forall L, prefix σ L -> L = nil) -> diverges σ.
Proof.
  revert σ. cofix f; intros.
  destruct (@step_dec _ H σ).
  - destruct H1; dcr. destruct x.
    + exfalso. exploit H0. econstructor 2; try eapply H2.
      eexists; eauto.
      econstructor 4. congruence.
    + econstructor. eauto. eapply f.
      intros. eapply H0.
      eapply prefix_star2_silent.
      eapply (S_star2 EvtTau); eauto. econstructor. eauto.
  - exfalso.
    exploit H0. econstructor 3. reflexivity. econstructor. eauto. congruence.
Qed.

Lemma prefix_extevent S `{StateType S} (σ:S) evt L
: prefix σ (EEvtExtern evt::L)
  -> exists σ', star2 step σ nil σ'
          /\ activated σ'
          /\ exists σ'', step σ' evt σ'' /\ prefix σ'' L.
Proof.
  intros. general induction H0.
  - edestruct IHprefix. reflexivity. dcr.
    eexists x; intuition. eapply (S_star2 EvtTau); eauto.
    eexists; eauto.
  - eexists σ; intuition. econstructor. eexists; eauto.
Qed.

Lemma prefix_terminates S `{StateType S} (σ:S) r L
:  prefix σ (EEvtTerminate r::L)
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = r /\ L = nil.
Proof.
  intros. general induction H0.
  - edestruct IHprefix. reflexivity.
    eexists x; dcr; intuition. eapply (S_star2 EvtTau); eauto.
  - eexists; intuition; eauto.
Qed.

Lemma diverges_produces_only_nil S `{StateType S} S' `{StateType S'} (σ:S)
: diverges σ -> (forall L, prefix σ L -> L = nil).
Proof.
  intros. general induction L; eauto.
  destruct a.
  - eapply prefix_extevent in H2; dcr.
    exfalso. eapply diverges_never_activated; eauto.
    eapply diverges_reduction_closed; eauto.
  - eapply prefix_terminates in H2; dcr; subst.
    exfalso. eapply diverges_never_terminates; eauto using diverges_reduction_closed.
Qed.

(** *** Prefix Equivalence is sound for divergence *)

Lemma produces_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ L <-> prefix σ' L)
  -> diverges σ -> diverges σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  inv H2.
  edestruct (@step_dec _ H0 σ').
  inv H5; dcr.
  destruct x.
  - exfalso.
    pose proof (diverges_produces_only_nil H2).
    exploit H6. eapply H1.
    econstructor 2. eexists; eauto. eauto. econstructor 4.
    congruence.
  - econstructor. eapply H7.
    eapply f; intros; try eapply H4.
    split; intros.
    + eapply prefix_star2_silent'.
      eapply (S_star2 EvtTau). eapply H7. econstructor.
      eapply H1. econstructor; eauto.
    + eapply prefix_star2_silent'.
      eapply (S_star2 EvtTau). eapply H3. econstructor.
      eapply H1. econstructor; eauto.
  - exfalso.
    exploit (diverges_produces_only_nil H2).
    eapply H1. econstructor 3; eauto. constructor.
    congruence.
Qed.

(** *** Several closedness properties *)

Lemma prefix_star_activated S `{StateType S} (σ1 σ1' σ1'':S) evt L
: star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' evt σ1''
  -> prefix σ1'' L
  -> prefix σ1 (EEvtExtern evt::L).
Proof.
  intros. general induction H0.
  - econstructor 2; eauto.
  - destruct y, yl; simpl in *; try congruence.
    econstructor; eauto.
Qed.

Lemma prefix_preserved' S `{StateType S} S' `{StateType S'} (σ1 σ1' σ1'':S) (σ2 σ2' σ2'':S') evt
: (forall L : list extevent, prefix σ1 L <-> prefix σ2 L)
  -> star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' evt σ1''
  -> star2 step σ2 nil σ2'
  -> activated σ2'
  -> step σ2' evt σ2''
  -> forall L, prefix σ1'' L -> prefix σ2'' L.
Proof.
  intros.
  - exploit (prefix_star_activated _ H2 H3 H4 H8).
    eapply H1 in X.
    eapply prefix_extevent in X. dcr.
    exploit both_activated. eapply H10. eapply H5. eauto. eauto. subst.
    assert (x0 = σ2''). eapply step_externally_determined; eauto. subst; eauto.
Qed.

Lemma prefix_preserved S `{StateType S} S' `{StateType S'} (σ1 σ1' σ1'':S) (σ2 σ2' σ2'':S') evt
:
  (forall L : list extevent, prefix σ1 L <-> prefix σ2 L)
  -> star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' evt σ1''
  -> star2 step σ2 nil σ2'
  -> activated σ2'
  -> step σ2' evt σ2''
  -> forall L, prefix σ1'' L <-> prefix σ2'' L.
Proof.
  split; intros.
  eapply (prefix_preserved' _ _ H1); eauto.
  symmetry in H1.
  eapply (prefix_preserved' _ _ H1); eauto.
Qed.

Lemma produces_silent_closed {S} `{StateType S}  S' `{StateType S'}  (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, prefix σ1 L <-> prefix σ2 L)
  -> (forall L, prefix σ1' L <-> prefix σ2' L).
Proof.
  split; intros.
  - eapply prefix_star2_silent'; eauto. eapply H3.
    eapply prefix_star2_silent; eauto.
  - eapply prefix_star2_silent'; eauto. eapply H3.
    eapply prefix_star2_silent; eauto.
Qed.

(** ** Trace Equivalence (maximal traces) *)

CoInductive stream (A : Type) : Type :=
| sil : stream A
| sons : A -> stream A -> stream A.

Arguments sil [A].

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

(** *** Several closedness properties *)

Lemma coproduces_reduction_closed_step S `{StateType S} (σ σ':S) L
: coproduces σ L -> step σ EvtTau σ'  -> coproduces σ' L.
Proof.
  intros. inv H0.
  - exploit activated_star_reach. eapply H3. eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
    econstructor. eapply X. eauto. eauto. eauto.
  - econstructor. eapply diverges_reduction_closed; eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
  - exploit star2_reach_normal. eauto.
    eapply (S_star2 EvtTau); eauto. econstructor.
    eapply H. eauto.
    econstructor; try eapply X. eauto. eauto.
Qed.

Lemma coproduces_reduction_closed S `{StateType S} (σ σ':S) L
: coproduces σ L -> star2 step σ nil σ'  -> coproduces σ' L.
Proof.
  intros. general induction H1; eauto using coproduces. eauto.
  destruct yl, y; simpl in *; try congruence.
  eapply IHstar2; eauto.
  eapply coproduces_reduction_closed_step; eauto.
Qed.

(** *** Bisimilarity is sound for maximal traces *)

Lemma bisim_coproduces S `{StateType S} S' `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, coproduces sigma L -> coproduces σ' L.
Proof.
  revert sigma σ'. cofix COH; intros.
  inv H2.
  - assert (bisim' σ'0 σ').
    eapply bisim'_reduction_closed. eapply (bisim_bisim' H1).
    eauto. econstructor.
    exploit (bisim'_activated H4 H7). dcr.
    edestruct H10. eauto. dcr.
    econstructor; try eapply H8. eauto. eapply H11.
    eapply COH; eauto.
    destruct H11.
    eapply bisim'_bisim. eapply H13.
  - econstructor. eapply (bisim_sound_diverges H1); eauto.
  - exploit (bisim'_terminate H4 H5 (bisim_bisim' H1)).
    dcr.
    econstructor; eauto.
Qed.

(** *** Prefix trace equivalence coincides with maximal trace equivalence. *)

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

Require Import Classical_Prop.

Lemma three_possibilities S `{StateType S} (σ:S)
: (exists σ', star2 step σ nil σ' /\ normal2 step σ')
  \/ (exists σ', star2 step σ nil σ' /\ activated σ')
  \/ diverges σ.
Proof.
  destruct (classic (exists σ' : S, star2 step σ nil σ' /\ normal2 step σ')); intuition; right.
  destruct (classic (exists σ' : S, star2 step σ nil σ' /\ activated σ')); intuition; right.
  revert σ H0 H1. cofix f.
  intros. destruct (@step_dec _ H σ). inv H2; dcr.
  destruct x.
  - exfalso. eapply H1; eexists σ; intuition.
    econstructor. do 2 eexists; eauto.
  - econstructor. eauto. eapply f; intros; dcr.
    eapply H0; eexists; split; eauto. eapply (S_star2 EvtTau); eauto.
    eapply H1; eexists; split; eauto. eapply (S_star2 EvtTau); eauto.
  - exfalso. eapply H0; eexists σ; intuition. econstructor.
Qed.

Lemma prefix_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ L <-> prefix σ' L)
  -> bisim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  destruct (three_possibilities σ) as [A|[A|A]].
  - dcr. assert (prefix σ (EEvtTerminate (result x)::nil)).
    econstructor 3; eauto.
    eapply H1 in H2.
    eapply prefix_terminates in H2. dcr.
    econstructor 3; eauto.
  - dcr. inv H4; dcr.
    assert (prefix x1 nil) by econstructor 4.
    exploit (prefix_star_activated _ H3 H4 H5 H2).
    eapply H1 in X.
    eapply prefix_extevent in X. dcr.
    econstructor 2; eauto.
    + intros.
      assert (B:prefix x (EEvtExtern evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      pose proof H1.
      eapply produces_silent_closed in H11; eauto.
      eapply H11 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H9 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply prefix_preserved; eauto.
    + intros.
      assert (B:prefix x2 (EEvtExtern evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      pose proof H1.
      eapply produces_silent_closed in H11; eauto.
      eapply H11 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H5 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply prefix_preserved; eauto.
  - assert (diverges σ').
    eapply (produces_diverges H1); eauto.
    eapply bisim_complete_diverges; eauto.
Qed.





(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
