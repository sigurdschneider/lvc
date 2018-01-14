Require Import List.
Require Import Util Var Val Exp Envs Map CSet AutoIndTac IL AllInRel.
Require Import SmallStepRelations StateType NonParametricBiSim.
Require Import Divergence StateTypeProperties.

Set Implicit Arguments.
Unset Printing Records.

(** * Prefix Trace Equivalence (partial traces) **)

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

Definition prefix_eq {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S') :=
  forall L, prefix σ L <-> prefix σ' L.

(* Only prove it of one StateType *)
Instance prefix_eq_Equivalence {S} `{StateType S}
  : Equivalence prefix_eq.
Proof.
  econstructor.
  - hnf. intros; hnf. split; eauto.
  - split; intros.
    + eapply H0; eauto.
    + eapply H0; eauto.
  - unfold Transitive, prefix_eq; firstorder.
Qed.

(** ***Closedness under silent reduction/expansion *)

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
    + relsimpl; eauto.
    + relsimpl.
    + exploit star2_reach_silent_step; eauto. eapply H.
      destruct H3; subst. exfalso. eapply H5; firstorder.
      econstructor 3; eauto.
    + econstructor 4.
Qed.

(** ** Bisimilarity is sound for prefix inclusion *)

Lemma bisim_prefix' {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
: bisim sigma σ' -> forall L, prefix sigma L -> prefix σ' L.
Proof.
  intros. general induction H2.
  - eapply IHprefix; eauto.
    eapply bisim_reduction_closed; eauto.
    eapply (star2_step _ _ H0). eapply star2_refl.
  - eapply bisim_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    destruct evt.
    + eapply prefix_star2_silent; eauto.
      edestruct H6; eauto. destruct H8.
      econstructor 2. eauto. eapply H8.
      eapply IHprefix; eauto.
    + exfalso; eapply (no_activated_tau_step _ H0 H1); eauto.
  - eapply bisim_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 3; [ | eauto | eauto]. congruence.
  - econstructor 4.
Qed.

Lemma bisim_prefix {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, prefix sigma L <-> prefix σ' L.
Proof.
  split; eapply bisim_prefix'; eauto.
  eapply NonParametricBiSim.bisim_sym; eauto.
Qed.

(** ** The only prefix is empty if and only if the state diverges *)

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
      eapply star2_silent; eauto. econstructor. eauto.
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
    eexists x; split; eauto using star2_silent.
  - eexists σ; eauto using star2.
Qed.

Lemma prefix_terminates S `{StateType S} (σ:S) r L
:  prefix σ (EEvtTerminate r::L)
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = r /\ L = nil.
Proof.
  intros. general induction H0.
  - edestruct IHprefix. reflexivity.
    eexists x; dcr; subst. eauto using star2_silent.
  - eexists; intuition; eauto.
Qed.

Lemma prefix_terminates_incl S `{StateType S} S' `{StateType S'} (σ σ1:S) (σ':S') r
  :  star2 step σ nil σ1
     -> normal2 step σ1
     -> result σ1 = r
     -> (forall L, prefix σ L -> prefix σ' L)
     -> exists σ2, star2 step σ' nil σ2 /\ normal2 step σ2 /\ result σ2 = r.
Proof.
  intros.
  edestruct prefix_terminates.
  - eapply H4. econstructor 3; eauto.
  - dcr; eauto.
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

Lemma diverges_iff_nil S `{StateType S} S' `{StateType S'} (σ:S)
: diverges σ <-> (forall L, prefix σ L -> L = nil).
Proof.
  split.
  - eapply diverges_produces_only_nil; eauto.
  - eapply produces_only_nil_diverges; eauto.
Qed.

(** ** Prefix Equivalence is sound for divergence *)

Lemma produces_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ' L -> prefix σ L)
  -> diverges σ -> diverges σ'.
Proof.
  intros.
  pose proof (diverges_produces_only_nil H2).
  eapply produces_only_nil_diverges.
  intros. eapply H3. eauto.
Qed.

(** ** Several closedness properties *)

Lemma prefix_star_activated S `{StateType S} (σ1 σ1' σ1'':S) evt L
: star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' evt σ1''
  -> prefix σ1'' L
  -> prefix σ1 (EEvtExtern evt::L).
Proof.
  intros. general induction H0.
  - econstructor 2; eauto.
  - relsimpl.
    econstructor; eauto.
Qed.

Lemma prefix_preserved' S `{StateType S} S' `{StateType S'} (σ1 σ1' σ1'':S) (σ2 σ2' σ2'':S') evt
: (forall L : list extevent, prefix σ1 L -> prefix σ2 L)
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
    eapply H1 in H9.
    eapply prefix_extevent in H9. dcr.
    exploit both_activated. eapply H11. eapply H5. eauto. eauto. subst.
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
  split.
  - eapply prefix_preserved'; try eassumption. firstorder.
  - eapply prefix_preserved'; try eassumption. firstorder.
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

Lemma prefix_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, prefix σ L <-> prefix σ' L)
  -> bisim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  destruct (three_possibilities σ) as [A|[A|A]].
  - dcr.
    assert (prefix σ (EEvtTerminate (result x)::nil)). {
      econstructor 3; eauto.
    }
    eapply H1 in H2.
    eapply prefix_terminates in H2. dcr.
    econstructor 3; eauto.
  - dcr. inv H4; dcr.
    assert (prefix x1 nil) by econstructor 4.
    exploit (prefix_star_activated _ H3 H4 H5 H2).
    eapply H1 in H6.
    eapply prefix_extevent in H6. dcr.
    econstructor 2; eauto.
    + intros.
      assert (B:prefix x (EEvtExtern evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      pose proof H1.
      eapply produces_silent_closed in H9; eauto.
      eapply H9 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H10 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply prefix_preserved; eauto.
    + intros.
      assert (B:prefix x2 (EEvtExtern evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      pose proof H1.
      eapply produces_silent_closed in H9; eauto.
      eapply H9 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H5 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply prefix_preserved; eauto.
  - assert (diverges σ').
    eapply (produces_diverges ltac:(eapply H1)); eauto.
    eapply bisim_complete_diverges; eauto.
Qed.

Lemma bisim_prefix_iff S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
  : prefix_eq σ σ'
    <-> bisim σ σ'.
Proof.
  split; intros.
  - eapply prefix_bisim; eauto.
  - split.
    + eapply bisim_prefix, bisim_sym; eauto.
    + eapply bisim_prefix; eauto.
Qed.