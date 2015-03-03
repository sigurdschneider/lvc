Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export EventsActivated StateType paco Equiv Bisim Sim.

Require Import TraceEquiv.

Set Implicit Arguments.
Unset Printing Records.

Inductive produces_prefix {S} `{StateType S} : S -> list extevent -> Prop :=
  | producesPrefixSilent (σ:S) (σ':S) L :
      step σ EvtTau σ'
      -> produces_prefix σ' L
      -> produces_prefix σ  L
  | producesPrefixExtern (σ:S) (σ':S) ext L :
      activated σ
      -> step σ (EvtExtern ext) σ'
      -> produces_prefix σ' L
      -> produces_prefix σ (EEvtExtern (EvtExtern ext)::L)
  | producesPrefixTerm (σ:S) (σ':S) r
    : result σ' = Some r
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces_prefix σ (EEvtTerminate (Some r)::nil)
  | producesPrefixCrash (σ:S) (σ':S) L
    : result σ' = None
      -> star2 step σ nil σ'
      -> normal2 step σ'
      -> produces_prefix σ L
  | producesPrefixPrefix (σ:S)
    : produces_prefix σ nil.

Lemma produces_prefix_star2_silent {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces_prefix σ' L -> produces_prefix σ L.
Proof.
  intros. general induction H0; eauto.
  - destruct yl, y; simpl in *; try congruence.
    econstructor 1; eauto.
Qed.

Lemma star2_reach_silent_step (X : Type) (R:X -> event -> X -> Prop) (x y z : X)
: R x EvtTau y
  -> star2 R x nil z
  -> internally_deterministic R
  -> x = z \/ star2 R y nil z.
Proof.
  intros. inv H0; eauto.
  exploit H1; eauto. dcr; subst; eauto.
Qed.


Lemma produces_prefix_star2_silent' {S} `{StateType S} (σ σ':S) L
 : star2 step σ nil σ' ->
   produces_prefix σ L -> produces_prefix σ' L.
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
    + exploit star2_reach_silent_step; eauto. eapply H1.
      destruct X; subst. exfalso. eapply H5; firstorder.
      econstructor 4; eauto.
    + econstructor 5; eauto.
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

Lemma bisim_prefix {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
: bisim sigma σ' -> forall L, produces_prefix sigma L -> produces_prefix σ' L.
Proof.
  intros. general induction H2.
  - eapply bisim_bisim' in H3.
    eapply IHproduces_prefix; eauto.
    eapply bisim'_bisim. eapply bisim'_reduction_closed_1; eauto.
    eapply (S_star2 _ _ H0). eapply star2_refl.
  - eapply bisim_bisim' in H4.
    eapply bisim'_activated in H4; eauto.
    destruct H4 as [? [? [? []]]].
    + eapply produces_prefix_star2_silent; eauto.
      edestruct H6; eauto. destruct H8.
      econstructor 2. eauto. eapply H8.
      eapply IHproduces_prefix; eauto.
      eapply bisim'_bisim. eapply H9.
  - eapply bisim_bisim' in H4. eapply bisim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. rewrite H0.
    econstructor 3; [ | eauto | eauto]. congruence.
  - eapply bisim_bisim' in H4. eapply bisim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 4; [ | eauto | eauto]. congruence.
  - econstructor 5; eauto.
Qed.

Lemma bisim_prefix_eq {S} `{StateType S} {S'} `{StateType S'} (sigma:S) (σ':S')
  : bisim sigma σ' -> forall L, produces_prefix sigma L <-> produces_prefix σ' L.
Proof.
  split; eapply bisim_prefix; eauto.
  eapply bisim_sym; eauto.
Qed.

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

Lemma diverges_never_terminates S `{StateType S} (σ σ':S) A
: normal2 step σ' -> star2 step σ A σ' -> diverges σ -> False.
Proof.
  intros. general induction H1.
  - inv H2. firstorder.
  - inv H3.
    exploit (step_internally_deterministic). eauto. eapply H. dcr; subst.
    eapply IHstar2; eauto.
Qed.

Definition crashes S `{StateType S} (σ:S) :=
  exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = None.

Lemma diverges_never_crashes S `{StateType S} (σ σ':S)
: crashes σ -> diverges σ -> False.
Proof.
  intros. destruct H0; dcr.
  eapply diverges_never_terminates; eauto.
Qed.

Lemma crashes_not_activated S `{StateType S} (σ σ':S)
: crashes σ -> star2 step σ nil σ' -> activated σ' -> False.
Proof.
  intros. destruct H0. dcr.
  eauto using activated_normal_star.
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
    + exfalso. eapply (diverges_never_terminates H6); eauto. constructor.
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


Lemma sim_sound_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: sim σ σ' -> diverges σ -> diverges σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1.
  - eapply plus2_destr_nil in H4. dcr.
    econstructor. eauto.
    eapply COH; eauto.
    eapply sim'_sim.
    eapply sim'_reduction_closed.
    eapply sim_sim'. eapply H1. econstructor.
    eapply (S_star2 EvtTau); eauto. econstructor.
  - eapply diverges_reduction_closed in H3.
    + exfalso. eapply (diverges_never_activated H5); eauto.
    + eapply H2.
  - eapply diverges_reduction_closed in H4.
    + exfalso. eapply (diverges_never_terminates H5); eauto. constructor.
    + eapply H2.
  - eapply diverges_reduction_closed in H4.
    + exfalso. eapply (diverges_never_terminates H6); eauto. constructor.
    + eapply H2.
Qed.

Lemma sim_complete_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: diverges σ -> diverges σ' -> sim σ σ'.
Proof.
  revert σ σ'. cofix COH; intros.
  inv H1; inv H2.
  econstructor. econstructor; eauto. econstructor; eauto.
  eapply COH; eauto.
Qed.

CoInductive stream (A : Type) : Type :=
| sil : stream A
| sons : A -> stream A -> stream A.

Arguments sil [A].

(*
CoInductive coproduces {S} `{StateType S} : S -> stream extevent -> Prop :=
| CoProducesExtern (σ σ' σ'':S) ext L :
    star2 step σ nil σ'
      -> activated σ'
      -> step σ' (EvtExtern ext) σ''
      -> coproduces σ'' L
      -> coproduces σ (sons (EEvt ext) L)
| CoProducesSilent (σ:S) :
    diverges σ
    -> coproduces σ sil
| CoProducesTerm (σ:S) (σ':S) r
  : result σ' = r
    -> star2 step σ nil σ'
    -> normal2 step σ'
    -> coproduces σ (sons (EvtTerminate r) sil).

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
 *)

Lemma produces_prefix_extevent S `{StateType S} (σ:S) evt L
: produces_prefix σ (EEvtExtern evt::L)
  -> ~ crashes σ
  -> exists σ', star2 step σ nil σ'
          /\ activated σ'
          /\ exists σ'', step σ' evt σ'' /\ produces_prefix σ'' L.
Proof.
  intros. general induction H0.
  - edestruct IHproduces_prefix. reflexivity.
    + intro. eapply H2. inv H3; dcr.
      eexists; split; eauto. eapply (S_star2 EvtTau); eauto.
    + eexists x; intuition. eapply (S_star2 EvtTau); eauto.
  - eexists σ; intuition. econstructor. eexists; eauto.
  - exfalso. eapply H3. eexists; eauto.
Qed.

Lemma produces_prefix_terminates S `{StateType S} (σ:S) r L
:  produces_prefix σ (EEvtTerminate r::L)
   -> ~ crashes σ
   -> exists σ', star2 step σ nil σ' /\ normal2 step σ' /\ result σ' = r /\ L = nil.
Proof.
  intros. general induction H0.
  - edestruct IHproduces_prefix. reflexivity.
    + intro. eapply H2. inv H3; dcr.
      eexists; split; eauto. eapply (S_star2 EvtTau); eauto.
    + eexists x; dcr; intuition. eapply (S_star2 EvtTau); eauto.
  - eexists; intuition; eauto.
  - exfalso; eapply H3.
    eexists; eauto.
Qed.

Lemma diverges_produces_only_nil S `{StateType S} S' `{StateType S'} (σ:S)
: diverges σ -> (forall L, produces_prefix σ L -> L = nil).
Proof.
  intros. general induction L; eauto.
  destruct a.
  - eapply produces_prefix_extevent in H2; dcr.
    exfalso. eapply diverges_never_activated; eauto.
    eapply diverges_reduction_closed; eauto.
    intro. eapply diverges_never_crashes; eauto.
  - eapply produces_prefix_terminates in H2; dcr; subst.
    exfalso. eapply diverges_never_terminates; eauto using diverges_reduction_closed.
    eauto using diverges_never_crashes.
Qed.

Lemma produces_only_nil_diverges S `{StateType S} (σ:S)
: (forall L, produces_prefix σ L -> L = nil) -> diverges σ.
Proof.
  revert σ. cofix f; intros.
  destruct (@step_dec _ H σ).
  - destruct H1; dcr. destruct x.
    + exfalso. exploit H0. econstructor 2; try eapply H2.
      eexists; eauto.
      econstructor 5. congruence.
    + econstructor. eauto. eapply f.
      intros. eapply H0.
      eapply produces_prefix_star2_silent.
      eapply (S_star2 EvtTau); eauto. econstructor. eauto.
  - exfalso. case_eq (result σ); intros.
    + exploit H0. econstructor 3; eauto. constructor. congruence.
    + exploit H0. econstructor 4; eauto. constructor.
      instantiate (1:=EEvtExtern (EvtExtern (ExternI 0 nil 0))::nil) in X.
      congruence.
Qed.

Lemma produces_diverges' S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ' L -> produces_prefix σ L)
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
    econstructor 2. eexists; eauto. eauto. econstructor 5.
    congruence.
  - econstructor. eapply H7.
    eapply f; intros; try eapply H4.
    + eapply produces_prefix_star2_silent'.
      eapply (S_star2 EvtTau). eapply H3. econstructor.
      eapply H1. econstructor; eauto.
  - exfalso.
    case_eq (result σ'); intros.
    + exploit (diverges_produces_only_nil H2).
      eapply H1. econstructor 3; eauto. constructor.
      congruence.
    + exploit (diverges_produces_only_nil H2).
      eapply H1. econstructor 4; eauto. constructor.
      instantiate (1:=EEvtExtern (EvtExtern (ExternI 0 nil 0))::nil) in X.
      congruence.
Qed.

Lemma produces_diverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ L <-> produces_prefix σ' L)
  -> diverges σ -> diverges σ'.
Proof.
  intros.
  eapply (@produces_diverges' S _ S' _); eauto.
  eapply H1; eauto.
Qed.


Lemma produces_prefix_star_activated S `{StateType S} (σ1 σ1' σ1'':S) ext L
: star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' (EvtExtern ext) σ1''
  -> produces_prefix σ1'' L
  -> produces_prefix σ1 (EEvtExtern ext::L).
Proof.
  intros. general induction H0.
  - econstructor 2; eauto.
  - destruct y, yl; simpl in *; try congruence.
    econstructor; eauto.
Qed.

Lemma produces_prefix_preserved' S `{StateType S} S' `{StateType S'} (P : list extevent -> Prop)
      (PEXT:forall L e, P L -> P (EEvtExtern e::L))
      (σ1 σ1' σ1'':S) (σ2 σ2' σ2'':S') ext
: (forall L : list extevent, P L -> produces_prefix σ1 L -> produces_prefix σ2 L)
  -> star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' (EvtExtern ext) σ1''
  -> star2 step σ2 nil σ2'
  -> activated σ2'
  -> step σ2' (EvtExtern ext) σ2''
  -> forall L, P L -> produces_prefix σ1'' L -> produces_prefix σ2'' L.
Proof.
  intros.
  - exploit (produces_prefix_star_activated _ H2 H3 H4 H9).
    eapply H1 in X.
    eapply produces_prefix_extevent in X. dcr.
    exploit both_activated. eapply H11. eapply H5. eauto. eauto. subst.
    assert (x0 = σ2''). eapply step_externally_determined; eauto. subst; eauto.
    eauto using crashes_not_activated.
    eauto using no_activated_tau_step.
Qed.

Lemma produces_prefix_preserved S `{StateType S} S' `{StateType S'}
      (P : list extevent -> Prop)
      (PEXT:forall L e, P L -> P (EEvtExtern e::L))
      (σ1 σ1' σ1'':S) (σ2 σ2' σ2'':S') ext
:
  (forall L : list extevent, P L -> (produces_prefix σ1 L <-> produces_prefix σ2 L))
  -> star2 step σ1 nil σ1'
  -> activated σ1'
  -> step σ1' (EvtExtern ext) σ1''
  -> star2 step σ2 nil σ2'
  -> activated σ2'
  -> step σ2' (EvtExtern ext) σ2''
  -> forall L, P L -> (produces_prefix σ1'' L <-> produces_prefix σ2'' L).
Proof.
  split; intros.
  eapply (@produces_prefix_preserved' S _ S' _ P); intros; eauto.
  eapply H1; eauto.
  eapply (@produces_prefix_preserved' S' _ S _ P); intros; eauto.
  eapply H1; eauto.
Qed.

(*
Lemma produces_coproduces S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ L <-> produces_prefix σ' L)
  -> (forall T, coproduces σ T -> coproduces σ' T).
Proof.
  revert σ σ'.
  cofix f; intros.
  inv H2.
  - assert (produces_prefix σ (EEvt ext::nil)).
    eapply produces_prefix_star_activated; eauto. econstructor 5.
    eapply H1 in H7.
    eapply produces_prefix_extevent in H7. dcr.
    econstructor. eauto. eauto. eauto. eapply f; try eapply H6.
    intros.
    eapply (produces_prefix_preserved (fun _ => True)); eauto.
    admit.
  - eapply produces_diverges in H3.
    econstructor; eauto. eauto.
  - case_eq (result σ'0); intros.
    + assert (produces_prefix σ (EvtTerminate (result σ'0)::nil)). {
        + rewrite H3. econstructor 3; eauto.
      }
    eapply H1 in H6.
    eapply produces_prefix_terminates in H6. dcr.
    econstructor 3; eauto. rewrite H9; eauto.
    intro. admit.
    + admit.
Admitted.
 *)

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

Lemma produces_silent_closed {S} `{StateType S}  S' `{StateType S'}  (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, produces_prefix σ1 L <-> produces_prefix σ2 L)
  -> (forall L, produces_prefix σ1' L <-> produces_prefix σ2' L).
Proof.
  split; intros.
  - eapply produces_prefix_star2_silent'; eauto. eapply H3.
    eapply produces_prefix_star2_silent; eauto.
  - eapply produces_prefix_star2_silent'; eauto. eapply H3.
    eapply produces_prefix_star2_silent; eauto.
Qed.

Lemma terminates_not_crashes S `{StateType S} (σ:S) (σ':S) v
:  star2 step σ nil σ'
   -> normal2 step σ'
   -> result σ' = ⎣ v ⎦
   -> ~ crashes σ.
Proof.
  intros. intro. destruct H3; dcr.
  assert (x = σ'). eapply star2_reach_normal2; eauto. eapply H.
  subst. congruence.
Qed.

Lemma produces_all_prefixes_crashes S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ L) <-> crashes σ.
Proof.
  split; intros.
  - destruct (classic (crashes σ)); eauto.
    exfalso.
    assert (produces_prefix σ (EEvtExtern (ExternI 0 nil 0)::nil)) by eauto.
    assert (produces_prefix σ (EEvtTerminate 0::nil)) by eauto.
    exploit (produces_prefix_terminates H4); eauto.
    exploit (produces_prefix_extevent H3); eauto. dcr.
    exploit (star2_reach_normal H10 H6); eauto. eapply H.
    eauto using @activated_normal_star.
  - destruct H1 as [? [? []]].
    econstructor 4; eauto.
Qed.

Lemma crashes_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
:  crashes σ
   -> crashes σ'
   -> bisim σ σ'.
Proof.
  intros. destruct H1, H2; dcr.
  econstructor 3; eauto. congruence.
Qed.

Lemma produces_prefix_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ L <-> produces_prefix σ' L)
  -> bisim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  destruct (three_possibilities σ) as [A|[A|A]].
  - dcr. case_eq (result x); intros.
    + assert (produces_prefix σ (EEvtTerminate v::nil)).
      econstructor 3; eauto.
      eapply H1 in H5.
      eapply produces_prefix_terminates in H5. dcr.
      econstructor 3; eauto. congruence.
      * intro. pose proof (terminates_not_crashes H3 H4 H2).
        rewrite <- produces_all_prefixes_crashes in H6; eauto.
        assert (forall L : list extevent, produces_prefix σ L). {
          intros. eapply H1. eauto.
        }
        rewrite produces_all_prefixes_crashes in H8; eauto.
    + clear f.
      assert (crashes σ). eexists; split. eauto. eauto.
      assert (crashes σ').
      rewrite <- produces_all_prefixes_crashes in H5; [|eauto|eauto].
      assert (forall L : list extevent, produces_prefix σ' L) by firstorder.
      rewrite produces_all_prefixes_crashes in H6; [|eauto|eauto].
      eauto.
      eapply crashes_bisim; eauto. Guarded.
  - dcr. inv H4; dcr.
    assert (produces_prefix x1 nil) by econstructor 5.
    exploit (produces_prefix_star_activated _ H3 H4 H5 H2).
    eapply H1 in X.
    eapply produces_prefix_extevent in X. dcr.
    econstructor 2; eauto. Guarded.
    + intros. destruct evt.
      assert (B:produces_prefix x (EEvtExtern call::nil)).
      econstructor 2. eauto. eauto. econstructor 5.
      pose proof H1.
      eapply produces_silent_closed in H11; eauto.
      eapply H11 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H9 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        intros. Guarded.
        eapply (produces_prefix_preserved (fun _ => True)); eauto.
      * exfalso. eauto using activated_normal_star, star2.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H8 H5 ); eauto. dcr; congruence.
    + intros. destruct evt.
      assert (B:produces_prefix x2 (EEvtExtern call::nil)).
      econstructor 2. eauto. eauto. econstructor 5.
      pose proof H1.
      eapply produces_silent_closed in H11; eauto.
      eapply H11 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H5 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        intros. Guarded.
        eapply (produces_prefix_preserved (fun _ => True)); eauto.
      * exfalso. eapply (activated_normal_star (star2_refl _ _) H4). eauto. eauto.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H8 H9 ); eauto. dcr; congruence.
    + clear f.
      intro.
      assert (crashes σ).
      rewrite <- produces_all_prefixes_crashes in H6; [|eauto|eauto].
      assert (forall L : list extevent, produces_prefix σ L) by firstorder.
      rewrite produces_all_prefixes_crashes in H7; [|eauto|eauto].
      eauto.
      eapply (crashes_not_activated H7). eauto. eauto.
  - assert (diverges σ').
    eapply (produces_diverges H1); eauto.
    eapply bisim_complete_diverges; eauto.
Qed.

Inductive not_crashed : list extevent -> Prop :=
| NotCrashedTrm v
  : not_crashed (EEvtTerminate v::nil)
| NotCrashedDiv
  : not_crashed nil
| NotCrashedStep e es
  : not_crashed es
    -> not_crashed (EEvtExtern e::es).

Lemma produces_not_crashed_silent_closed {S} `{StateType S}  S' `{StateType S'}  (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, not_crashed L -> (produces_prefix σ1 L <-> produces_prefix σ2 L))
  -> (forall L, not_crashed L -> (produces_prefix σ1' L <-> produces_prefix σ2' L)).
Proof.
    split; intros.
  - eapply produces_prefix_star2_silent'; eauto. eapply H3. eauto.
    eapply produces_prefix_star2_silent; eauto.
  - eapply produces_prefix_star2_silent'; eauto. eapply H3. eauto.
    eapply produces_prefix_star2_silent; eauto.
Qed.

Lemma produces_not_crashed_silent_closed' {S} `{StateType S}  S' `{StateType S'}  (σ1 σ1':S) (σ2 σ2':S')
: star2 step σ1 nil σ1'
  -> star2 step σ2 nil σ2'
  -> (forall L, not_crashed L -> (produces_prefix σ1 L -> produces_prefix σ2 L))
  -> (forall L, not_crashed L -> (produces_prefix σ1' L -> produces_prefix σ2' L)).
Proof.
  intros.
  - eapply produces_prefix_star2_silent'; eauto. eapply H3. eauto.
    eapply produces_prefix_star2_silent; eauto.
Qed.

CoInductive crashdiverges S `{StateType S} : S -> Prop :=
| CrashDivergesDiv σ σ'
  : step σ EvtTau σ'
    -> crashdiverges σ'
    -> crashdiverges σ
| CrashDivergesCrash σ
  : normal2 step σ
    -> result σ = None
    ->  crashdiverges σ.

Lemma crashdiverges_not_diverges S `{StateType S} (σ:S)
: ~ crashes σ -> crashdiverges σ -> diverges σ.
Proof.
  revert σ. cofix f. intros.
  inv H1.
  - econstructor; eauto. eapply f.
    intro. eapply H0. destruct H4. dcr.
    eexists x; repeat split; eauto. eapply (S_star2 EvtTau); eauto.
    eauto.
  - exfalso. eapply H0. eexists σ; split; eauto. econstructor.
Qed.

Lemma crashdiverges_crashes_or_diverges S `{StateType S} (σ:S)
: crashdiverges σ -> crashes σ \/ diverges σ.
Proof.
  destruct (classic (crashes σ)); eauto using crashdiverges_not_diverges.
Qed.

Lemma crash_crashdiverges  S `{StateType S} (σ σ':S)
: star2 step σ nil σ'
  -> normal2 step σ'
  -> result σ' = None
  -> crashdiverges σ.
Proof.
  intros. general induction H0; eauto using crashdiverges.
  destruct y,yl; simpl in *; try congruence.
  eauto using crashdiverges.
Qed.

Lemma produces_not_crashed_prefix_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, produces_prefix σ' L -> produces_prefix σ L)
  -> sim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  destruct (classic (crashes σ)).
  clear f. inv H2. econstructor 3. eapply H3. eauto. eapply H3.
  destruct (three_possibilities σ') as [A|[A|A]].
  - dcr. case_eq (result x); intros.
    + assert (produces_prefix σ' (EEvtTerminate v::nil)).
      econstructor 3; eauto.
      eapply H1 in H6.
      eapply produces_prefix_terminates in H6. dcr.
      econstructor 4; eauto. congruence. eauto.
    + clear f. exfalso.
      assert (crashes σ'). eexists; split. eauto. eauto.
      eapply H2.
      rewrite <- produces_all_prefixes_crashes in H6; [|eauto|eauto].
      assert (forall L : list extevent, produces_prefix σ L) by firstorder.
      rewrite produces_all_prefixes_crashes in H7; [|eauto|eauto].
      eauto.
  - dcr. inv H5; dcr.
    assert (produces_prefix x1 nil) by econstructor 5.
    exploit (produces_prefix_star_activated _ H4 H5 H6 H3).
    eapply H1 in X.
    eapply produces_prefix_extevent in X. dcr.
    econstructor 2; eauto. Guarded.
    + (* intros. destruct evt.
      assert (B:produces_prefix x2 (EEvtExtern call::nil)).
      econstructor 2. eauto. eauto. econstructor 5.
      eapply H1 in B.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H9 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        intros. Guarded.
        eapply (produces_prefix_preserved (fun _ => True)); eauto.
      * exfalso. eauto using activated_normal_star, star2.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H8 H5 ); eauto. dcr; congruence.
      *)
      exfalso; clear_all; admit.
    + intros. destruct evt.
      assert (B:produces_prefix x (EEvtExtern call::nil)).
      econstructor 2. eauto. eauto. econstructor 5.
      assert (C:produces_prefix x2 (EEvtExtern call :: nil)). clear f; admit.
      inv C.
      * exfalso. eapply (no_activated_tau_step _ _ H12).
      * eexists; split. eauto. eapply f.
        intros. Guarded.
        eapply (produces_prefix_preserved' (fun _ => True)); eauto.
      * exfalso. eapply (activated_normal_star (star2_refl _ _) H7). eauto. eauto.
      * exfalso. eapply (no_activated_tau_step _ _ H9).
    + eauto.
  - assert (diverges σ').
    eapply (produces_diverges H1); eauto.
    eapply bisim_complete_diverges; eauto.
Qed.


Inductive crashed : list extevent -> Prop :=
| CrashCrash r
  : r = None
    -> crashed (EEvtTerminate r::nil)
| CrashedStep e es
  : crashed es
    -> crashed (EEvt (EvtExtern e)::es).

Lemma produces_not_crashed_crashdiverges S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, not_crashed L -> produces_prefix σ' L -> produces_prefix σ L)
  -> diverges σ -> crashdiverges σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  inv H2.
  edestruct (@step_dec _ H0 σ').
  inv H5; dcr.
  destruct x.
  - exfalso.
    pose proof (diverges_produces_only_nil H2).
    exploit H6. eapply H1. Focus 2.
    econstructor 2. eexists; eauto. eauto. econstructor 4.
    econstructor; econstructor.
    congruence.
  - econstructor. eapply H7.
    eapply f; intros; try eapply H4.
    + eapply produces_prefix_star2_silent'.
      eapply (S_star2 EvtTau). eapply H3. econstructor.
      eapply H1. eauto. econstructor; eauto.
  - case_eq (result σ'); intros.
    + exfalso.
      exploit (diverges_produces_only_nil H2).
      eapply H1. Focus 2.
      econstructor 3; eauto. constructor.
      eauto using not_crashed.
      congruence.
    + eapply crash_crashdiverges; eauto. econstructor.
Qed.

Lemma crashes_crashed S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
:  (forall L : list extevent,
      crashed L -> produces_prefix σ' L -> produces_prefix σ L)
   -> crashes σ' -> crashes σ.
Proof.
  intros. destruct H2; dcr.
  exploit producesPrefixTerm; eauto.
  eapply H1 in X.
  eapply produces_prefix_terminates in X. dcr.
  eexists x0; intuition. eauto using crashed.
Qed.

(*
Lemma produces_not_crashed_prefix_sim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, not_crashed L -> (produces_prefix σ L -> produces_prefix σ' L))
  -> (forall L, crashed L -> (produces_prefix σ' L -> produces_prefix σ L))
  -> sim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  destruct (three_possibilities σ) as [A|[A|A]].
  - dcr.
    case_eq (result x); intros.
    + assert (produces_prefix σ (EvtTerminate (result x)::nil)).
      econstructor 3; eauto.
      eapply H1 in H6; [|eauto using not_crashed].
      eapply produces_prefix_terminates in H6. dcr.
      econstructor 4; eauto.
    + econstructor 3; eauto.
  - dcr. inv H5; dcr.
    assert (produces_prefix x1 nil) by econstructor 4.
    exploit (produces_prefix_star_activated _ H4 H5 H6 H3).
    eapply H1 in X;[| eauto using not_crashed].
    eapply produces_prefix_extevent in X. dcr.
    econstructor 2; eauto.
    + intros.
      assert (B:produces_prefix x (EEvt evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      eapply produces_not_crashed_silent_closed' in B; eauto.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H10 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply produces_prefix_preserved'; eauto.
        intros; econstructor; eauto.
        eapply produces_prefix_preserved'; eauto.
        intros; econstructor; eauto.
      * destruct evt; eauto using not_crashed.
        exfalso. exploit (@step_internally_deterministic S _ ). eauto. eapply H6. dcr; congruence.
    + intros.
      assert (B:produces_prefix x2 (EEvt evt::nil)) by
          (econstructor 2; eauto; econstructor 4).
      pose proof (produces_not_crashed_silent_closed' H4 H8 H1); eauto.
      inv B.
      * exfalso. exploit (step_internally_deterministic _ _ _ _ H12 H10 ); eauto. dcr; congruence.
      * eexists; split. eauto. eapply f.
        eapply produces_prefix_preserved; eauto.
        intros; econstructor; eauto.
        eapply produces_prefix_preserved'; eauto.
        intros; econstructor; eauto.
      * destruct evt; eauto using not_crashed.
        exfalso. eauto using no_activated_tau_step. Guarded.
  - exploit (@produces_not_crashed_crashdiverges S _ S' _). eapply H1. eauto.
    eapply crashdiverges_crashes_or_diverges in X. destruct X.
    exfalso. eapply crashes_crashed in H3; eauto.
    destruct H3; dcr.
    eapply (diverges_never_terminates H6); eauto.
    eapply sim_complete_diverges. eauto. eauto.
Qed.

Lemma sim_prefix {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
: sim σ σ' -> forall L, produces_prefix σ' L -> produces_prefix σ L.
Proof.
  intros. general induction H2.
  - eapply sim_sim' in H3.
    eapply IHproduces_prefix; eauto.
    eapply sim'_sim. eapply sim'_reduction_closed_2; eauto.
    eapply (S_star2 _ _ H). eapply star2_refl.
  - eapply sim_sim' in H4.
    eapply sim'_activated_2 in H4; eauto.
    dcr; intuition.
    destruct evt.
    + eapply produces_prefix_star2_silent; eauto.
      edestruct H4; eauto. destruct H7.
      econstructor 2. eauto. eapply H7.
      eapply IHproduces_prefix; eauto.
      eapply sim'_sim. eapply H9.
    + exfalso; eapply (no_activated_tau_step _ H H1); eauto.
    +
  - case_eq (result σ'); intros.
    eapply sim_sim' in H4. eapply sim'_terminate in H4; eauto.
    destruct H4 as [? [? []]]. econstructor 3; [ | eauto | eauto]. congruence. congruence.
  - econstructor 4.
Qed.

Lemma sim_traces S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: sim σ σ'
  ->  (forall L, produces_prefix σ' L -> produces_prefix σ L).
Proof.
  intros.
  general induction H2.
  - eapply IHproduces_prefix.
    eapply sim'_sim.
    eapply sim'_reduction_closed. eapply sim_sim'. eapply H3. econstructor.
    eapply (S_star2 EvtTau); eauto. constructor.
  - destruct evt.
    edestruct (@sim'_activated_2 S' _ σ S); eauto. eapply (sim_sim' H4).
    intuition.
    + inv H7. dcr. eapply produces_prefix_star_activated. eauto. eauto.
*)
Lemma three_possibilities' S `{StateType S} (σ:S)
: { σ' | star2 step σ nil σ' /\ normal2 step σ' }
  + { σ' | star2 step σ nil σ' /\ activated σ' }
  + diverges σ.
Proof.
Admitted.

Lemma activated_destr S `{StateType S} (σ:S)
:  activated σ -> { ext : extern & { σ' | step σ (EvtExtern ext) σ' } }.
Proof.
  intros. admit.
Qed.

Lemma coproduces_trace S `{StateType S} (σ:S) : stream extevent.
Proof.
  revert σ. cofix f; intros σ.
  destruct (three_possibilities' σ). destruct s.
  - destruct s. eapply (sons (EvtTerminate (result x)) sil).
  - destruct s. destruct a. eapply activated_destr in H1.
    destruct H1. destruct s. refine (sons (EEvt (EvtExtern x0)) _).
    eapply (f x1).
  - eapply sil.
Defined.

Definition stream_match X (s:stream X) :=
  match s with
    | sil => sil
    | sons A s => sons A s
  end.

Lemma stream_match_eq X (s:stream X)
: s = stream_match s.
Proof.
  destruct s; reflexivity.
Qed.

Lemma coproduces_trace_sound S `{StateType S} (σ:S)
: coproduces σ (coproduces_trace σ).
Proof.
  revert σ. cofix f; intros.
  unfold coproduces_trace.
  rewrite stream_match_eq; simpl.
  case_eq (three_possibilities' σ); intros; simpl.
  - destruct s. destruct s. econstructor; eauto.
    + destruct s. destruct a.
      destruct (activated_destr a). destruct s0.
      econstructor. eauto. eauto. eauto. eapply f.
  - econstructor 2. eauto.
Qed.

Lemma coproduces_total S `{StateType S} (σ:S)
: exists L, coproduces σ L.
Proof.
  eexists. eapply coproduces_trace_sound.
Qed.


Inductive safe : stream extevent -> Prop :=
| SafeTrm v
  : safe (sons (EvtTerminate (Some v)) sil)
| SafeDiv
  : safe sil
| SafeStep e es
  : safe es
    -> safe (sons e es).

Lemma diverges_coproduces_only_sil S `{StateType S} S' `{StateType S'} (σ:S)
: diverges σ -> (forall L, coproduces σ L -> L = sil).
Proof.
  intros. inv H2.
  - exfalso. eapply (diverges_never_activated H4).
    eapply diverges_reduction_closed; eauto.
  - reflexivity.
  - exfalso. eapply (diverges_never_terminates H5); eauto.
Qed.

CoInductive cocontinues X :

Lemma coproduces_safe_bisim S `{StateType S} S' `{StateType S'} (σ:S) (σ':S')
: (forall L, coproduces σ L -> coproduces σ' L)
  -> sim σ σ'.
Proof.
  revert σ σ'.
  cofix f; intros.
  assert (exists L, safe L /\ coproduces σ L) by (exfalso; clear_all; admit).
  dcr. inv H5.
  - exploit H1. eauto. eauto.
    inv X.
    econstructor 2. eauto. eauto. eauto. eauto.
    + intros.
    +

  - eapply H1 in H5. inv H5.
    eapply sim_complete_diverges; eauto. eauto.
  - case_eq (result σ'0); intros.
    + exploit H1. eauto. eauto.
      inv X.
      econstructor 4. symmetry in H8. eapply H8.
      eauto. eauto. eauto. eauto.
    + econstructor 3; eauto.
Qed.






(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
