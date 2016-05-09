Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export SmallStepRelations StateType paco Equiv.

Set Implicit Arguments.
Unset Printing Records.

(** * Simulation *)
(** A characterization of simulation equivalence on states; works only for deterministic semantics *)

CoInductive sim {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | simSilent (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> sim σ1' σ2'
      -> sim σ1 σ2
  | simExtern (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ sim σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ sim σ1' σ2')
      -> sim pσ1 pσ2
  | simErr (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim σ1 σ2
  | simTerm (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim σ1 σ2.

Arguments sim [S] {H} [S'] {H0} _ _.

Lemma sim_refl {S} `{StateType S} (σ:S)
      : sim σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply simExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply simSilent; eauto using plus2O.
  - eapply simTerm; eauto using star2_refl.
Qed.

Inductive sim_gen
          {S} `{StateType S} {S'} `{StateType S'} (r: S -> S' -> Prop)  : S -> S' -> Prop :=
  | sim'Silent (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> r σ1' σ2'
      -> sim_gen r σ1 σ2
  | sim'Extern (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ r σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ r σ1' σ2')
      -> sim_gen r pσ1 pσ2
  | sim'Err (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim_gen r σ1 σ2
  | sim'Term (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim_gen r σ1 σ2.

Arguments sim_gen [S] {H} [S'] {H0} r _ _.

Hint Constructors sim_gen.

Definition sim' {S} `{StateType S} {S'} `{StateType S'}  (σ1:S) (σ2:S')
  := paco2 (@sim_gen S _ S' _) bot2 σ1 σ2.
Hint Unfold sim'.

Definition sim'r {S} `{StateType S} {S'} `{StateType S'} r (σ1:S) (σ2:S')
  := paco2 (@sim_gen S _ S' _) r σ1 σ2.
Hint Unfold sim'r.

Lemma sim_gen_mon {S} `{StateType S} {S'} `{StateType S'}
: monotone2 (@sim_gen S _ S' _).
Proof.
  hnf; intros. inv IN; eauto using @sim_gen.
  - econstructor 2; eauto; intros.
    edestruct H5; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.
Qed.

Arguments sim_gen_mon [S] {H} [S'] {H0} [x0] [x1] r r' IN LE.


Hint Resolve sim_gen_mon : paco.

Lemma sim_sim' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> sim' σ1 σ2.
Proof.
  revert σ1 σ2. pcofix CIH.
  intros. pfold.
  inv H2; eauto using sim_gen.
  - econstructor 2; eauto; intros.
    + edestruct H6; eauto; dcr. eexists; eauto.
    + edestruct H7; eauto; dcr. eexists; eauto.
Qed.


Lemma sim'_sim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim' σ1 σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix CIH.
  intros.
  (assert (sim_gen (paco2 (sim_gen (S':=S')) bot2 \2/ bot2) σ1 σ2)).
  punfold H1.
  destruct H2. destruct H4.
  - econstructor; eauto.
  - exfalso; intuition.
  - econstructor 2; eauto; intros.
    + edestruct H6; eauto; dcr. destruct H11. eexists; eauto. exfalso; intuition.
    + edestruct H7; eauto; dcr. destruct H11. eexists; eauto. exfalso; intuition.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
Qed.


Lemma sim'_refl {S} `{StateType S} (σ:S)
      : sim' σ σ.
Proof.
  eapply sim_sim'. eapply sim_refl.
Qed.


Lemma sim_Y_left r σA1 σB1 σ1' σ2
  : paco2 (@sim_gen I.state _ I.state _) r
            σA1
            σ2
    -> step σA1 EvtTau σ1'
    -> step σB1 EvtTau σ1'
    -> paco2 (@sim_gen I.state _ I.state _) r
            σB1
            σ2.
Proof.
  intros SIM Step1 Step2.
  pinversion SIM; subst; intros; relsimpl; pfold;
    eauto using sim_gen, star2_silent, star2_plus2.
Qed.

Lemma sim_Y_right r σ1 σA2 σB2 σ2'
  : paco2 (@sim_gen I.state _ I.state _) r σ1 σA2
    -> step σA2 EvtTau σ2'
    -> step σB2 EvtTau σ2'
    -> paco2 (@sim_gen I.state _ I.state _) r σ1 σB2.
Proof.
  intros SIM Step1 Step2.
  pinversion SIM; subst; intros; relsimpl; pfold;
    eauto using sim_gen, star2_silent, star2_plus2.
Qed.

Ltac contr_trans :=
  repeat (match goal with
          | [ H : star2 ?R ?σ1 _ ?σ2, H' : star2 ?R ?σ2 _ ?σ3 |- _ ]
            => let H'' := fresh H in
              pose proof (star2_trans H H') as H''; clear H; clear H';
              rename H'' into H
          end).

Lemma sim'_expansion_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S') r
  : sim'r r σ1' σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sim'r r σ1 σ2.
Proof.
  intros SIM ? ?.
  pinversion SIM; subst; pfold;
    eauto using sim_gen, star2_plus2_plus2_silent, star2_trans_silent.
Qed.

Tactic Notation "size" "induction" hyp(n) :=
  pattern n; eapply size_induction with (f:=id); intros; unfold id in *.

Lemma sim'_reduction_closed_1 {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S')
  : sim' σ1 σ2
    -> star2 step σ1 nil σ1'
    -> sim' σ1' σ2.
Proof.
  intros Sim Star. eapply star2_star2n in Star. destruct Star as [n StarN].
  revert σ1 σ1' σ2 Sim StarN.
  size induction n.
  pinversion Sim; subst.
  - invc StarN; eauto; relsimpl.
    eapply star2_star2n in H2. destruct H2 as [n' H2].
    edestruct (star2n_reach H9 H2); eauto. eapply H.
    + eapply sim'_expansion_closed; eauto using star2n_star2, plus2_star2.
    + eapply H1; try eapply H9. omega.
      eapply sim'_expansion_closed;
      eauto using star2n_star2, plus2_star2.
  - eapply star2n_star2 in StarN; relsimpl; eauto.
  - pfold. eapply star2n_star2 in StarN; relsimpl; eauto.
  - pfold. eapply star2n_star2 in StarN; relsimpl; eauto.
Qed.


Lemma sim'_reduction_closed_2 {S} `{StateType S}
      (σ1:S) {S'} `{StateType S'} (σ2 σ2':S')
  : sim' σ1 σ2
    -> star2 step σ2 nil σ2'
    -> sim' σ1 σ2'.
Proof.
  intros. eapply star2_star2n in H2. destruct H2 as [n ?].
  revert σ1 σ2' σ2 H1 H2.
  pattern n.
  eapply size_induction with (f:=id); intros; unfold id in *; simpl in *.
  pinversion H2; subst.
  - inv H3; eauto.
    eapply plus2_plus2n in H5. destruct H5. eapply plus2n_star2n in H5.
    edestruct (star2n_reach H3 H5); eauto. eapply H0.
    + eapply sim'_expansion_closed. eapply H6.
      eauto using plus2_star2. eauto using star2n_star2.
    + eapply H1; try eapply H9. omega.
      eapply sim'_expansion_closed. eapply H6.
      eauto using plus2_star2. eapply star2_refl.
  - eapply star2n_star2 in H3. eapply activated_star_reach in H3; eauto.
  - pfold. eauto.
  - pfold. eapply star2n_star2 in H3.
    eapply star2_reach_normal in H3; eauto. eapply H0.
Qed.


Lemma sim'_terminate {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2:S2)
: star2 step σ1 nil σ1'
  -> normal2 step σ1'
  -> result σ1' <> None
  -> sim' σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ normal2 step σ2' /\ result σ1' = result σ2'.
Proof.
  intros. general induction H1.
  - pinversion H4; subst.
    + exfalso. eapply H2. inv H1; do 2 eexists; eauto.
    + exfalso. eapply star2_normal in H1; eauto. subst.
      eapply (activated_normal _ H6); eauto.
    + eapply star2_normal in H5; eauto; subst.
      congruence.
    + eapply star2_normal in H5; eauto; subst.
      eexists; split; eauto.
  - destruct y; isabsurd. simpl.
    eapply IHstar2; eauto.
    eapply sim'_reduction_closed_1; eauto using star2, star2_silent.
Qed.


Lemma sim'_terminate_2 {S1} `{StateType S1} (σ2 σ2':S1)
      {S2} `{StateType S2} (σ1:S2)
: star2 step σ2 nil σ2'
  -> normal2 step σ2'
  -> sim' σ1 σ2
  -> exists σ1', star2 step σ1 nil σ1' /\ normal2 step σ1' /\
           (result σ1' = result σ2' \/ result σ1' = None).
Proof.
  intros. general induction H1.
  - pinversion H3; subst.
    + exfalso. eapply H2. inv H4; do 2 eexists; eauto.
    + exfalso. eapply star2_normal in H4; eauto. subst.
      eapply (activated_normal _ H6); eauto.
    + eexists σ1'; split; eauto.
    + inv H5.
      * eexists; split; eauto.
      * exfalso. eapply H2. eexists; eauto.
  - destruct y; isabsurd. simpl.
    eapply IHstar2; eauto.
    eapply sim'_reduction_closed_2; eauto using star2, star2_silent.
Qed.

Lemma sim'_activated {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> sim' σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\
                 (paco2 (sim_gen (S':=S2)) bot2 σ1'' σ2''))
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\
                 (paco2 (sim_gen (S':=S2)) bot2 σ1' σ2'')).
Proof.
  intros.
  pinversion H2; subst.
  -  exfalso. edestruct (plus2_destr_nil H3); dcr.
     destruct H1 as [? []].
     exploit (step_internally_deterministic _ _ _ _ H7 H1); dcr; congruence.
  - assert (σ1 = σ0). eapply activated_star_eq; eauto. subst σ1.
    eexists σ3; split; eauto. split; eauto. split.
    intros. edestruct H7; eauto; dcr. destruct H12; isabsurd.
    eexists; split; eauto.
    intros. edestruct H8; eauto; dcr. destruct H12; isabsurd.
    eexists; split; eauto.
  - exfalso. refine (activated_normal_star _ H1 _ _); eauto using star2.
  - exfalso. refine (activated_normal_star _ H1 _ _); eauto using star2.
Qed.

Lemma sim'_activated_2 {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> sim' σ2 σ1
  -> exists σ2', star2 step σ2 nil σ2' /\
           (activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\
                 (paco2 (sim_gen (S':=S1)) bot2 σ2'' σ1''))
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\
                 (paco2 (sim_gen (S':=S1)) bot2 σ2'' σ1'))
           \/ (normal2 step σ2' /\ result σ2' = None)).
Proof.
  intros.
  pinversion H2; subst.
  -  exfalso. edestruct (plus2_destr_nil H4); dcr.
     destruct H1 as [? []].
     exploit (step_internally_deterministic _ _ _ _ H7 H1); dcr. congruence.
  - assert (σ1 = σ3). eapply activated_star_eq; eauto. subst σ1.
    eexists σ0; split; eauto. left. split; eauto. split.
    + intros. edestruct H8; eauto; dcr. destruct H12; isabsurd.
      eexists; split; eauto.
    + intros. edestruct H7; eauto; dcr. destruct H12; isabsurd.
      eexists; split; eauto.
  - eexists σ1'. split; eauto.
  - exfalso. refine (activated_normal_star _ H1 _ _); eauto using star2.
Qed.


Lemma sim'_zigzag {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2a σ2b:S2) {S3} `{StateType S3} (σ3:S3)
  : sim' σ1 σ2a
    -> (star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a)
    -> sim' σ2b σ3
    -> sim' σ1 σ3.
Proof.
  revert σ1 σ2a σ2b σ3. pcofix CIH; intros.
  destruct H4.
  - {
      pinversion H3; pinversion H5; subst.
      - (* plus <-> plus *)
        pfold. eapply star2_plus2_plus2 in H10; eauto. clear H2; simpl in *.
        edestruct (plus2_reach H6 H10); eauto.
        eapply H0.
      - (* plus step <-> activated *)
        pfold.
        eapply star2_trans in H10; eauto. clear H2; simpl in *.
        eapply plus2_star2 in H6.
        exploit (activated_star_reach H12 H10 H6); eauto.
        eapply sim'_reduction_closed_2 in H7; eauto.
        destruct (sim'_activated_2 H12 H7); dcr.
        destruct H16; dcr.
        + econstructor 2.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H9). eapply H11.
          eauto. eauto.
          * intros. edestruct H19; eauto. destruct H17.
            edestruct H14; eauto. dcr.
            eexists; split; eauto. destruct H23; isabsurd.
            right. eapply CIH. eauto.
            left. eapply star2_refl. eauto.
          * intros. edestruct H15; eauto; dcr.
            destruct H21; isabsurd.
            edestruct H18; eauto; dcr. destruct H21.
            eexists; split; eauto.
            right. eapply CIH. eauto.
            left; eapply star2_refl.
            eauto.
        + econstructor 3; eauto.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H9); eauto.
      - (* plus step <-> err *)
        eapply star2_trans in H11; eauto. clear H2; simpl in *.
        eapply plus2_star2 in H6.
        exploit (star2_reach_normal H11 H12 (step_internally_deterministic) H6).
        edestruct (sim'_terminate_2 H2 H12 H7); eauto; dcr.
        destruct H15.
        + pfold.
          eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
          rewrite H10 in H8.
          econstructor 3; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
      - (*  plus step <-> term *)
        eapply star2_trans in H11; eauto. clear H2; simpl in *.
        eapply plus2_star2 in H6.
        exploit (star2_reach_normal H11 H13 step_internally_deterministic H6).
        edestruct (sim'_terminate_2 H2 H13 H7); eauto; dcr.
        destruct H17.
        + pfold.
          eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
          rewrite H10 in H8.
          econstructor 4; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
      - (* activated <-> plus step *)
          pfold.
          eapply plus2_star2 in H13.
          eapply star2_trans in H13; eauto. clear H2; simpl in *.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply sim'_reduction_closed_1 in H15; eauto.
          destruct (sim'_activated H8 H15); dcr.
          econstructor 2. eauto.
          eapply plus2_star2 in H14.
          eapply (star2_trans H14 H12). eauto.
          eauto.
          + intros.
            edestruct H9 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H16 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto. left. eapply star2_refl.
          + intros.
            edestruct H19 as [? [? ?]]; eauto; isabsurd.
            edestruct H10 as [? [? [?|?]]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto.
            left; eapply star2_refl.
      - (* activated <-> activated *)
        eapply star2_trans in H13; eauto. clear H2; simpl in *.
        exploit (both_activated H6 H13); eauto. subst.
        pfold. econstructor 2; eauto; intros.
        + edestruct H9; eauto. dcr.
          edestruct H17; eauto; dcr.
          eexists. split; eauto.
          destruct H19, H21; isabsurd.
          right. eapply CIH; try eapply H11; try eapply H19.
          left. eapply star2_refl.
        + edestruct H18; eauto. dcr.
          edestruct H10; eauto; dcr.
          eexists. split; eauto.
          destruct H19, H21; isabsurd.
          right. eapply CIH; try eapply H11; try eapply H19.
          left. eapply star2_refl.
      - (* activated <-> err *)
        eapply star2_trans in H14; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6); eauto.
      - (* activated <-> term *)
        eapply star2_trans in H14; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6); eauto.
      - (* term <-> plus step *)
        case_eq (result σ1'); intros.
        + eapply plus2_star2 in H12.
          eapply star2_trans in H12; eauto. clear H2; simpl in *.
          exploit (star2_reach_normal H7 H9 step_internally_deterministic H12).
          assert (result σ2' <> None) by congruence.
          edestruct (sim'_terminate H2 H9 H11 H14); eauto; dcr.
          pfold.
          econstructor 4. rewrite H19 in H4. eapply H4.
          eauto.
          eapply plus2_star2 in H13.
          eapply (star2_trans H13 H16); eauto.
          eauto. eauto.
        + pfold. econstructor 3; eauto.
      - eapply star2_trans in H12; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H12 H14 H7); eauto.
      - (* term <-> err *)
        pfold.
        eapply star2_trans in H13; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H14. do 2 eexists; eauto.
      - (* term <-> term *)
        pfold.
        eapply star2_trans in H13; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 4; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 4; eauto. congruence.
          * exfalso. eapply H15. do 2 eexists; eauto.
    }
  - {
      pinversion H3; pinversion H5; subst.
      - (* plus <-> plus *)
        pfold. eapply star2_plus2_plus2 in H6; eauto. clear H2; simpl in *.
        edestruct (plus2_reach H10 H6); eauto.
        eapply H0.
      - (* plus step <-> activated *)
        pfold.
        eapply plus2_star2 in H6.
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (activated_star_reach H12 H10 H6); eauto.
        eapply sim'_reduction_closed_2 in H7; eauto.
        destruct (sim'_activated_2 H12 H7); dcr.
        destruct H16; dcr.
        + econstructor 2.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H9). eapply H11.
          eauto. eauto.
          * intros. edestruct H19; eauto. destruct H17.
            edestruct H14; eauto. dcr.
            eexists; split; eauto. destruct H23; isabsurd.
            right. eapply CIH. eauto.
            left. eapply star2_refl. eauto.
          * intros. edestruct H15; eauto; dcr.
            destruct H21; isabsurd.
            edestruct H18; eauto; dcr. destruct H21.
            eexists; split; eauto.
            right. eapply CIH. eauto.
            left; eapply star2_refl.
            eauto.
        + econstructor 3; eauto.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H9); eauto.
      - (* plus step <-> err *)
        eapply plus2_star2 in H6.
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (star2_reach_normal H11 H12 step_internally_deterministic H6).
        edestruct (sim'_terminate_2 H2 H12 H7); eauto; dcr.
        destruct H15.
        + pfold.
          eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
          rewrite H10 in H8.
          econstructor 3; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
      - (*  plus step <-> term *)
        eapply plus2_star2 in H6.
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (star2_reach_normal H11 H13 step_internally_deterministic H6).
        edestruct (sim'_terminate_2 H2 H13 H7); eauto; dcr.
        destruct H17.
        + pfold.
          eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
          rewrite H10 in H8.
          econstructor 4; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H9); eauto.
      - (* activated <-> plus step *)
          pfold.
          eapply star2_trans in H6; eauto. clear H2; simpl in *.
          eapply plus2_star2 in H13.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply sim'_reduction_closed_1 in H15; eauto.
          destruct (sim'_activated H8 H15); dcr.
          econstructor 2. eauto.
          eapply plus2_star2 in H14.
          eapply (star2_trans H14 H12). eauto.
          eauto.
          + intros.
            edestruct H9 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H16 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto. left. eapply star2_refl.
          + intros.
            edestruct H19 as [? [? ?]]; eauto; isabsurd.
            edestruct H10 as [? [? [?|?]]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto.
            left; eapply star2_refl.
      - (* activated <-> activated *)
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (both_activated H6 H13); eauto. subst.
        pfold. econstructor 2; eauto; intros.
        + edestruct H9; eauto. dcr.
          edestruct H17; eauto; dcr.
          eexists. split; eauto.
          destruct H19, H21; isabsurd.
          right. eapply CIH; try eapply H11; try eapply H19.
          left. eapply star2_refl.
        + edestruct H18; eauto. dcr.
          edestruct H10; eauto; dcr.
          eexists. split; eauto.
          destruct H19, H21; isabsurd.
          right. eapply CIH; try eapply H11; try eapply H19.
          left. eapply star2_refl.
      - (* activated <-> err *)
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6 H8 H14); eauto.
      - (* activated <-> term *)
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6 H8 H14); eauto.
      - (* term <-> plus step *)
        case_eq (result σ1'); intros.
        + eapply plus2_star2 in H12.
          eapply star2_trans in H7; eauto. clear H2; simpl in *.
          exploit (star2_reach_normal H7 H9 step_internally_deterministic H12).
          assert (result σ2' <> None) by congruence.
          edestruct (sim'_terminate H2 H9 H11 H14); eauto; dcr.
          pfold.
          econstructor 4. rewrite H19 in H4. eapply H4.
          eauto.
          eapply plus2_star2 in H13.
          eapply (star2_trans H13 H16); eauto.
          eauto. eauto.
        + pfold. econstructor 3; eauto.
      - eapply star2_trans in H7; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H12 H14 H7); eauto.
      - (* term <-> err *)
        pfold.
        eapply star2_trans in H7; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H14. do 2 eexists; eauto.
      - (* term <-> term *)
        pfold.
        eapply star2_trans in H7; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 4; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 4; eauto. congruence.
          * exfalso. eapply H15. do 2 eexists; eauto.
    }
Qed.

Lemma sim'_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim' σ1 σ2 -> sim' σ2 σ3 -> sim' σ1 σ3.
Proof.
  intros. eauto using (sim'_zigzag (S1:=S1) (S2:=S2) (S3:=S3)), star2_refl.
Qed.

Lemma sim_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim σ1 σ2
    -> sim σ2 σ3
    -> sim σ1 σ3.
Proof.
  intros. eapply sim'_sim.
  eapply sim_sim' in H2.
  eapply sim_sim' in H3.
  eapply (sim'_trans H2 H3).
Qed.

Arguments sim_trans [S1] {H} σ1 [S2] {H0} σ2 [S3] {H1} σ3 _ _.


Lemma sim'_reduction_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S')
  : sim' σ1 σ2
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sim' σ1' σ2'.
Proof.
  intros.
  eapply sim'_trans. eapply sim'_reduction_closed_1; eauto.
  eapply sim'_reduction_closed_2; eauto.
  eapply sim'_refl.
Qed.

Instance sim_progeq {S} `{StateType S} : ProgramEquivalence S S.
Proof.
econstructor. instantiate (1:=paco2 (@sim_gen S _ S _)).
eapply paco2_mon.
Defined.

Lemma simL_mon (r r0:rel2 F.state (fun _ : F.state => F.state)) A AR L1 L2 (AL:list A)
:  inRel (simB sim_progeq r AR) AL L1 L2
  -> (forall x0 x1 : F.state, r x0 x1 -> r0 x0 x1)
  ->  inRel (simB sim_progeq r0 AR) AL L1 L2.
Proof.
  intros. eapply inRel_mon. eauto.
  intros. inv H1. econstructor; eauto.
  intros. eapply paco2_mon. eapply H4; eauto. eauto.
Qed.

Lemma mutual_block_extension r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simL' sim_progeq r AR ALX L1 L2)
      (CIH: forall a
              (Z Z' : params)
              (Yv Y'v : list val) (s s' : stmt) (n : nat),
          get F1 n (Z, s) ->
          get F2 n (Z', s') ->
          get AL n a ->
          ArgRel E1 E2 a Yv Y'v ->
          r ((mapi (F.mkBlock E1) F1 ++ L1)%list, E1 [Z <-- List.map Some Yv], s)
            ((mapi (F.mkBlock E2) F2 ++ L2)%list, E2 [Z' <-- List.map Some Y'v], s'))
  :

    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteq' sim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
        BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
        ParamRel a Z Z')
    -> mutual_block
        (simB sim_progeq r AR (AL ++ ALX) (mapi (F.mkBlock E1) F1 ++ L1)%list
              (mapi (F.mkBlock E2) F2 ++ L2)%list) i AL'
        (mapi_impl (F.mkBlock E1) i F1')
        (mapi_impl (F.mkBlock E2) i F2').
Proof.
  intros.
  assert (LEN1':length_eq F1' F2').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  assert (LEN2':length_eq AL' F1').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  general induction LEN1'. inv LEN2'.
  - simpl. econstructor.
  - inv LEN2'.
    simpl. econstructor; simpl; eauto.
    + eapply IHLEN1'; eauto using drop_shift_1.
    + destruct x,y. edestruct H as [[B1 B2] [B3 B4]]; eauto using drop_eq.
      econstructor; eauto.
      intros. hnf.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H0; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H5; eauto.
      congruence. reflexivity.
      simpl. right. orewrite (i-i=0); simpl.
      eapply CIH; eauto using drop_eq.
Qed.


Lemma fix_compatible r A AR (a:A) AL F F' E E' Z Z' L L' Yv Y'v s s' n AL'
(LEN1:length F = length F') (LEN2:length AL' = length F)
  : simL' sim_progeq r AR AL L L'
    -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                             fexteq' sim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                             /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                             /\ ParamRel a Z Z')
    -> get F n (Z,s)
    -> get F' n (Z',s')
    -> get AL' n a
    -> ArgRel E E' a Yv Y'v
    -> sim'r r
              ((mapi (F.mkBlock E) F ++ L)%list, E [Z <-- List.map Some Yv], s)
              ((mapi (F.mkBlock E') F' ++ L')%list, E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto.
  hnf; intros.
  econstructor; eauto.
  - eapply simL_mon; eauto.
  - eapply mutual_block_extension; eauto.
    eapply simL_mon; eauto.
Qed.

Lemma mutual_block_extension_simple r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simL' sim_progeq r AR ALX L1 L2)
  :
    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteq' sim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
        BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
        ParamRel a Z Z')
    -> mutual_block
        (simB sim_progeq r AR (AL ++ ALX) (mapi (F.mkBlock E1) F1 ++ L1)%list
              (mapi (F.mkBlock E2) F2 ++ L2)%list) i AL'
        (mapi_impl (F.mkBlock E1) i F1')
        (mapi_impl (F.mkBlock E2) i F2').
Proof.
  intros.
  assert (LEN1':length_eq F1' F2').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  assert (LEN2':length_eq AL' F1').
  eapply length_length_eq. subst; eauto using drop_length_stable.
  general induction LEN1'. inv LEN2'.
  - simpl. econstructor.
  - inv LEN2'.
    simpl. econstructor; simpl; eauto.
    + eapply IHLEN1'; eauto using drop_shift_1.
    + destruct x,y. edestruct H as [[B1 B2] [B3 B4]]; eauto using drop_eq.
      econstructor; eauto.
      intros. hnf.
      pfold. econstructor; try eapply plus2O.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H0; eauto.
      congruence. reflexivity.
      econstructor; eauto. eapply get_app.
      eapply mapi_get_1. eapply drop_eq. eauto. simpl.
      edestruct RelsOK; eauto. exploit omap_length; try eapply H5; eauto.
      congruence. reflexivity.
      simpl. left. orewrite (i-i=0); simpl.
      eapply fix_compatible; eauto.
      eauto using drop_eq. eauto using drop_eq. eauto using drop_eq.
Qed.

Lemma simL_extension' r A AR (AL AL':list A) F F' E E' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
: simL' sim_progeq r AR AL L L'
  -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                         fexteq' sim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                         /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                         /\ ParamRel a Z Z')
  -> simL' sim_progeq r AR (AL' ++ AL) (mapi (F.mkBlock E) F ++ L) (mapi (F.mkBlock E') F' ++ L').
Proof.
  intros.
  hnf; intros.
  econstructor; eauto.
  eapply mutual_block_extension_simple; eauto.
Qed.


Lemma get_drop_lab0 (L:F.labenv) l blk
:  get L (counted l) blk
   -> get (drop (labN l) L) (counted (LabI 0)) blk.
Proof.
  intros. eapply drop_get; simpl. orewrite (labN l + 0 = labN l); eauto.
Qed.

Lemma drop_get_lab0 (L:F.labenv) l blk
: get (drop (labN l) L) (counted (LabI 0)) blk
  -> get L (counted l) blk.
Proof.
  intros. eapply get_drop in H; simpl in *. orewrite (labN l + 0 = labN l) in H; eauto.
Qed.

Ltac simpl_get_drop :=
  repeat match goal with
  | [ H : get (drop (?n - _) ?L) _ _, H' : get ?L ?n ?blk, STL: sawtooth ?L |- _ ]
    => eapply get_drop in H;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X, H;
        orewrite (n - F.block_n blk + F.block_n blk = n) in H; clear X
  | [ H' : get ?L ?n ?blk, STL: sawtooth ?L |- get (drop (?n - _) ?L) _ _ ]
    => eapply drop_get;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X; simpl;
        orewrite (n - F.block_n blk + F.block_n blk = n); clear X
  end.

Ltac simpl_minus :=
  repeat match goal with
  | [ H : context [?n - ?n] |- _ ]
    => orewrite (n - n = 0) in H
  end.

Lemma sim_drop_shift r l L E Y L' E' Y' blk blk' (STL:sawtooth L) (STL':sawtooth L')
  : get L (labN l) blk
  -> get L' (labN l) blk'
  -> paco2 (@sim_gen F.state _ F.state _) r
          (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
          (drop (labN l - block_n blk') L', E', stmtApp (LabI (block_n blk')) Y')
  -> paco2 (@sim_gen F.state _ F.state _) r (L, E, stmtApp l Y)
          (L', E', stmtApp l Y').
Proof.
  intros. pinversion H1; subst.
  - eapply plus2_destr_nil in H2.
    eapply plus2_destr_nil in H3.
    destruct H2; destruct H3; dcr. inv H3.
    simpl in *. inv H5; simpl in *.
    simpl_get_drop; repeat get_functional.
    simpl_minus.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  - inv H2.
    + exfalso. destruct H4 as [? [? ?]]. inv H4.
    + inv H3.
      * exfalso. destruct H5 as [? [? ?]]. inv H5.
      * inv H9; inv H12; simpl in *.
        pfold. subst yl yl0.
        simpl_get_drop; repeat get_functional.
        simpl_minus.
        econstructor; try eapply star2_plus2.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        left. pfold. econstructor 2; try eapply star2_refl; eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; simpl; eauto using star2_refl. eauto.
      stuck2. eapply H4.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_drop. eauto.
    + inv H6.
      pfold. econstructor 3; try eapply H2; eauto.
      destruct yl; isabsurd.
      simpl in *. simpl_get_drop. repeat get_functional.
      eapply (star2_silent).
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2. eapply H5.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_drop. eauto.
    + inv H8. inv H4; simpl in *.
      * pfold. subst. econstructor 3; try eapply H2; eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
      * inv H11.
        pfold. econstructor 4; try eapply H2; eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
        simpl in *. simpl_get_drop. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. subst.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
Qed.

Ltac simpl_get_dropI :=
  repeat match goal with
  | [ H : get (drop (?n - _) ?L) _ _, H' : get ?L ?n ?blk, STL: sawtooth ?L |- _ ]
    => eapply get_drop in H;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X, H;
        orewrite (n - I.block_n blk + I.block_n blk = n) in H; clear X
  | [ H' : get ?L ?n ?blk, STL: sawtooth ?L |- get (drop (?n - _) ?L) _ _ ]
    => eapply drop_get;
      let X := fresh "LT" in pose proof (sawtooth_smaller STL H') as X;
        simpl in X; simpl;
        orewrite (n - I.block_n blk + I.block_n blk = n); clear X
  end.

Lemma sim_drop_shift_I r l (L:I.labenv) E Y (L':I.labenv) E' Y' blk blk' (STL:sawtooth L) (STL':sawtooth L')
  : get L (labN l) blk
  -> get L' (labN l) blk'
  -> paco2 (@sim_gen I.state _ I.state _) r
          (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
          (drop (labN l - block_n blk') L', E', stmtApp (LabI (block_n blk')) Y')
  -> paco2 (@sim_gen I.state _ I.state _) r (L, E, stmtApp l Y)
          (L', E', stmtApp l Y').
Proof.
  intros. pinversion H1; subst.
  - eapply plus2_destr_nil in H2.
    eapply plus2_destr_nil in H3.
    dcr. inv H5; simpl in *. inv H6; simpl in *.
    simpl_get_dropI. repeat get_functional.
    simpl_minus.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  - inv H2.
    + exfalso. destruct H4 as [? [? ?]]. inv H4.
    + inv H3.
      * exfalso. destruct H5 as [? [? ?]]. inv H5.
      * inv H9; inv H12; simpl in *.
        pfold. subst yl yl0.
        simpl_get_dropI; repeat get_functional.
        simpl_minus.
        econstructor; try eapply star2_plus2.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
        left. pfold. econstructor 2; try eapply star2_refl; eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; simpl; eauto using star2_refl. eauto.
      stuck2. eapply H4.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_dropI. eauto.
    + inv H6.
      pfold. econstructor 3; try eapply H2; eauto.
      destruct yl; isabsurd.
      simpl in *. simpl_get_dropI. repeat get_functional.
      eapply star2_silent.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
  - inv H3; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. eauto.
      stuck2. eapply H5.
      do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl. simpl_get_dropI. eauto.
    + inv H8. inv H4; simpl in *.
      * pfold. subst. econstructor 3; try eapply H2; eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
      * inv H11.
        pfold. econstructor 4; try eapply H2; eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
        simpl in *. simpl_get_dropI. repeat get_functional.
        eapply star2_silent.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. subst.
        eauto. rewrite drop_drop in H8. simpl_minus. simpl in *. eauto.
Qed.

Ltac single_step :=
  match goal with
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = true |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = false |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor 3; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : val2bool _ = false |- _ ] => econstructor 3 ; try eassumption; try reflexivity
    | [ H : step (?L, _ , stmtApp ?l _) _, H': get ?L (counted ?l) _ |- _] =>
      econstructor; try eapply H'; eauto
    | [ H': get ?L (counted ?l) _ |- step (?L, _ , stmtApp ?l _) _] =>
      econstructor; try eapply H'; eauto
    | _ => econstructor; eauto
  end.

Ltac one_step := eapply simSilent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac no_step := eapply simTerm;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2
                | stuck2  ].

Ltac err_step := eapply simErr;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2  ].

Ltac step_activated :=
  match goal with
    | [ H : omap (exp_eval ?E) ?Y = Some ?vl
        |- activated (_, ?E, stmtExtern ?x ?f ?Y ?s) ] =>
      eexists (ExternI f vl default_val); eexists; try (now (econstructor; eauto))
  end.

Ltac extern_step :=
  let STEP := fresh "STEP" in
  eapply simExtern;
    [ eapply star2_refl
    | eapply star2_refl
    | try step_activated
    | try step_activated
    | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
    | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
    ].


Ltac pone_step := pfold; eapply sim'Silent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac pno_step :=
  pfold; eapply sim'Term;
  [ | eapply star2_refl | eapply star2_refl | | ];
  [ repeat get_functional; try reflexivity
  | repeat get_functional; stuck2
  | repeat get_functional; stuck2 ].

Ltac pextern_step :=
  let STEP := fresh "STEP" in
  pfold; eapply sim'Extern;
  [ eapply star2_refl
  | eapply star2_refl
  | try step_activated
  | try step_activated
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  | intros ? ? STEP; inv STEP; eexists; split; [econstructor; eauto | ]
  ].
