Require Import Util AllInRel Sawtooth Get.
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

Lemma sim_Y_left S `{StateType S} S' `{StateType S'} r σA1 σB1 σ1' σ2
  : paco2 (@sim_gen S _ S _) r
            σA1
            σ2
    -> step σA1 EvtTau σ1'
    -> step σB1 EvtTau σ1'
    -> paco2 (@sim_gen S _ S _) r
            σB1
            σ2.
Proof.
  intros SIM Step1 Step2.
  pinversion SIM; subst; intros; relsimpl; pfold;
    eauto using sim_gen, star2_silent, star2_plus2.
Qed.

Lemma sim_Y_right  S `{StateType S} S' `{StateType S'} r σ1 σA2 σB2 σ2'
  : paco2 (@sim_gen S _ S' _) r σ1 σA2
    -> step σA2 EvtTau σ2'
    -> step σB2 EvtTau σ2'
    -> paco2 (@sim_gen S _ S' _) r σ1 σB2.
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
  - relsimpl.
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
  - relsimpl.
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
    intros. edestruct H7; eauto; dcr. destruct H12; eauto. inv H10.
    intros. edestruct H8; eauto; dcr. destruct H12; eauto. inv H10.
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
