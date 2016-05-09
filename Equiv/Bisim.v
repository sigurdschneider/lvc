Require Import List.
Require Import Util IL AllInRel Sawtooth.
Require Export SmallStepRelations StateType paco Equiv.

Set Implicit Arguments.
Unset Printing Records.

(** * Simulation *)
(** A characterization of simulation equivalence on states; works only for deterministic semantics *)

CoInductive bisim {S} `{StateType S} {S'} `{StateType S'}  : S -> S' -> Prop :=
  | bisimSilent (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> bisim σ1' σ2'
      -> bisim σ1 σ2
  | bisimExtern (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ bisim σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ bisim σ1' σ2')
      -> bisim pσ1 pσ2
  | bisimTerm (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> bisim σ1 σ2.

Arguments bisim [S] {H} [S'] {H0} _ _.

(** Simulation is an equivalence relation *)
Lemma bisim_refl {S} `{StateType S} (σ:S)
      : bisim σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply bisimExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply bisimSilent; eauto using plus2O.
  - eapply bisimTerm; eauto using star2_refl.
Qed.

Lemma bisim_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
      : bisim σ σ' -> bisim σ' σ.
Proof.
  revert σ σ'. cofix; intros.
  inv H1.
  - eapply bisimSilent; eauto.
  - eapply bisimExtern; eauto; intros.
    edestruct H7; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.
  - eapply bisimTerm; eauto using star2_refl.
Qed.

Inductive bisim_gen
          {S} `{StateType S} {S'} `{StateType S'} (r: S -> S' -> Prop)  : S -> S' -> Prop :=
  | bisim'Silent (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> r σ1' σ2'
      -> bisim_gen r σ1 σ2
  | bisim'Extern (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ r σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ r σ1' σ2')
      -> bisim_gen r pσ1 pσ2
  | bisim'Term (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> bisim_gen r σ1 σ2.

Arguments bisim_gen [S] {H} [S'] {H0} r _ _.

Hint Constructors bisim_gen.

Definition bisim' {S} `{StateType S} {S'} `{StateType S'}  (σ1:S) (σ2:S')
  := paco2 (@bisim_gen S _ S' _) bot2 σ1 σ2.
Hint Unfold bisim'.

Definition bisim'r {S} `{StateType S} {S'} `{StateType S'} r (σ1:S) (σ2:S')
  := paco2 (@bisim_gen S _ S' _) r σ1 σ2.
Hint Unfold bisim'.

Lemma bisim_gen_mon {S} `{StateType S} {S'} `{StateType S'}
: monotone2 (@bisim_gen S _ S' _).
Proof.
  hnf; intros. inv IN.
  - econstructor 1; eauto.
  - econstructor 2; eauto; intros.
    edestruct H5; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.
  - econstructor 3; eauto.
Qed.

Arguments bisim_gen_mon [S] {H} [S'] {H0} [x0] [x1] r r' IN LE.

Hint Resolve bisim_gen_mon : paco.

Lemma bisim_bisim' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: bisim σ1 σ2 -> bisim' σ1 σ2.
Proof.
  revert σ1 σ2. pcofix CIH.
  intros. pfold.
  inv H2.
  - econstructor; eauto.
  - econstructor 2; eauto; intros.
    + edestruct H6; eauto; dcr. eexists; eauto.
    + edestruct H7; eauto; dcr. eexists; eauto.
  - econstructor 3; eauto.
Qed.


Lemma bisim'_bisim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: bisim' σ1 σ2 -> bisim σ1 σ2.
Proof.
  revert σ1 σ2. cofix CIH.
  intros.
  (assert (bisim_gen (paco2 (bisim_gen (S':=S')) bot2 \2/ bot2) σ1 σ2)).
  punfold H1.
  destruct H2. destruct H4.
  - econstructor; eauto.
  - exfalso; intuition.
  - econstructor 2; eauto; intros.
    + edestruct H6; eauto; dcr. destruct H11. eexists; eauto. exfalso; intuition.
    + edestruct H7; eauto; dcr. destruct H11. eexists; eauto. exfalso; intuition.
  - econstructor 3; eauto.
Qed.

Lemma bisim'_refl {S} `{StateType S} (σ:S)
      : bisim' σ σ.
Proof.
  eapply bisim_bisim'. eapply bisim_refl.
Qed.

Lemma bisim'_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
      : bisim' σ σ' -> bisim' σ' σ.
Proof.
  intros. eapply bisim_bisim'. eapply bisim_sym. eapply bisim'_bisim; eauto.
Qed.



Lemma bisim'_expansion_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S') r
  : bisim'r r σ1' σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> bisim'r r σ1 σ2.
Proof.
  intros. pinversion H1; subst; pfold.
  - econstructor; eauto.
    + eapply (star2_plus2_plus2 H2 H4).
    + eapply (star2_plus2_plus2 H3 H5).
  - econstructor 2.
    + eapply (star2_trans H2 H4).
    + eapply (star2_trans H3 H5).
    + eauto.
    + eauto.
    + intros. edestruct H6; eauto.
    + intros. edestruct H7; eauto.
  - econstructor 3; eauto using star2_trans.
    + eapply (star2_trans H2 H5).
    + eapply (star2_trans H3 H6).
Qed.



Lemma bisim'_reduction_closed_1 {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S')
  : bisim' σ1 σ2
    -> star2 step σ1 nil σ1'
    -> bisim' σ1' σ2.
Proof.
  intros. eapply star2_star2n in H2. destruct H2 as [n ?].
  revert σ1 σ1' σ2 H1 H2.
  pattern n.
  eapply size_induction with (f:=id); intros; unfold id in *; simpl in *.
  pinversion H2; subst.
  - inv H3; eauto.
    eapply plus2_plus2n in H4. destruct H4. eapply plus2n_star2n in H4.
    edestruct (star2n_reach H3 H4); eauto. eapply H.
    + eapply bisim'_expansion_closed. eapply H6.
      eauto using star2n_star2. eauto using plus2_star2.
    + eapply H1; try eapply H9. omega.
      eapply bisim'_expansion_closed. eapply H6. eapply star2_refl.
      eauto using plus2_star2.
  - eapply star2n_star2 in H3. eapply activated_star_reach in H3; eauto.
  - pfold. eapply star2n_star2 in H3.
    eapply star2_reach_normal in H3; eauto. eapply H.
Qed.

Lemma bisim'_terminate {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2:S2)
: star2 step σ1 nil σ1'
  -> normal2 step σ1'
  -> bisim' σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ normal2 step σ2' /\ result σ1' = result σ2'.
Proof.
  intros. general induction H1.
  - pinversion H3; subst.
    + exfalso. eapply H2. inv H1; do 2 eexists; eauto.
    + exfalso. eapply star2_normal in H1; eauto. subst.
      eapply (activated_normal _ H5); eauto.
    + eapply star2_normal in H4; eauto; subst.
      eexists; split; eauto.
  - destruct y; isabsurd. simpl.
    eapply IHstar2; eauto.
    eapply bisim'_reduction_closed_1; eauto using star2, star2_silent.
Qed.


Lemma bisim'_activated {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> bisim' σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\
                 (paco2 (bisim_gen (S':=S2)) bot2 σ1'' σ2''))
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\
                 (paco2 (bisim_gen (S':=S2)) bot2 σ1' σ2'')).
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
Qed.

Lemma plus_step_activated {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2a σ2' σ2b σ4:S2)
      {S3} `{StateType S3} (σ3 σ5:S3)  (r : S1 -> S3 -> Prop)
      (H6:plus2 step σ2a nil σ2')
      (H2:star2 step σ2a nil σ2b)
      (H10:star2 step σ2b nil σ4)
      (H11 : star2 step σ3 nil σ5)
      (H4 : plus2 step σ1 nil σ1')
      (H13 : activated σ5)
      (H12 : activated σ4)
      (H7 : paco2 (bisim_gen (S':=S2)) bot2 σ1' σ2')
      (H14 : forall (evt : event) (σ1' : S2),
               step σ4 evt σ1' ->
               exists σ2' : S3,
          step σ5 evt σ2' /\
          (paco2 (bisim_gen (S':=S3)) bot2 σ1' σ2' \/ bot2 σ1' σ2'))
      (H15 : forall (evt : event) (σ2' : S3),
               step σ5 evt σ2' ->
               exists σ1' : S2,
                 step σ4 evt σ1' /\
                 (paco2 (bisim_gen (S':=S3)) bot2 σ1' σ2' \/ bot2 σ1' σ2'))
      (CIH : forall (σ1 : S1) (σ2a σ2b : S2) (σ3 : S3),
               bisim' σ1 σ2a ->
               star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a ->
               bisim' σ2b σ3 -> r σ1 σ3)
: paco2 (bisim_gen (S':=S3)) r σ1 σ3.
Proof.
  pfold.
  eapply star2_trans in H10; eauto. clear H2; simpl in *.
  eapply plus2_star2 in H6.
  exploit (activated_star_reach H12 H10 H6); eauto.
  eapply bisim'_sym in H7.
  eapply bisim'_reduction_closed_1 in H7; eauto.
  destruct (bisim'_activated H12 H7); dcr.
  econstructor 2.
  eapply plus2_star2 in H4.
  eapply (star2_trans H4 H5). eapply H11.
  eauto. eauto.
  + intros. edestruct H17; eauto. destruct H16.
    edestruct H14; eauto. dcr.
    destruct H21; isabsurd.
    eexists; split; eauto.
    right. eapply CIH. eapply bisim'_sym in H18. eauto.
    left. eapply star2_refl. eauto.
  + intros. edestruct H15; eauto; dcr.
    edestruct H8; eauto; dcr. destruct H16.
    eexists; split; eauto. destruct H19; isabsurd.
    right. eapply CIH. eapply bisim'_sym. eapply H20.
    left; eapply star2_refl.
    eauto.
Qed.

Lemma bisim'_zigzag {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2a σ2b:S2) {S3} `{StateType S3} (σ3:S3)
  : bisim' σ1 σ2a
    -> (star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a)
    -> bisim' σ2b σ3
    -> bisim' σ1 σ3.
Proof.
  revert σ1 σ2a σ2b σ3. pcofix CIH; intros.
  destruct H4.
  - {
      pinversion H3; pinversion H5; subst.
      - pfold. eapply star2_plus2_plus2 in H10; eauto. clear H2; simpl in *.
        edestruct (plus2_reach H6 H10); eauto.
        eapply H0.
      - (* plus step <-> activated *)
        eapply (@plus_step_activated S1 _ _ _ S2 _ _ _ _ _ S3); eauto.
      - (* plus step <-> term *)
        eapply star2_trans in H11; eauto. clear H2; simpl in *.
        eapply plus2_star2 in H6.
        exploit (star2_reach_normal H11 H13 step_internally_deterministic H6);
          eauto.
        edestruct (bisim'_terminate H2 H13 (bisim'_sym H7)); eauto; dcr.
        pfold.
        econstructor 3. rewrite H17 in H10. eapply H10.
        eapply plus2_star2 in H4.
        eapply (star2_trans H4 H9); eauto.
        eauto. eauto. eauto.
      - (* plus step <-> activated *)
          pfold.
          eapply plus2_star2 in H13.
          eapply star2_trans in H13; eauto. clear H2; simpl in *.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply bisim'_reduction_closed_1 in H15; eauto.
          destruct (bisim'_activated H8 H15); dcr.
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
      - (* activated <-> term *)
        eapply star2_trans in H14; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6); eauto.
      - (* term <-> plus step *)
        eapply plus2_star2 in H12.
        eapply star2_trans in H12; eauto. clear H2; simpl in *.
        exploit (star2_reach_normal H7 H9 step_internally_deterministic H12); eauto.
        edestruct (bisim'_terminate H2 H9 H14); eauto; dcr.
        pfold.
        econstructor 3. rewrite H17 in H4. eapply H4.
        eauto.
        eapply plus2_star2 in H13.
        eapply (star2_trans H13 H11); eauto.
        eauto. eauto.
      - eapply star2_trans in H12; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H12 H14 H7); eauto.
      - (* term <-> term *)
        pfold.
        eapply star2_trans in H13; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H15. do 2 eexists; eauto.
    }
  -{
      pinversion H3; pinversion H5; subst.
      - pfold. eapply star2_plus2_plus2 in H6; eauto. clear H2; simpl in *.
        edestruct (plus2_reach H6 H10); eauto.
        eapply H0.
      - (* plus step <-> activated *)
          pfold.
          eapply plus2_star2 in H6.
          eapply star2_trans in H6; eauto. clear H2; simpl in *.
          exploit (activated_star_reach H12 H10 H6); eauto.
          eapply bisim'_sym in H7.
          eapply bisim'_reduction_closed_1 in H7; eauto.
          destruct (bisim'_activated H12 H7); dcr.
          econstructor 2.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H9). eapply H11.
          eauto. eauto.
          + intros.
            edestruct H19 as [? [? ?]]; eauto; isabsurd.
            edestruct H14 as [? [? [?|?]]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH. eapply bisim'_sym in H20; eauto.
            left. eapply star2_refl. eauto.
          + intros.
            edestruct H15 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H16 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH. eapply bisim'_sym in H22; eauto.
            left; eapply star2_refl. eauto.
      - (* plus step <-> term *)
        eapply plus2_star2 in H6.
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (star2_reach_normal H11 H13 step_internally_deterministic H6);
          eauto.
        edestruct (bisim'_terminate H2 H13 (bisim'_sym H7)); eauto; dcr.
        pfold.
        econstructor 3. rewrite H17 in H10. eapply H10.
        eapply plus2_star2 in H4.
        eapply (star2_trans H4 H9); eauto.
        eauto. eauto. eauto.
      - (* plus step <-> activated *)
          pfold.
          eapply star2_trans in H6; eauto. clear H2; simpl in *.
          eapply plus2_star2 in H13.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply bisim'_reduction_closed_1 in H15; eauto.
          destruct (bisim'_activated H8 H15); dcr.
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
        + edestruct H9 as [? [? [?|?]]]; eauto; isabsurd.
          edestruct H17 as [? [? [?|?]]]; eauto; isabsurd.
          eexists; split; eauto.
          right. eapply CIH; eauto. left. eapply star2_refl.
        + edestruct H18 as [? [? [?|?]]]; eauto; isabsurd.
          edestruct H10 as [? [? [?|?]]]; eauto; isabsurd.
          eexists; split; eauto.
          right. eapply CIH; eauto. left. eapply star2_refl.
      - (* activated <-> term *)
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H6 H8 H14); eauto.
      - (* term <-> plus step *)
        eapply star2_trans in H7; eauto. clear H2; simpl in *.
        eapply plus2_star2 in H12.
        exploit (star2_reach_normal H7 H9 step_internally_deterministic H12); eauto.
        edestruct (bisim'_terminate H2 H9 H14); eauto; dcr.
        pfold.
        econstructor 3. rewrite H17 in H4. eapply H4.
        eauto.
        eapply plus2_star2 in H13.
        eapply (star2_trans H13 H11); eauto.
        eauto. eauto.
      - eapply star2_trans in H7; eauto. clear H2; simpl in *.
        exfalso; eapply (activated_normal_star H12 H14 H7); eauto.
      - (* term <-> term *)
        pfold.
        eapply star2_trans in H7; eauto. clear H2; simpl in *.
        edestruct (star2_reach H7 H13); eauto. eapply H0.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H9. do 2 eexists; eauto.
        + inv H2.
          * econstructor 3; eauto. congruence.
          * exfalso. eapply H15. do 2 eexists; eauto.
    }

Qed.

Lemma bisim'_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : bisim' σ1 σ2
    -> bisim' σ2 σ3
    -> bisim' σ1 σ3.
Proof.
  intros. eauto using (bisim'_zigzag (S1:=S1) (S2:=S2) (S3:=S3)), star2_refl.
Qed.

Lemma bisim_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : bisim σ1 σ2
    -> bisim σ2 σ3
    -> bisim σ1 σ3.
Proof.
  intros. eapply bisim'_bisim.
  eapply bisim_bisim' in H2.
  eapply bisim_bisim' in H3.
  eapply (bisim'_trans H2 H3).
Qed.

Lemma bisim'_reduction_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S')
  : bisim' σ1 σ2
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> bisim' σ1' σ2'.
Proof.
  intros. eapply bisim'_trans.
  eapply bisim'_reduction_closed_1; eauto.
  eapply bisim'_sym.
  eapply bisim'_sym in H1.
  eapply bisim'_reduction_closed_1; eauto.
  eapply bisim'_refl.
Qed.

Instance bisim_progeq {S} `{StateType S} : ProgramEquivalence S S.
Proof.
  econstructor. instantiate (1:=(paco2 (@bisim_gen S _ S _))).
  eapply paco2_mon.
Defined.

Definition same_call (e e':extern) := extern_fnc e = extern_fnc e' /\ extern_args e = extern_args e'.

Definition receptive S `{StateType S} :=
  forall σ σ' ext, step σ (EvtExtern ext) σ'
              -> forall ext', same_call ext ext' -> exists σ'', step σ (EvtExtern ext') σ''.

Arguments receptive S [H].

Definition determinate S `{StateType S} :=
  forall σ σ' σ'' ext ext', step σ (EvtExtern ext) σ'
              -> step σ (EvtExtern ext') σ'' -> same_call ext ext'.

Arguments determinate S [H].

Lemma bisimExternDet {S} `{StateType S} {S'} `{StateType S'} (pσ1:S) (pσ2:S') (σ1:S) (σ2:S')
      (RCPT:receptive S) (DET:determinate S')
: star2 step pσ1 nil σ1
  -> star2 step pσ2 nil σ2
  -> activated σ1
  -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ bisim σ1' σ2')
  -> bisim pσ1 pσ2.
Proof.
  intros.
  econstructor 2; eauto.
  - inv H3. dcr. edestruct H4; eauto. firstorder.
  - intros. inv H3. dcr. exploit H4; eauto; dcr.
    destruct evt.
    + exploit DET. eauto. eapply H5.
      exploit RCPT; eauto. dcr.
      exploit H4. eapply H11. dcr.
      eexists; split. eapply H11.
      exploit step_externally_determined. Focus 3.
      instantiate (2:=σ2') in H8. rewrite H8. eapply H14.
      eauto. eauto.
    + exfalso. exploit step_internally_deterministic; eauto; dcr. congruence.
Qed.
