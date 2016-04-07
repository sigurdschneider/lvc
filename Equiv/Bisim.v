Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel Sawtooth.
Require Export EventsActivated StateType paco Equiv.

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
    eapply bisim'_reduction_closed_1; eauto using star2.
    eapply (S_star2 _ _ H); eauto using star2_refl.
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
        exploit (star2_reach_normal H11 H6); eauto. eapply H0.
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
        exploit (star2_reach_normal H7 H12); eauto. eapply H0.
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
        exploit (star2_reach_normal H11 H6); eauto. eapply H0.
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
        exploit (star2_reach_normal H7 H12); eauto. eapply H0.
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
(*
Class BisimRelation (A:Type) := {
    ParamRel : A-> list var -> list var -> Prop;
    ArgRel : onv val -> onv val -> A-> list val -> list val -> Prop;
    BlockRel : A-> F.block -> F.block -> Prop;
    RelsOK : forall E E' a Z Z' VL VL', ParamRel a Z Z' -> ArgRel E E' a VL VL' -> length Z = length VL /\ length Z' = length VL'
}.

Inductive simB (r:rel2 F.state (fun _ : F.state => F.state)) {A} (AR:BisimRelation A)  : F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' V V' Z Z' s s'
  : ParamRel a Z Z'
    -> BlockRel a (F.blockI V Z s) (F.blockI V' Z' s')
    -> (forall E E' Y Y' Yv Y'v,
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> ArgRel V V' a Yv Y'v
         -> paco2 (@bisim_gen F.state _ F.state _) r (L, E, stmtApp (LabI 0) Y)
                        (L', E', stmtApp (LabI 0) Y'))
    -> simB r AR L L' a (F.blockI V Z s) (F.blockI V' Z' s').

Definition simL' (r:rel2 F.state (fun _ : F.state => F.state))
           {A} AR (AL:list A) L L' := AIR5 (simB r AR) L L' AL L L'.

Definition fexteq'
           {A} AR (a:A) (AL:list A) E Z s E' Z' s' :=
  forall VL VL' L L' (r:rel2 F.state (fun _ : F.state => F.state)),
    ArgRel E E' a VL VL'
    -> simL' r AR AL L L'
    -> length Z = length VL
    -> length Z' = length VL'
    -> paco2 (@bisim_gen F.state _ F.state _) r (L, E[Z <-- List.map Some VL], s)
            (L', E'[Z' <-- List.map Some VL'], s').
*)

Instance bisim_progeq : ProgramEquivalence F.state F.state.
constructor. eapply (paco2 (@bisim_gen F.state _ F.state _)).
Defined.

Lemma simL_mon (r r0:rel2 F.state (fun _ : F.state => F.state)) A AR L1 L2 (AL:list A)
:  inRel (simB bisim_progeq r AR) AL L1 L2
  -> (forall x0 x1 : F.state, r x0 x1 -> r0 x0 x1)
  ->  inRel (simB bisim_progeq r0 AR) AL L1 L2.
Proof.
  intros. eapply inRel_mon. eauto.
  intros. inv H1. econstructor; eauto.
  intros. eapply paco2_mon. eapply H4; eauto. eauto.
Qed.

(*
Lemma subst_lemma A AR (a:A) AL s s' V V' E E' Z Z' L1 L2 t t'
: fexteq' bisim_progeq AR a (a::AL) E Z s E' Z' s'
  -> ParamRel a Z Z'
  -> BlockRel a (F.blockI E Z s 0) (F.blockI E' Z' s' 0)
  -> simL' bisim_progeq bot2 AR AL L1 L2
  -> (forall r (L L' : list F.block),
       simL' bisim_progeq r AR (a :: AL) L L' ->
       paco2 (@bisim_gen F.state _ F.state _) r (L, V, t) (L', V', t'))
  -> paco2 (@bisim_gen F.state _ F.state _) bot2 (F.blockI E Z s 0:: L1, V, t)
         (F.blockI E' Z' s' 0:: L2, V', t').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H4. rewrite cons_app.
  setoid_rewrite cons_app at 3.
  setoid_rewrite cons_app at 5.
  econstructor. hnf in H3. eapply simL_mon. eauto. inversion 1.
  econstructor; eauto. econstructor.
  econstructor; eauto.
  intros. pfold.
  econstructor; try eapply plus2O.
  econstructor; eauto using get; simpl.
  edestruct RelsOK; eauto.
  eapply omap_length in H. congruence. reflexivity.
  econstructor; eauto using get; simpl. edestruct RelsOK; eauto.
  eapply omap_length in H5. congruence. reflexivity.
  simpl.
  right. eapply CIH; eauto.
  intros. eapply H0; eauto.
  eapply simL_mon; eauto. intros; isabsurd.
Qed.
 *)


Lemma mutual_block_extension r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
      (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
      (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
      (SIML:simL' bisim_progeq r AR ALX L1 L2)
      (CIH: forall a
              (Z Z' : params)
              (Yv Y'v : list val) (s s' : stmt) (n : nat),
          get F1 n (Z, s) ->
          get F2 n (Z', s') ->
          get AL n a ->
          ArgRel E1 E2 a Yv Y'v ->
          r ((F.mkBlocks E1 F1 ++ L1)%list, E1 [Z <-- List.map Some Yv], s)
            ((F.mkBlocks E2 F2 ++ L2)%list, E2 [Z' <-- List.map Some Y'v], s'))
  :

    (forall (n : nat) (Z : params)
       (s : stmt) (Z' : params) (s' : stmt)
       (a : A),
        get F1 n (Z, s) ->
        get F2 n (Z', s') ->
        get AL n a ->
        fexteq' bisim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
        BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
        ParamRel a Z Z')
    -> mutual_block
        (simB bisim_progeq r AR (AL ++ ALX) (F.mkBlocks E1 F1 ++ L1)%list
              (F.mkBlocks E2 F2 ++ L2)%list) i AL'
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
  : simL' bisim_progeq r AR AL L L'
    -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                             fexteq' bisim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                             /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                             /\ ParamRel a Z Z')
    -> get F n (Z,s)
    -> get F' n (Z',s')
    -> get AL' n a
    -> ArgRel E E' a Yv Y'v
    -> bisim'r r
              ((F.mkBlocks E F ++ L)%list, E [Z <-- List.map Some Yv], s)
              ((F.mkBlocks E' F' ++ L')%list, E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto.
  hnf; intros.
  econstructor; eauto.
  - eapply simL_mon; eauto.
  - eapply mutual_block_extension; eauto.
    eapply simL_mon; eauto.
Qed.

Lemma simL_extension' r A AR (AL AL':list A) F F' E E' L L'
      (LEN1:length AL' = length F) (LEN2:length F = length F')
: simL' bisim_progeq r AR AL L L'
  -> (forall n Z s Z' s' a, get F n (Z,s) -> get F' n (Z',s') -> get AL' n a ->
                         fexteq' bisim_progeq AR a (AL' ++ AL) E Z s E' Z' s'
                         /\ BlockRel a (F.blockI E Z s n) (F.blockI E' Z' s' n)
                         /\ ParamRel a Z Z')
  -> simL' bisim_progeq r AR (AL' ++ AL) (F.mkBlocks E F ++ L) (F.mkBlocks E' F' ++ L').
Proof.
  intros.
  hnf; intros.
  econstructor; eauto.
  Lemma mutual_block_extension_simple r A AR F1 F2 F1' F2' ALX AL AL' i E1 E2 L1 L2
        (D1:F1' = drop i F1) (D2:F2' = drop i F2) (D3:AL' = drop i AL)
        (LEN1:length F1 = length F2) (LEN2:length AL = length F1)
        (SIML:simL' bisim_progeq r AR ALX L1 L2)
    :
       (forall (n : nat) (Z : params)
         (s : stmt) (Z' : params) (s' : stmt)
         (a : A),
       get F1 n (Z, s) ->
       get F2 n (Z', s') ->
       get AL n a ->
       fexteq' bisim_progeq AR a (AL ++ ALX) E1 Z s E2 Z' s' /\
       BlockRel a (F.blockI E1 Z s n) (F.blockI E2 Z' s' n) /\
       ParamRel a Z Z')
      -> mutual_block
          (simB bisim_progeq r AR (AL ++ ALX) (F.mkBlocks E1 F1 ++ L1)%list
                (F.mkBlocks E2 F2 ++ L2)%list) i AL'
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

Lemma bisim_drop_shift r l L E Y L' E' Y' blk blk' (STL:sawtooth L) (STL':sawtooth L')
  : get L (labN l) blk
  -> get L' (labN l) blk'
  -> paco2 (@bisim_gen F.state _ F.state _) r
          (drop (labN l - block_n blk) L, E, stmtApp (LabI (block_n blk)) Y)
          (drop (labN l - block_n blk') L', E', stmtApp (LabI (block_n blk')) Y')
  -> paco2 (@bisim_gen F.state _ F.state _) r (L, E, stmtApp l Y)
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
  - inv H3; inv H4; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. reflexivity.
      * stuck2. eapply H5. do 2 eexists.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        simpl.
        simpl_get_drop. eauto.
      * stuck2. eapply H6. do 2 eexists.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
        simpl_get_drop. eauto.
    + inv H8.
      simpl_get_drop; repeat get_functional.
      pfold. econstructor 3; [
             | eapply star2_refl
             |
             |
             |].
      Focus 2. rewrite <- H7. eapply S_star2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl in *. simpl_minus.
      eauto. eauto.
      stuck2. eapply H5. do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl_get_drop. eauto.
      eauto.
    + inv H8.
      simpl_get_drop; repeat get_functional.
      pfold. econstructor 3; [
             |
             |eapply star2_refl
             |
             |].
      Focus 2. rewrite <- H7. eapply S_star2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl in *. simpl_minus.
      eauto. eauto. eauto.
      stuck2. eapply H6. do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      simpl_get_drop. eauto.
    + inv H8; inv H11. pfold. simpl in *. subst yl yl0.
      simpl_get_drop; repeat get_functional.
      simpl in *. simpl_minus.
      econstructor 1; try eapply star2_plus2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
      left. pfold. econstructor 3; try eapply star2_refl; eauto.
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

Ltac one_step := eapply bisimSilent; [ eapply plus2O; single_step
                              | eapply plus2O; single_step
                              | ].

Ltac no_step := eapply bisimTerm;
               try eapply star2_refl; try get_functional; try subst;
                [ try reflexivity
                | stuck2
                | stuck2  ].


Ltac step_activated :=
  match goal with
    | [ H : omap (exp_eval ?E) ?Y = Some ?vl
        |- activated (_, ?E, stmtExtern ?x ?f ?Y ?s) ] =>
      eexists (ExternI f vl default_val); eexists; try (now (econstructor; eauto))
  end.

Ltac extern_step :=
  let STEP := fresh "STEP" in
  eapply bisimExtern;
    [ eapply star2_refl
    | eapply star2_refl
    | try step_activated
    | try step_activated
    | intros ? ? STEP; inv STEP
    | intros ? ? STEP; inv STEP
    ].


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
