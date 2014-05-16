Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export Events StateType paco.

Set Implicit Arguments.
Unset Printing Records.

Open Scope map_scope.
(** * Simulation *)
(** A characterization of simulation equivalence on states; works only for deterministic semantics *)

Definition activated {S} `{StateType S} (σ:S) :=
  exists ext σ', step σ (EvtExtern ext) σ'.


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


Lemma star2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros.
  general induction H; eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + right. econstructor 2; eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      edestruct (IHstar2 _ eq_refl H6); eauto.
Qed.

Lemma star2_reach_normal X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> normal2 R σ2a
  -> star2 R σ2b nil σ2a.
Proof.
  intros.
  general induction H0; eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + exfalso. eapply H3. do 2 eexists. eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      eapply IHstar2; eauto.
Qed.

Lemma plus2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: plus2 R σ1 nil σ2a
  -> plus2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros. eapply plus2_destr_nil in H. eapply plus2_destr_nil in H0.
  destruct H, H0; dcr.
  assert (x0 = x). eapply H1; eauto. subst.
  edestruct (star2_reach H4 H3); eauto using star2_trans.
Qed.


Inductive star2n (X : Type) (R : X -> event -> X -> Prop) : nat -> X -> list event -> X -> Prop :=
    star2n_refl : forall x : X, star2n R 0 x nil x
  | S_star2n n : forall y x x' yl z,
                   R x y x'
                   -> star2n R n x' yl z
                   -> star2n R (S n) x (filter_tau y yl) z.

Inductive plus2n (X : Type) (R : X -> event -> X -> Prop)
: nat -> X -> list event -> X -> Prop :=
  plus2nO x y x' el
  : R x y x'
    -> el = (filter_tau y nil)
    -> plus2n R 0 x el x'
| plus2nS n x y x' yl z el
  : R x y x'
    -> el = (filter_tau y yl)
    -> plus2n R n x' yl z
    -> plus2n R (S n)  x el z.

Lemma plus2_plus2n X (R: X -> event -> X -> Prop) x A y
: plus2 R x A y
  -> exists n, plus2n R n x A y.
Proof.
  intros. general induction H.
  - eexists; eauto using plus2n.
  - destruct IHplus2; eexists; eauto using plus2n.
Qed.

Lemma star2n_star2 X (R: X -> event -> X -> Prop) x A y n
: star2n R n x A y
  -> star2 R x A y.
Proof.
  intros. general induction H; eauto using star2.
Qed.

Lemma plus2n_star2n X (R: X -> event -> X -> Prop) x A y n
: plus2n R n x A y
  -> star2n R (S n) x A y.
Proof.
  intros. general induction H; eauto using star2n.
Qed.

Lemma star2_star2n X (R: X -> event -> X -> Prop) x A y
: star2 R x A y
  -> exists n, star2n R n x A y.
Proof.
  intros. general induction H; eauto using star2n.
  - destruct IHstar2; eexists; econstructor; eauto.
Qed.

Lemma star2n_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b n n'
: star2n R n σ1 nil σ2a
  -> star2n R n' σ1 nil σ2b
  -> internally_deterministic R
  -> (star2n R (n'-n) σ2a nil σ2b \/ star2n R (n-n') σ2b nil σ2a).
Proof.
  intros.
  general induction H; eauto.
  - left. orewrite (n' - 0 = n'). eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + right. orewrite (S n - 0 = S n). econstructor; eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      eapply IHstar2n; eauto.
Qed.


Lemma plus2_star2 X R (x y:X) A
: plus2 R x A y
  -> star2 R x A y.
Proof.
  intros. general induction H; simpl; eauto using star2.
Qed.

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

Lemma bisim'_reduction_closed {S} `{StateType S}
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

Lemma star2_normal X R (x y:X)
  : star2 R x nil y
    -> normal2 R x
    -> x = y.
Proof.
  intros. inv H; eauto.
  exfalso. firstorder.
Qed.

Lemma activated_normal S `{StateType S} (σ:S)
  : activated σ
    -> normal2 step σ
    -> False.
Proof.
  intros. inv H0. eapply H1. eexists. eapply H2.
Qed.


Arguments activated_normal [S] [H] σ _ _.

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
    eapply bisim'_reduction_closed; eauto using star2.
    eapply (S_star2 _ _ H); eauto using star2_refl.
Qed.




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
          eapply bisim'_reduction_closed in H7; eauto.
          destruct (bisim'_activated H12 H7); dcr.
          econstructor 2.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H3). eapply H11.
          eauto. eauto.
          + intros. edestruct H16; eauto. destruct H9.
            edestruct H14; eauto. dcr.
            eexists; split; eauto. destruct H20; isabsurd.
            right. eapply CIH. eapply bisim'_sym in H17. eauto.
            left. eapply star2_refl. eauto.
          + intros. edestruct H15; eauto; dcr.
            edestruct H5; eauto; dcr. destruct H9.
            eexists; split; eauto. destruct H18; isabsurd.
            right. eapply CIH. eapply bisim'_sym. eapply H19.
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
        edestruct (bisim'_terminate X H13 (bisim'_sym H7)); eauto; dcr.
        pfold.
        econstructor 3. rewrite H16 in H10. eapply H10.
        eapply plus2_star2 in H4.
        eapply (star2_trans H4 H8); eauto.
        eauto. eauto. eauto.
      - (* plus step <-> activated *)
          pfold.
          eapply plus2_star2 in H13.
          eapply star2_trans in H13; eauto. clear H2; simpl in *.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply bisim'_reduction_closed in H15; eauto.
          destruct (bisim'_activated H8 H15); dcr.
          econstructor 2. eauto.
          eapply plus2_star2 in H14.
          eapply (star2_trans H14 H11). eauto.
          eauto.
          + intros.
            edestruct H9 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H12 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto. left. eapply star2_refl.
          + intros.
            edestruct H18 as [? [? ?]]; eauto; isabsurd.
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
        edestruct (bisim'_terminate X H9 H14); eauto; dcr.
        pfold.
        econstructor 3. rewrite H16 in H4. eapply H4.
        eauto.
        eapply plus2_star2 in H13.
        eapply (star2_trans H13 H10); eauto.
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
          eapply bisim'_reduction_closed in H7; eauto.
          destruct (bisim'_activated H12 H7); dcr.
          econstructor 2.
          eapply plus2_star2 in H4.
          eapply (star2_trans H4 H8). eapply H11.
          eauto. eauto.
          + intros.
            edestruct H18 as [? [? ?]]; eauto; isabsurd.
            edestruct H14 as [? [? [?|?]]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH. eapply bisim'_sym in H19; eauto.
            left. eapply star2_refl. eauto.
          + intros.
            edestruct H15 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H9 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH. eapply bisim'_sym in H21; eauto.
            left; eapply star2_refl. eauto.
      - (* plus step <-> term *)
        eapply plus2_star2 in H6.
        eapply star2_trans in H6; eauto. clear H2; simpl in *.
        exploit (star2_reach_normal H11 H6); eauto. eapply H0.
        edestruct (bisim'_terminate X H13 (bisim'_sym H7)); eauto; dcr.
        pfold.
        econstructor 3. rewrite H16 in H10. eapply H10.
        eapply plus2_star2 in H4.
        eapply (star2_trans H4 H8); eauto.
        eauto. eauto. eauto.
      - (* plus step <-> activated *)
          pfold.
          eapply star2_trans in H6; eauto. clear H2; simpl in *.
          eapply plus2_star2 in H13.
          exploit (activated_star_reach H8 H6 H13); eauto.
          eapply bisim'_reduction_closed in H15; eauto.
          destruct (bisim'_activated H8 H15); dcr.
          econstructor 2. eauto.
          eapply plus2_star2 in H14.
          eapply (star2_trans H14 H11). eauto.
          eauto.
          + intros.
            edestruct H9 as [? [? [?|?]]]; eauto; isabsurd.
            edestruct H12 as [? [? ?]]; eauto; isabsurd.
            eexists; split; eauto.
            right. eapply CIH; eauto. left. eapply star2_refl.
          + intros.
            edestruct H18 as [? [? ?]]; eauto; isabsurd.
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
        edestruct (bisim'_terminate X H9 H14); eauto; dcr.
        pfold.
        econstructor 3. rewrite H16 in H4. eapply H4.
        eauto.
        eapply plus2_star2 in H13.
        eapply (star2_trans H13 H10); eauto.
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
         -> paco2 (@bisim_gen F.state _ F.state _) r (L, E, stmtGoto (LabI 0) Y)
                        (L', E', stmtGoto (LabI 0) Y'))
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


Lemma simL_mon (r r0:rel2 F.state (fun _ : F.state => F.state)) A AR L1 L2 (AL:list A) L1' L2'
:  AIR5 (simB r AR) L1 L2 AL L1' L2'
  -> (forall x0 x1 : F.state, r x0 x1 -> r0 x0 x1)
  -> L1 = L1'
  -> L2 = L2'
  ->  AIR5 (simB r0 AR) L1 L2 AL L1' L2'.
Proof.
  intros. general induction H; eauto using AIR5.
  econstructor; eauto.
  inv pf. econstructor; eauto.
  intros. eapply paco2_mon; eauto.
Qed.

Lemma subst_lemma A AR (a:A) AL s s' V V' E E' Z Z' L1 L2 t t'
: fexteq' AR a (a::AL) E Z s E' Z' s'
  -> ParamRel a Z Z'
  -> BlockRel a (F.blockI E Z s) (F.blockI E' Z' s')
  -> simL' bot2 AR AL L1 L2
  -> (forall r (L L' : list F.block),
       simL' r AR (a :: AL) L L' ->
       paco2 (@bisim_gen F.state _ F.state _) r (L, V, t) (L', V', t'))
  -> paco2 (@bisim_gen F.state _ F.state _) bot2 (F.blockI E Z s :: L1, V, t)
         (F.blockI E' Z' s' :: L2, V', t').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H4.
  econstructor. econstructor; eauto.
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
  edestruct RelsOK; eauto.
  edestruct RelsOK; eauto.
  eapply simL_mon; eauto. intros; isabsurd.
Qed.


Lemma fix_compatible r A AR (a:A) AL s s' E E' Z Z' L L' Yv Y'v
: simL' r AR AL L L'
  -> fexteq' AR a (a::AL) E Z s E' Z' s'
  -> ParamRel a Z Z'
  -> BlockRel a (F.blockI E Z s) (F.blockI E' Z' s')
  -> ArgRel E E' a Yv Y'v
  -> bisim'r r
            (F.blockI E Z s :: L, E [Z <-- List.map Some Yv], s)
            (F.blockI E' Z' s' :: L', E' [Z' <-- List.map Some Y'v], s').
Proof.
  revert_all; pcofix CIH; intros.
  eapply H1; eauto.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.
  pfold. econstructor; try eapply plus2O.
  - econstructor; eauto using get.
    + simpl. edestruct RelsOK; eauto.
      exploit omap_length; try eapply H; eauto.
      congruence.
  - reflexivity.
  - econstructor; eauto using get. simpl.
    edestruct RelsOK; eauto. exploit omap_length; try eapply H6; eauto.
    congruence.
  - reflexivity.
  - simpl. right. eapply CIH; eauto.
  - eapply simL_mon; eauto.
  - edestruct RelsOK; eauto.
  - edestruct RelsOK; eauto.
Qed.

Lemma simL_extension' r A AR (a:A) AL s s' E E' Z Z' L L'
: simL' r AR AL L L'
  -> fexteq' AR a (a::AL) E Z s E' Z' s'
  -> ParamRel a Z Z'
  -> BlockRel a (F.blockI E Z s) (F.blockI E' Z' s')
  -> simL' r AR (a::AL) (F.blockI E Z s :: L) (F.blockI E' Z' s' :: L').
Proof.
  intros.
  hnf; intros. econstructor; eauto. econstructor; eauto; intros.
  + pfold. econstructor; try eapply plus2O.
    econstructor; eauto using get. simpl.
    edestruct RelsOK; eauto. exploit omap_length; try eapply H3; eauto.
    congruence. reflexivity.
    econstructor; eauto using get. simpl.
    edestruct RelsOK; eauto. exploit omap_length; try eapply H4; eauto.
    congruence. reflexivity.
    simpl. left.
    eapply fix_compatible; eauto.
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

Lemma bisim_drop_shift r l L E Y L' E' Y'
: paco2 (@bisim_gen F.state _ F.state _) r (drop (labN l) L, E, stmtGoto (LabI 0) Y)
        (drop (labN l) L', E', stmtGoto (LabI 0) Y')
  -> paco2 (@bisim_gen F.state _ F.state _) r (L, E, stmtGoto l Y)
          (L', E', stmtGoto l Y').
Proof.
  intros. pinversion H; subst.
  - eapply plus2_destr_nil in H0.
    eapply plus2_destr_nil in H1.
    destruct H0; destruct H1; dcr. inv H3.
    simpl in *. inv H1; simpl in *.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  -  (*
  inv H1; inv H2; simpl in *.
  pfold. econstructor 2; try eapply star_refl; eauto. stuck.
  eapply H3. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  stuck. eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  pfold. inv H5. econstructor 2.
  Focus 2. eapply star_refl.
  Focus 2. econstructor 2.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  eauto. simpl; eauto. stuck.
  eapply H3. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  eauto.
  pfold. inv H5. econstructor 2.
  Focus 2. econstructor 2.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  eauto.
  Focus 2. eapply star_refl.
  simpl; eauto. eauto. stuck.
  eapply H4. econstructor.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  pfold. inv H5. inv H7. econstructor 2.
  Focus 2. econstructor 2.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  eauto.
  Focus 2. econstructor 2.
  econstructor; eauto using get_drop_lab0, drop_get_lab0.
  eauto. eauto. eauto. eauto.
  inv H1. pfold. econstructor 3; try eapply star_refl; eauto.
  stuck. destruct H2. econstructor. econstructor.
  eapply drop_get. simpl. orewrite (labN l + 0 = labN l).
  eauto. eauto. eauto. reflexivity.
  pfold. econstructor 3; eauto.
  inv H3; simpl in *.
  econstructor.
  econstructor. eapply get_drop in Ldef.
  orewrite (labN l + 0 = labN l) in Ldef. eauto. eauto. eauto. reflexivity.
  eauto.
  eapply psimapxd_mon. *)
Admitted.






(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
