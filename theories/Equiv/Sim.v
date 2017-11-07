Require Import Util Option AllInRel Get OptionR.
Require Export paco3 SmallStepRelations StateType.

Set Implicit Arguments.
Unset Printing Records.

(** * Parametric Definition of Simulation and Bisimulation *)
(** A characterization of simulation equivalence on states;
works only for internally deterministic semantics *)

Inductive simtype := Bisim | Sim.

Definition isBisim t :=
  match t with
  | Sim => false
  | Bisim => true
  end.

(** ** Generating Function *)

Inductive sim_gen
          {S} `{StateType S} {S'} `{StateType S'} (r: simtype -> S -> S' -> Prop)  : simtype -> S -> S' -> Prop :=
  | SimSilent t (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> r t σ1' σ2'
      -> sim_gen r t σ1 σ2
  | SimExtern t (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ r t σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ r t σ1' σ2')
      -> sim_gen r t pσ1 pσ2
  | SimErr (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim_gen r Sim σ1 σ2
  | SimTerm t (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim_gen r t σ1 σ2.

Arguments sim_gen [S] {H} [S'] {H0} r _ _ _.

Hint Constructors sim_gen.

Definition sim_bot {S} `{StateType S} {S'} `{StateType S'} t  (σ1:S) (σ2:S')
  := paco3 (@sim_gen S _ S' _) bot3 t σ1 σ2.
Hint Unfold sim_bot.

Definition sim {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  := paco3 (@sim_gen S _ S' _) r t σ1 σ2.
Hint Unfold sim.

Lemma sim_gen_mon {S} `{StateType S} {S'} `{StateType S'}
: monotone3 (@sim_gen S _ S' _).
Proof.
  hnf; intros. inv IN; eauto using @sim_gen.
  - econstructor 2; eauto; intros.
    edestruct H5; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.
Qed.

Arguments sim_gen_mon [S] {H} [S'] {H0} [x0] [x1] [x2] r r' IN LE.

Hint Resolve sim_gen_mon : paco.

Lemma sim_mon S `{StateType S} S' `{StateType S'}
      (r r':rel3 simtype (fun _ : simtype => S) (fun (_ : simtype) (_ : S) => S'))
  : (forall (x0 : simtype) (x1:S) (x2 : S'), r x0 x1 x2 -> r' x0 x1 x2)
    -> forall (t0 : simtype) (x:S) (y : S'), sim r t0 x y -> sim r' t0 x y.
Proof.
  intros. eapply paco3_mon; eauto.
Qed.

Hint Resolve sim_mon.

Lemma bisim_sim {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
      : sim bot3 Bisim σ σ' -> sim bot3 Sim σ σ'.
Proof.
  revert σ σ'. pcofix CIH.
  intros. pinversion H2; subst.
  - pfold. eapply SimSilent; eauto 20 using plus2O.
  - pfold. eapply SimExtern; intros; eauto using star2_refl.
    + edestruct H6; eauto; dcr; pclearbot; eauto 20.
    + edestruct H7; eauto; dcr; pclearbot; eauto 20.
  - pfold. eapply SimTerm; eauto using star2_refl.
Qed.

(** ** Reflexivity, Symmetry *)

Lemma sim_refl {S} `{StateType S} (σ:S) t r
      : sim r t σ σ.
Proof.
  revert σ.
  pcofix CIH.
  intros. destruct (step_dec σ) as [[[] []]|].
  - pfold. eapply SimExtern; intros; eauto using star2_refl; eexists; eauto.
  - pfold. eapply SimSilent; eauto using plus2O.
  - pfold. eapply SimTerm; eauto using star2_refl.
Qed.


Lemma bisim_sym {S} `{StateType S} {S'} `{StateType S'} (σ:S) (σ':S')
  : sim bot3 Bisim σ σ' -> sim bot3 Bisim σ' σ.
Proof.
  revert σ σ'. pcofix CIH.
  intros. pinversion H2; subst.
  - pfold. eapply SimSilent; eauto using plus2O.
  - pfold. eapply SimExtern; intros; eauto using star2_refl.
    + edestruct H7; eauto; dcr; pclearbot; eauto 20.
    + edestruct H6; eauto; dcr; pclearbot; eauto 20.
  - pfold. eapply SimTerm; eauto using star2_refl.
Qed.

(** ** Admissible Rules *)

Lemma sim_Y_left S `{StateType S} S' `{StateType S'} r t σA1 σB1 σ1' σ2
  : paco3 (@sim_gen S _ S _) r t σA1 σ2
    -> step σA1 EvtTau σ1'
    -> step σB1 EvtTau σ1'
    -> paco3 (@sim_gen S _ S _) r t σB1 σ2.
Proof.
  intros SIM Step1 Step2.
  pinversion SIM; subst; intros; relsimpl; pfold;
    eauto using sim_gen, star2_silent, star2_plus2.
Qed.

Lemma sim_Y_right  S `{StateType S} S' `{StateType S'} r t σ1 σA2 σB2 σ2'
  : paco3 (@sim_gen S _ S' _) r t σ1 σA2
    -> step σA2 EvtTau σ2'
    -> step σB2 EvtTau σ2'
    -> paco3 (@sim_gen S _ S' _) r t σ1 σB2.
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

(** ** Closedness under Expansion and Reduction *)

Lemma sim_expansion_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S') r t
  : sim r t σ1' σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sim r t σ1 σ2.
Proof.
  intros SIM ? ?.
  pinversion SIM; subst; pfold;
    eauto using sim_gen, star2_plus2_plus2_silent, star2_trans_silent.
Qed.

Lemma sim_reduction_closed_1 t {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S')
  : sim bot3 t σ1 σ2
    -> star2 step σ1 nil σ1'
    -> sim bot3 t σ1' σ2.
Proof.
  intros Sim Star. eapply star2_star2n in Star. destruct Star as [n StarN].
  revert σ1 σ1' σ2 Sim StarN.
  size induction n.
  pinversion Sim0; subst.
  - invc StarN; eauto; relsimpl.
    eapply star2_star2n in H2. destruct H2 as [n' H2].
    edestruct (star2n_reach H9 H2); eauto. eapply H.
    + eapply sim_expansion_closed; eauto using star2n_star2, plus2_star2.
    + eapply H1; try eapply H9. omega.
      eapply sim_expansion_closed;
      eauto using star2n_star2, plus2_star2.
  - eapply star2n_star2 in StarN; relsimpl; eauto.
  - pfold. eapply star2n_star2 in StarN; relsimpl; eauto.
  - pfold. eapply star2n_star2 in StarN; relsimpl; eauto.
Qed.

(** ** Transitivity *)

Lemma sim_reduction_closed_2 t {S} `{StateType S}
      (σ1:S) {S'} `{StateType S'} (σ2 σ2':S')
  : sim bot3 t σ1 σ2
    -> star2 step σ2 nil σ2'
    -> sim bot3 t σ1 σ2'.
Proof.
  intros. eapply star2_star2n in H2. destruct H2 as [n ?].
  revert σ1 σ2' σ2 H1 H2.
  pattern n.
  eapply size_induction with (f:=id); intros; unfold id in *; simpl in *.
  pinversion H2; subst.
  - inv H3; eauto.
    eapply plus2_star2n in H5. destruct H5.
    edestruct (star2n_reach H3 H5); eauto. eapply H0.
    + eapply sim_expansion_closed. eapply H6.
      eauto using plus2_star2. eauto using star2n_star2.
    + eapply H1; try eapply H9. omega.
      eapply sim_expansion_closed. eapply H6.
      eauto using plus2_star2. eapply star2_refl.
  - eapply star2n_star2 in H3. eapply activated_star_reach in H3; eauto.
  - pfold. eauto.
  - pfold. eapply star2n_star2 in H3.
    eapply star2_reach_normal in H3; eauto. eapply H0.
Qed.

Lemma sim_reduction_closed t {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S')
  : sim bot3 t σ1 σ2
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sim bot3 t σ1' σ2'.
Proof.
  intros.
  eapply sim_reduction_closed_1; [| eauto].
  eapply sim_reduction_closed_2; eauto.
Qed.


Lemma sim_terminate t {S1} `{StateType S1} (σ1 σ1':S1)
      {S2} `{StateType S2} (σ2:S2)
: star2 step σ1 nil σ1'
  -> normal2 step σ1'
  -> result σ1' <> None
  -> sim bot3 t σ1 σ2
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
    eapply sim_reduction_closed_1; eauto using star2, star2_silent.
Qed.


Lemma sim_terminate_2 t {S1} `{StateType S1} (σ2 σ2':S1)
      {S2} `{StateType S2} (σ1:S2)
: star2 step σ2 nil σ2'
  -> normal2 step σ2'
  -> sim bot3 t σ1 σ2
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
    eapply sim_reduction_closed_2; eauto using star2, star2_silent.
Qed.

Lemma sim_activated t {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> sim bot3 t σ1 σ2
  -> exists σ2', star2 step σ2 nil σ2' /\ activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\ sim bot3 t σ1'' σ2'')
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\ sim bot3 t σ1' σ2'').
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

Lemma sim_activated_2 t {S1} `{StateType S1} (σ1:S1)
      {S2} `{StateType S2} (σ2:S2)
: activated σ1
  -> sim bot3 t σ2 σ1
  -> exists σ2', star2 step σ2 nil σ2' /\
           (activated σ2' /\
           ( forall (evt : event) (σ1'' : S1),
               step σ1 evt σ1'' ->
               exists σ2'' : S2,
                 step σ2' evt σ2'' /\ (sim bot3 t σ2'' σ1''))
           /\
           ( forall (evt : event) (σ2'' : S2),
               step σ2' evt σ2'' ->
               exists σ1' : S1,
                 step σ1 evt σ1' /\ (sim bot3 t σ2'' σ1'))
           \/ (normal2 step σ2' /\ result σ2' = None /\ t = Sim)).
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

Lemma star2_plus2
: forall (X : Type) (R: X -> event -> X -> Prop) (x y z : X) e A,
    R x e y -> star2 R y A z -> plus2 R x (filter_tau e A) z.
Proof.
  intros. general induction H0; relsimpl'; eauto using plus2.
Qed.

Lemma plus2_star2_plus2
     : forall (X : Type) R (x y z : X) A B,
       plus2 R x A y -> star2 R y B z -> plus2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto using plus2.
  - rewrite filter_tau_app. eapply star2_plus2; eauto.
  - econstructor 2; eauto. rewrite filter_tau_app; eauto.
Qed.

Ltac zsimpl_step :=
  match goal with
  | [ SIM : sim bot3 ?t ?σ2 ?σ1, ACT : normal2 step ?σ2', STAR: star2 step ?σ2 nil ?σ2' |- _ ] =>
    eapply sim_reduction_closed_1 in SIM; [| eapply STAR]
  | [ SIM : paco3 (@sim_gen _ _ _ _) _ ?t ?σ2 ?σ1, ACT : normal2 step ?σ2', STAR: star2 step ?σ2 nil ?σ2' |- _ ] =>
    eapply sim_reduction_closed_1 in SIM; [| eapply STAR]
  | [ SIM : paco3 (@sim_gen _ _ _ _) _ ?t ?σ1 ?σ2,
            ACT : activated ?σ1', STAR: star2 step ?σ1 nil ?σ1' |- _ ] =>
    eapply sim_reduction_closed_1 in SIM; [| eapply STAR]
  | [ H : star2 ?R ?σ1 nil ?σ2, H':plus2 ?R ?σ2 nil ?σ3 |- _ ] =>
    eapply (star2_plus2_plus2 H) in H'; clear H; simpl in H'
  | [ H : plus2 ?R ?σ1 nil ?σ2, H':star2 ?R ?σ2 nil ?σ3 |- _ ] =>
    match goal with
    | [ H''' : plus2 R σ1 nil σ3 |- _ ] => fail 1
    | [ H''' : star2 R σ1 nil σ3 |- _ ] => fail 1
    | _ => eapply (plus2_star2_plus2 H) in H'; clear H; simpl in H'
    end
  | [ H : star2 ?R ?σ1 nil ?σ2, H':star2 ?R ?σ2 nil ?σ3 |- _ ] =>
    eapply (star2_trans H) in H'; clear H; simpl in H'
  | [ H : plus2 ?R ?σ nil ?σ', H' : star2 ?R ?σ _ ?σ'',
                                    H'' : activated ?σ'' |- _ ]
    => match goal with
      | [ H''' : star2 R σ' nil σ'' |- _ ] => fail 1
      | _ => pose proof (activated_star_reach H'' H' (plus2_star2 H))
      end
  | [ H : step ?σ1 _ ?σ2, A : forall (evt : event) (σ2'' : _),
          step ?σ1 evt σ2'' -> _ |- _ ] => specialize (A _ _ H); dcr
  | [ H : _ \/ bot3 _ _ _ |- _ ] => destruct H;[ | isabsurd]
  | [ SIM : paco3 (@sim_gen _ _ _ _) _ ?t ?σ1 ?σ2, ACT : activated ?σ2', STAR: star2 step ?σ2 nil ?σ2' |- _ ] =>
    eapply sim_reduction_closed_2 in SIM; [| eapply STAR]
  | [ H : plus2 step ?σ nil _, H' : star2 (@step ?S ?ST) ?σ _ ?σ',
                                    H'' : normal2 _ ?σ' |- _ ]
    => eapply plus2_star2 in H;
      eapply (star2_reach_normal H' H''
                                 (@step_internally_deterministic S ST)) in H
  | [ H : plus2 step ?σ1 nil ?σ2, H' : star2 step ?σ2 nil ?σ3
      |- sim_gen _ _ ?σ1 _ ]
    => pose proof (star2_trans (plus2_star2 H) H')
  | [ SIM : sim bot3 ?t ?σ1 ?σ2,
            ACT : normal2 step ?σ2', STAR: star2 step ?σ2 nil ?σ2' |- _ ] =>
    eapply sim_reduction_closed_2 in SIM; [| eapply STAR]
  end.

Ltac zzsimpl :=
  repeat zsimpl_step; relsimpl.

Ltac zzcases :=
  match goal with
    [ H : plus2 (@step ?S ?ST) ?σ1 nil ?σ2a, H' : plus2 (@step ?S ?ST) ?σ1 nil ?σ2b |- _ ]
    => edestruct (plus2_reach H H' (@step_internally_deterministic _ ST))
  | [ H: sim bot3 _ ?σ1 ?σ2, H' : activated ?σ2 |- _ ] =>
    match goal with
    | [ H : activated σ1 |- _ ] => fail 1
    | _ => destruct (sim_activated_2 H' H) as [? [? [[? [? ?]]| [? [? ?]]]]]
    end
  | [ H: sim bot3 _ ?σ1 ?σ2, H' : activated ?σ1 |- _ ] =>
    match goal with
    | [ H : activated σ2 |- _ ] => fail 1
    | _ => destruct (sim_activated H' H) as [? [? [? [? ?]]]]
    end
  | [ STAR : star2 step ?σ2 nil ?σ2', NORM: normal2 step ?σ2',
                                            SIM : paco3 (@sim_gen _ _ _ _) bot3 _ ?σ1 ?σ2 |- _ ]
    => edestruct (sim_terminate_2 STAR NORM SIM) as [? [? [? [|]]]]
  | [ STAR : star2 step ?σ1 nil ?σ1', NORM: normal2 step ?σ1',
                                            SIM : paco3 (@sim_gen _ _ _ _) bot3 _ ?σ1 ?σ2 |- _ ]
    => let H := fresh "H" in
      assert (result σ1' <> None) by congruence;
      destruct (sim_terminate STAR NORM H SIM) as [? [? [? ?]]];
      clear H
  | [ NORM: normal2 step ?σ1, SIM : sim bot3 _ ?σ1 ?σ2 |- _ ]
    => let H := fresh "H" in
      assert (result σ1 <> None) by congruence;
      destruct (sim_terminate (@star2_refl _ _ σ1) NORM H SIM) as [? [? [? ?]]];
      clear H
  end.

Lemma plus_not_normal X (R:X -> event -> X -> Prop) σ1 σ1'
  :  plus2 R σ1 nil σ1'
     -> normal2 R σ1
     -> False.
Proof.
  intros A B. eapply B.
  eapply plus2_destr_nil in A. dcr.
  eexists; eauto.
Qed.

Lemma sim_t_Sim_activated t S1 `{StateType S1}
      (σ1:S1)
  : result σ1 = ⎣⎦
    -> normal2 step σ1
    -> forall S2 `{StateType S2} (σ2:S2),
        sim bot3 t σ1 σ2
        -> activated σ2
        -> t = Sim.
Proof.
  intros. pinversion H3; subst; eauto; exfalso; relsimpl; eauto using plus_not_normal.
Qed.

Lemma sim_t_Sim_normal t S1 `{StateType S1}
      (σ1:S1) S2 `{StateType S2} (σ2:S2) r
  : result σ1 = ⎣⎦
    -> normal2 step σ1
    -> normal2 step σ2
    -> sim r t σ1 σ2
    -> t = Sim \/ result σ2 = None.
Proof.
  intros. pinversion H4; subst; eauto; relsimpl.
  - exfalso; eauto using plus_not_normal.
  - right. congruence.
Qed.

Lemma sim_t_Sim_normal_step t S1 `{StateType S1}
      (σ1:S1) S2 `{StateType S2} (σ2:S2) r
  : result σ1 = ⎣⎦
    -> normal2 step σ1
    -> sim r t σ1 σ2
    -> t = Sim \/ exists σ2', star2 step σ2 nil σ2' /\ normal2 step σ2' /\ result σ2' = None.
Proof.
  intros. pinversion H3; subst; eauto; relsimpl.
  - exfalso; eauto using plus_not_normal.
  - right. eexists; split; eauto. split; congruence.
Qed.

Local Hint Extern 5 =>
match goal with
| [ H : result ?σ1 = result ?σ2, H' : result ?σ2 = None |-
    result ?σ1 = None ] =>
  rewrite H; eapply H'
| [ H : result ?σ1 = result ?σ2, H' : result ?σ2 = result ?σ3 |-
    result ?σ1 = result ?σ3 ] =>
  rewrite H; eapply H'
end.

Local Hint Resolve plus2_star2.

Lemma sim_zigzag t {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2a σ2b:S2) {S3} `{StateType S3} (σ3:S3)
  : sim bot3 t σ1 σ2a
    -> (star2 step σ2a nil σ2b \/ star2 step σ2b nil σ2a)
    -> sim bot3 t σ2b σ3
    -> sim bot3 t σ1 σ3.
Proof.
  revert σ1 σ2a σ2b σ3. pcofix CIH; intros.
  destruct H4.
  - {
      pinversion H3; pinversion H5; subst.
      - (* plus <-> plus *)
        pfold. zzsimpl. zzcases; eauto 20.
      - (* plus step <-> activated *)
        pfold. zzsimpl.
        zzcases. zzsimpl.
        + econstructor 2; eauto using plus2_star2.
          * intros. unfold upaco3 in *; zzsimpl; eauto 10 using star2_refl.
          * intros. unfold upaco3 in *; zzsimpl; eauto 10 using star2_refl.
        + zzsimpl. assert (t = Sim).
          eapply (@sim_t_Sim_activated t _ _ _ H10 H9 _ _ _ H7); eauto.
          subst.
          econstructor 3; eauto using plus2_star2, star2_trans.
      - (* plus step <-> err *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 3; eauto; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H2); eauto.
      - (*  plus step <-> term *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 4; eauto; eauto.
        + zzsimpl.
          destruct (@sim_t_Sim_normal t _ _ _ _ _ _ _ H9 H8 H14 H7); eauto.
          * subst.
            pfold. econstructor 3; eauto using plus2_star2, star2_trans.
          * pfold. econstructor 4; eauto using plus2_star2, star2_trans.
            congruence.
      - (* activated <-> plus step *)
        pfold. zzsimpl.
        zzcases. zzsimpl.
        + unfold upaco3 in *.
          econstructor 2; eauto using plus2_star2.
          * intros. zzsimpl; eauto 10 using star2_refl.
          * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> activated *)
        pfold. zzsimpl.
        unfold upaco3 in *.
        econstructor 2; eauto using plus2_star2.
        * intros. zzsimpl; eauto 10 using star2_refl.
        * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> err *)
        zzsimpl.
      - (* activated <-> term *)
        zzsimpl.
      - (* term <-> plus step *)
        case_eq (result σ1'); intros.
        + pfold. zzsimpl. zzcases.
          zzsimpl.
          econstructor 4; eauto. eauto.
        + zzsimpl.
          rewrite H4 in H10.
          destruct (@sim_t_Sim_normal_step _ _ _ _ _ _ _ _ H10 H9 H15); eauto.
          * subst.
            pfold. econstructor 3; eauto. congruence.
          * destruct H2; dcr.
            zzsimpl.
            pfold. econstructor 4; eauto. congruence.
      - zzsimpl.
      - (* term <-> err *)
        zzsimpl.
        pfold. econstructor 3; eauto. congruence.
      - (* term <-> term *)
        zzsimpl.
        pfold. econstructor 4; eauto. congruence.
    }
  - {
      pinversion H3; pinversion H5; subst.
      - (* plus <-> plus *)
        pfold. zzsimpl.
        zzcases; unfold upaco3 in *; eauto.
      - (* plus step <-> activated *)
        pfold. zzsimpl.
        zzcases. zzsimpl.
        + unfold upaco3 in *.
          econstructor 2; eauto using plus2_star2.
          * intros. zzsimpl; eauto 10 using star2_refl.
          * intros. zzsimpl; eauto 10 using star2_refl.
        + zzsimpl. assert (t = Sim).
          eapply (@sim_t_Sim_activated t _ _ _ H10 H9 _ _ _ H7); eauto.
          subst.
          econstructor 3; eauto using plus2_star2, star2_trans.
      - (* plus step <-> err *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 3; eauto; eauto.
        + eapply plus2_star2 in H4.
          exploit (star2_trans H4 H2); eauto.
      - (*  plus step <-> term *)
        zzsimpl. zzcases.
        + pfold. zzsimpl.
          econstructor 4; eauto; eauto.
        + zzsimpl.
          destruct (@sim_t_Sim_normal t _ _ _ _ _ _ _ H9 H8 H14 H7); eauto.
          * subst.
            pfold. econstructor 3; eauto using plus2_star2, star2_trans.
          * pfold. econstructor 4; eauto using plus2_star2, star2_trans.
            congruence.
      - (* activated <-> plus step *)
        pfold. zzsimpl.
        zzcases. zzsimpl.
        + unfold upaco3 in *.
          econstructor 2; eauto using plus2_star2.
          * intros. zzsimpl; eauto 10 using star2_refl.
          * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> activated *)
        pfold. zzsimpl.
        unfold upaco3 in *.
        econstructor 2; eauto using plus2_star2.
        * intros. zzsimpl; eauto 10 using star2_refl.
        * intros. zzsimpl; eauto 10 using star2_refl.
      - (* activated <-> err *)
        zzsimpl.
      - (* activated <-> term *)
        zzsimpl.
      - (* term <-> plus step *)
        case_eq (result σ1'); intros.
        + pfold. zzsimpl.
          zzcases. zzsimpl.
          econstructor 4; eauto; eauto.
        + zzsimpl.
          rewrite H4 in H10.
          destruct (@sim_t_Sim_normal_step _ _ _ _ _ _ _ _ H10 H9 H15); eauto.
          * subst.
            pfold. econstructor 3; eauto. congruence.
          * destruct H2; dcr.
            zzsimpl.
            pfold. econstructor 4; eauto. congruence.
      - zzsimpl.
      - (* term <-> err *)
        zzsimpl.
        pfold. econstructor 3; eauto. congruence.
      - (* term <-> term *)
        zzsimpl.
        pfold. econstructor 4; eauto. congruence.
    }
Qed.

Lemma sim_trans t {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim bot3 t σ1 σ2 -> sim bot3 t σ2 σ3 -> sim bot3 t σ1 σ3.
Proof.
  intros. eauto using (sim_zigzag (S1:=S1) (S2:=S2) (S3:=S3)), star2_refl.
Qed.

Lemma sim_normal_inv S `{StateType S} (σ:S) S' `{StateType S'} (σ':S') r t
  : sim r t σ σ'
    -> normal2 StateType.step σ'
    -> exists σ'', star2 StateType.step σ nil σ'' /\ normal2 StateType.step σ''
             /\ fstNoneOrR eq (result σ'') (result σ') .
Proof.
  intros. pdestruct H1; subst; relsimpl; eauto.
  - exfalso. eapply H2. hnf. inv H3; eauto.
  - eexists; split; eauto. split; eauto. rewrite H1; eauto. econstructor.
  - eexists; split; eauto. split; eauto. rewrite H1; eauto. reflexivity.
Qed.

Lemma sim_stuck_exchange S `{StateType S} (σ:S) S' `{StateType S'} (σ':S')
      S'' `{StateType S''} (σ'':S'') r t r'
  : sim r t σ σ'
    -> normal2 StateType.step σ'
    -> result σ' = None
    -> normal2 StateType.step σ''
    -> result σ'' = None
    -> sim r' t σ σ''.
Proof.
  intros. eapply sim_normal_inv in H2; eauto; dcr.
  pfold. econstructor 4; try eassumption; eauto using star2_refl.
  rewrite H4 in *. inv H10. congruence.
Qed.
