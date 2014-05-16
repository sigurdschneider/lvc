Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export Events StateType paco.

Set Implicit Arguments.
Unset Printing Records.

Open Scope map_scope.
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

(** Simulation is an equivalence relation *)
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
  hnf; intros. inv IN.
  - econstructor 1; eauto.
  - econstructor 2; eauto; intros.
    edestruct H3; eauto; dcr. eexists; eauto.
    edestruct H4; eauto; dcr. eexists; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
Qed.

Arguments sim_gen_mon [S] {H} [S'] {H0} [x0] [x1] r r' IN LE.


Hint Resolve sim_gen_mon : paco.

Lemma sim_sim' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> sim' σ1 σ2.
Proof.
  revert σ1 σ2. pcofix CIH.
  intros. pfold.
  inv H2.
  - econstructor; eauto.
  - econstructor 2; eauto; intros.
    + edestruct H4; eauto; dcr. eexists; eauto.
    + edestruct H5; eauto; dcr. eexists; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
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
    + edestruct H4; eauto; dcr. destruct H9. eexists; eauto. exfalso; intuition.
    + edestruct H5; eauto; dcr. destruct H9. eexists; eauto. exfalso; intuition.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
Qed.

(** Transitivity is not obvious *)
(*
Inductive terminatesWith {S} `{StateType S} : S -> option val -> Prop :=
| trmWith σ r
  : r = result σ -> normal step σ  -> terminatesWith σ r
| trmWithStep σ σ' v
  : step σ σ' -> terminatesWith σ' v -> terminatesWith σ v.

Lemma terminatesWith_star_normal {S} `{StateType S} s v
  : terminatesWith s v -> exists s', star step s s' /\ normal step s' /\ result s' = v.
Proof.
  intros. general induction H0.
  eexists σ; eauto using star.
  destruct IHterminatesWith; dcr. eexists x; split; eauto using star.
Qed.

Lemma star_normal_terminatesWith {S} `{StateType S} s s' v
  : star step s s'
    -> normal step s'
    -> result s' = v
    -> terminatesWith s v.
Proof.
  intros. general induction H0.
  econstructor; eauto.
  eapply trmWithStep; eauto.
Qed.

Lemma terminatesWith_star {S} `{StateType S} s s' v
  : star step s' s -> terminatesWith s v -> terminatesWith s' v.
Proof.
  intros. general induction H0; eauto.
  eapply trmWithStep; eauto.
Qed.

Lemma terminatesWith_star_2 {S} `{StateType S} s s' v
  : star step s' s -> terminatesWith s' v -> terminatesWith s v.
Proof.
  intros. general induction H0; eauto.
  inv H2. exfalso. eapply H4; firstorder.
  pose proof (step_functional _ _ _ H H3); subst.
  eapply IHstar; eauto.
Qed.

Lemma terminatesWith_functional {S} `{StateType S} s v v'
  : terminatesWith s v -> terminatesWith s v' -> v = v'.
Proof.
  intros. general induction H0.
  inv H2. eauto.
  exfalso. firstorder.
  inv H2.
  exfalso; firstorder.
  rewrite step_functional in H4; eauto.
Qed.

Lemma terminatesWith_terminates {S} `{StateType S} s
  : (exists v, terminatesWith s v) <-> terminates step s.
Proof.
  split; intros. destruct H0.
  general induction H0. constructor; intros. exfalso; firstorder.
  econstructor; intros. rewrite step_functional; eauto.
  general induction H0.
  destruct (step_dec x). destruct H2. edestruct H0; eauto.
  exists x1. eapply trmWithStep; eauto.
  eexists (result x). econstructor; eauto.
Qed.

(* Termination *)

Lemma divergence_or_termination X (R: X -> X -> Prop) s
  : diverges R s -> terminates R s -> False.
Proof.
  intros. general induction H0.
  inv H1. eauto.
Qed.

Lemma not_terminates_is_divergence S `{StateType S} s
  : ~terminates step s -> diverges step s.
Proof.
  revert s. cofix; intros.
  destruct (step_dec s).
  + inv H1. econstructor. eauto.
    eapply not_terminates_is_divergence. intro. eapply H0.
    econstructor; intros; eauto. rewrite step_functional; eauto.
  + exfalso. eapply H0. econstructor; intros. exfalso. firstorder.
Qed.

Definition cobehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') :=
  (diverges step σ1 <-> diverges step σ2)
  /\ (forall v, terminatesWith σ1 v <-> terminatesWith σ2 v).

Lemma diverges_star {S} `{StateType S} (σ1 σ1':S)
  : diverges step σ1 -> star step σ1 σ1' -> diverges step σ1'.
Proof.
  intros. general induction H1; simpl; eauto using star.
  inv H2. pose proof (step_functional _ _ _ H H3); subst; eauto using diverges.
Qed.

Lemma star_diverges {S} `{StateType S} (σ1 σ1':S)
  : diverges step σ1' -> star step σ1 σ1' -> diverges step σ1.
Proof.
  intros. general induction H1; simpl; eauto using star, diverges.
Qed.

Lemma cobehave_reduction_closed {S} `{StateType S} {S'} `{StateType S'}
      (σ1 σ1':S) (σ2 σ2':S')
  : cobehave σ1 σ2
    -> star step σ1 σ1'
    -> star step σ2 σ2'
    -> cobehave σ1' σ2'.
Proof.
  intros.
  destruct H1. split; split; intros.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply diverges_star; eauto. eapply H1. eapply star_diverges; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
  eapply terminatesWith_star_2; eauto. eapply H4. eapply terminatesWith_star; eauto.
Qed.

Definition obseq (s s':stmt) :=
  forall (L:F.labenv) E, cobehave (L, E, s) (L, E, s').

Lemma sim_codiverge' {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> diverges step σ1 -> diverges (plus step) σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  intros.
  inv H1. eapply DivergesI; eauto. eapply sim_codiverge'; eauto.
  eapply div_ext_plus; eauto. eapply step_functional.
  exfalso. eapply normal_terminates in H6.
  eapply div_ext_star_2 in H2; eauto.
  eapply divergence_or_termination; eassumption. eapply step_functional.
Qed.

Lemma sim_codiverge {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> diverges step σ1 -> diverges step σ2.
Proof.
  intros. eapply div_plus. eapply (sim_codiverge' H1 H2).
Qed.

Lemma codiverge_sim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: diverges step σ1 -> diverges step σ2 -> sim σ1 σ2.
Proof.
  revert σ1 σ2. cofix; intros.
  inv H1; inv H2.
  eapply simS; eauto using plus.
Qed.

Lemma sim_step_closed {S} `{StateType S} {S'} `{StateType S'} (σ1 σ1':S) (σ2:S')
 : sim σ1 σ2 -> step σ1 σ1' -> sim σ1' σ2.
Proof.
  revert σ1 σ1' σ2. cofix; intros.
  inv H1. destruct H3. inv H5.
  eapply simS. rewrite step_functional; eauto.
  eapply plus_trans; eauto. eassumption.
  eapply simE. eauto. rewrite step_functional; eauto.
  eapply star_trans; eauto using plus_star.
  eauto. eauto.
  eapply simS. rewrite step_functional; eauto. eassumption. eauto.
  eapply simE. eauto. destruct H4. exfalso; firstorder.
  rewrite step_functional; eauto. eauto. eauto. eauto.
Qed.

Lemma sim_coterminatesWith {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 -> forall v, terminatesWith σ1 v -> terminatesWith σ2 v.
Proof.
  intros. general induction H2.
  + inv H3. exfalso. eapply H1. destruct H0; firstorder.
    destruct H4. eapply terminatesWith_star; eauto. econstructor; eauto.
    exfalso. firstorder.
  + eapply IHterminatesWith.
    pose proof (sim_step_closed _ H3 H0). eauto.
Qed.

Lemma coterminatesWith_sim {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S') v
: terminatesWith σ1 v -> terminatesWith σ2 v -> sim σ1 σ2.
Proof.
  intros.
  eapply terminatesWith_star_normal in H1.
  eapply terminatesWith_star_normal in H2.
  destruct H1, H2; dcr.
  eapply simE; eauto using star. congruence.
Qed.

Lemma sim_cobehave {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
: sim σ1 σ2 <-> cobehave σ1 σ2.
Proof.
  split. unfold cobehave; split; split; intros.
  + pose proof (sim_codiverge H1 H2); eauto.
  + pose proof (sim_codiverge (sim_sym H1) H2); eauto.
  + eapply (sim_coterminatesWith H1); eassumption.
  + eapply (sim_coterminatesWith (sim_sym H1) H2); eassumption.
  + revert_all. cofix; intros.
    destruct (step_dec σ1) as [[]|]; destruct (step_dec σ2) as [[]|].
    - eapply simS; try eapply plusO; try eassumption.
      eapply sim_cobehave. eapply cobehave_reduction_closed; eauto using star.
    - pose proof (normal_terminates H3). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ1 x0). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x0). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
    - pose proof (normal_terminates H2). eapply terminatesWith_terminates in H4; destruct H4.
      assert (terminatesWith σ2 x). eapply H1; eauto.
      eapply coterminatesWith_sim; eauto.
Qed.

Lemma cobehave_trans {S} `{StateType S} {S'} `{StateType S'} {S''} `{StateType S''}
(σ1:S) (σ2:S') (σ3:S'')
: cobehave σ1 σ2 -> cobehave σ2 σ3 -> cobehave σ1 σ3.
Proof.
  unfold cobehave; intros. destruct H2, H3; firstorder.
Qed.

Lemma sim_trans {S1} `{StateType S1} {S2} `{StateType S2} {S3} `{StateType S3}
      (σ1:S1) (σ2:S2) (σ3:S3)
  : sim σ1 σ2 -> sim σ2 σ3 -> sim σ1 σ3.
Proof.
  intros.
  rewrite sim_cobehave in H2.
  rewrite sim_cobehave in H3.
  rewrite sim_cobehave.
  pose proof (cobehave_trans H2 H3); eauto.
Qed.

*)



Lemma sim'_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim' σ1 σ2 -> sim' σ2 σ3 -> sim' σ1 σ3.
Proof.
  revert σ1 σ2 σ3. pcofix CIH; intros.
  pdestruct H3. pdestruct H4.
Admitted.

Lemma bisim'_expansion_closed {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2 σ2':S') r
  : sim'r r σ1' σ2'
    -> star2 step σ1 nil σ1'
    -> star2 step σ2 nil σ2'
    -> sim'r r σ1 σ2.
Proof.
  intros. pinversion H1; subst; pfold.
  - econstructor; eauto.
    + eapply (star2_plus2_plus2 H2 H4).
    + eapply (star2_plus2_plus2 H3 H5).
  - econstructor 2.
    + eapply (star2_trans H2 H4).
    + eapply (star2_trans H3 H5).
    + intros. edestruct H6; eauto.
    + intros. edestruct H7; eauto.
  - econstructor 3; eauto using star2_trans.
    + eapply (star2_trans H2 H5).
  - econstructor 4; eauto using star2_trans.
    + eapply (star2_trans H2 H5).
    + eapply (star2_trans H3 H6).
Qed.

Class SimRelation (A:Type) := {
    ParamRel : A-> list var -> list var -> Prop;
    ArgRel : onv val -> onv val -> A-> list val -> list val -> Prop;
    BlockRel : A-> F.block -> F.block -> Prop;
    RelsOK : forall E E' a Z Z' VL VL', ParamRel a Z Z' -> ArgRel E E' a VL VL' -> length Z = length VL /\ length Z' = length VL'
}.

Inductive simB (r:rel2 F.state (fun _ : F.state => F.state)) {A} (AR:SimRelation A)  : F.labenv -> F.labenv -> A -> F.block -> F.block -> Prop :=
| simBI a L L' V V' Z Z' s s'
  : ParamRel a Z Z'
    -> BlockRel a (F.blockI V Z s) (F.blockI V' Z' s')
    -> (forall E E' Y Y' Yv Y'v,
         omap (exp_eval E) Y = Some Yv
         -> omap (exp_eval E') Y' = Some Y'v
         -> ArgRel V V' a Yv Y'v
         -> paco2 (@sim_gen F.state _ F.state _) r (L, E, stmtGoto (LabI 0) Y)
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
    -> paco2 (@sim_gen F.state _ F.state _) r (L, E[Z <-- List.map Some VL], s)
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
       sim'r r (L, V, t) (L', V', t'))
  -> sim' (F.blockI E Z s :: L1, V, t)
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
  -> sim'r r
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

Lemma sim_drop_shift r l L E Y L' E' Y'
: sim'r (S:=F.state) (S':=F.state) r (drop (labN l) L, E, stmtGoto (LabI 0) Y)
        (drop (labN l) L', E', stmtGoto (LabI 0) Y')
  -> sim'r (S:=F.state) (S':=F.state)  r (L, E, stmtGoto l Y)
          (L', E', stmtGoto l Y').
Proof.
  intros. pinversion H; subst.
  - eapply plus2_destr_nil in H0.
    eapply plus2_destr_nil in H1.
    destruct H0; destruct H1; dcr. inv H3.
    simpl in *. inv H1.
    pfold. econstructor; try eapply star2_plus2.
(*
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  -
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
