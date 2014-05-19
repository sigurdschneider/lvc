Require Import List.
Require Export Util Var Val Exp Env Map CSet AutoIndTac IL AllInRel.
Require Export EventsActivated StateType paco.

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
  hnf; intros. inv IN.
  - econstructor 1; eauto.
  - econstructor 2; eauto; intros.
    edestruct H5; eauto; dcr. eexists; eauto.
    edestruct H6; eauto; dcr. eexists; eauto.

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
    + edestruct H6; eauto; dcr. eexists; eauto.
    + edestruct H7; eauto; dcr. eexists; eauto.
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

Lemma sim'_expansion_closed {S} `{StateType S}
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
    + eauto.
    + eauto.
    + intros. edestruct H8; eauto.
    + intros. edestruct H9; eauto.
  - econstructor 3; eauto using star2_trans.
    + eapply (star2_trans H2 H5).
  - econstructor 4; eauto using star2_trans.
    + eapply (star2_trans H2 H5).
    + eapply (star2_trans H3 H6).
Qed.

Lemma sim'_reduction_closed_1 {S} `{StateType S}
      (σ1 σ1':S) {S'} `{StateType S'} (σ2:S')
  : sim' σ1 σ2
    -> star2 step σ1 nil σ1'
    -> sim' σ1' σ2.
Proof.
  intros. eapply star2_star2n in H2. destruct H2 as [n ?].
  revert σ1 σ1' σ2 H1 H2.
  pattern n.
  eapply size_induction with (f:=id); intros; unfold id in *; simpl in *.
  pinversion H2; subst.
  - inv H3; eauto.
    eapply plus2_plus2n in H4. destruct H4. eapply plus2n_star2n in H4.
    edestruct (star2n_reach H3 H4); eauto. eapply H.
    + eapply sim'_expansion_closed. eapply H6.
      eauto using star2n_star2. eauto using plus2_star2.
    + eapply H1; try eapply H9. omega.
      eapply sim'_expansion_closed. eapply H6. eapply star2_refl.
      eauto using plus2_star2.
  - eapply star2n_star2 in H3. eapply activated_star_reach in H3; eauto.
  - pfold. eapply star2n_star2 in H3. eapply star2_reach_normal in H3; eauto.
    eapply H.
  - pfold. eapply star2n_star2 in H3.
    eapply star2_reach_normal in H3; eauto. eapply H.
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

Lemma sim'_trans {S1} `{StateType S1}
      (σ1:S1) {S2} `{StateType S2} (σ2:S2) {S3} `{StateType S3} (σ3:S3)
  : sim' σ1 σ2 -> sim' σ2 σ3 -> sim' σ1 σ3.
Proof.
  revert σ1 σ2 σ3. pcofix CIH; intros.
  pdestruct H3. pdestruct H4.
Admitted.

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
    simpl in *. inv H1; simpl in *.
    pfold. econstructor; try eapply star2_plus2.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    eauto.
  - inv H0.
    + exfalso. destruct H2 as [? [? ?]]. inv H2.
    + inv H1.
      * exfalso. destruct H3 as [? [? ?]]. inv H3.
      * inv H7; inv H10; simpl in *.
        pfold. subst yl yl0.
        econstructor; try eapply star2_plus2.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eapply H9.
        econstructor; eauto using get_drop_lab0, drop_get_lab0. eapply H12.
        left. pfold. econstructor 2; try eapply star2_refl; eauto.
  - inv H1.
    + pfold. econstructor 3; try eapply star2_refl. reflexivity.
      stuck2. eapply H2. do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
    + inv H4.
      pfold. econstructor 3.
      Focus 2. rewrite <- H3. eapply S_star2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
      eauto. eauto. eauto.
  - inv H1; inv H2; simpl in *.
    + pfold. econstructor 3; try eapply star2_refl. reflexivity.
      * stuck2. eapply H3. do 2 eexists.
        econstructor; eauto using get_drop_lab0, drop_get_lab0.
    + inv H6.
      pfold. econstructor 4; [
             | eapply star2_refl
             |
             |
             |].
      Focus 2. rewrite <- H5. eapply S_star2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
      simpl; eauto.
      stuck2. eapply H3. do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
    + inv H6.
      pfold. econstructor 4; [
             |
             |eapply star2_refl
             |
             |].
      Focus 2. rewrite <- H5. eapply S_star2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eauto.
      simpl; eauto. eauto.
      stuck2. eapply H4. do 2 eexists.
      econstructor; eauto using get_drop_lab0, drop_get_lab0.
    + inv H6; inv H9. pfold. simpl in *. subst yl yl0.
      econstructor 1; try eapply star2_plus2.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eapply H8.
      econstructor; eauto using get_drop_lab0, drop_get_lab0. eapply H11.
      left. pfold. econstructor 4; try eapply star2_refl; eauto.
Qed.



Ltac single_step :=
  match goal with
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = true |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = false |- step (_, ?E', stmtIf ?x _ _) _ ] =>
      econstructor 3; eauto; rewrite <- H; eauto; cset_tac; intuition
    | [ H : val2bool _ = false |- _ ] => econstructor 3 ; try eassumption; try reflexivity
    | [ H : step (?L, _ , stmtGoto ?l _) _, H': get ?L (counted ?l) _ |- _] =>
      econstructor; try eapply H'; eauto
    | [ H': get ?L (counted ?l) _ |- step (?L, _ , stmtGoto ?l _) _] =>
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
      eexists (ExternI f vl 0); eexists; try (now (econstructor; eauto))
  end.

Ltac extern_step :=
  let STEP := fresh "STEP" in
  eapply simExtern;
    [ eapply star2_refl
    | eapply star2_refl
    | try step_activated
    | try step_activated
    | intros ? ? STEP; inv STEP
    | intros ? ? STEP; inv STEP
    ].


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
