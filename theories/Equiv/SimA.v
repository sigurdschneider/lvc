Require Import Util Option AllInRel Sawtooth Get.
Require Export SmallStepRelations StateType.

Set Implicit Arguments.
Unset Printing Records.

(** * Simulation *)
(** A characterization of simulation equivalence on states;
works only for internally deterministic semantics *)

Inductive simtype := Bisim | Sim.

CoInductive sim {S} `{StateType S} {S'} `{StateType S'}  : simtype -> S -> S' -> Prop :=
  | simSilent t (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> sim t σ1' σ2'
      -> sim t σ1 σ2
  | simExtern t (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ sim t σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ sim t σ1' σ2')
      -> sim t pσ1 pσ2
  | simErr (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim Sim σ1 σ2
  | simTerm t (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim t σ1 σ2.

Arguments sim [S] {H} [S'] {H0} _ _ _.

Lemma sim_refl {S} `{StateType S} t (σ:S)
      : sim t σ σ.
Proof.
  revert σ. cofix.
  intros. destruct (step_dec σ) as [[[] []]|].
  - eapply simExtern; intros; eauto using star2_refl; eexists; eauto.
  - eapply simSilent; eauto using plus2O.
  - eapply simTerm; eauto using star2_refl.
Qed.

Inductive sim_gen {S} `{StateType S} {S'} `{StateType S'}
          (r: simtype -> S -> S' -> Prop)  : simtype -> S -> S' -> Prop :=
  | sim'Silent t (σ1 σ1':S) (σ2 σ2':S') : (* result σ1 = result σ2 -> *)
      plus2 step σ1 nil σ1'
      -> plus2 step σ2 nil σ2'
      -> r t σ1' σ2'
      -> sim_gen r t σ1 σ2
  | sim'Extern t (pσ1 σ1:S) (pσ2 σ2:S') : (* result σ1 = result σ2 -> *)
      star2 step pσ1 nil σ1
      -> star2 step pσ2 nil σ2
      -> activated σ1
      -> activated σ2
      -> (forall evt σ1', step σ1 evt σ1' -> exists σ2', step σ2 evt σ2' /\ r t σ1' σ2')
      -> (forall evt σ2', step σ2 evt σ2' -> exists σ1', step σ1 evt σ1' /\ r t σ1' σ2')
      -> sim_gen r t pσ1 pσ2
  | sim'Err (σ1 σ1':S) (σ2:S')
    : result σ1' = None
      -> star2 step σ1 nil σ1'
      -> normal2 step σ1'
      -> sim_gen r Sim σ1 σ2
  | sim'Term t (σ1 σ1':S) (σ2 σ2':S')
    : result σ1' = result σ2'
      -> star2 step σ1 nil σ1'
      -> star2 step σ2 nil σ2'
      -> normal2 step σ1'
      -> normal2 step σ2'
      -> sim_gen r t σ1 σ2.

Arguments sim_gen [S] {H} [S'] {H0} r _ _ _.

Hint Constructors sim_gen.


Definition rel2 T0 T1 :=
  forall (x0: T0) (x1: T1 x0), Prop.
Implicit Arguments rel2 [].

Definition pacoid {A : Type} (a: A) : A := a.

Notation bot2 :=
  (pacoid(fun _ _ => False)).

Notation "p \2/ q" :=
  (fun x0 x1 => p x0 x1 \/ q x0 x1)
  (at level 50, no associativity).

Notation "p <_paco_2= q" :=
  (forall _paco_x0 _paco_x1 (PR: p _paco_x0 _paco_x1 : Prop), q _paco_x0 _paco_x1 : Prop)
  (at level 50, no associativity).

Notation "p <2= q" :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 50, no associativity).

Section Arg2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Implicit Arguments gf [].

CoInductive paco2( r: rel2 T0 T1) x0 x1 : Prop :=
| paco2_pfold pco
    (LE : pco <2= (paco2 r \2/ r))
    (SIM: gf pco x0 x1)
.
End Arg2_def.
Implicit Arguments paco2 [ T0 T1 ].

Section Arg2_1.

Definition monotone2 T0 T1 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r r' (IN: gf r x0 x1) (LE: r <2= r'), gf r' x0 x1.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <_paco_2= rr), l <_paco_2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  intros; assert (SIM: paco2 gf (r \2/ l) x0 x1) by eauto.
  clear PR. revert x0 x1 SIM. cofix; intros.
  destruct SIM.
  econstructor; [ | eapply SIM].
  intros. exploit LE; eauto.
  destruct H. left. eapply paco2_acc. eauto.
  destruct H. right; eauto.
  left. eapply paco2_acc.
  eapply OBG; eauto.
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof.
  hnf. cofix CIH; intros.
  destruct IN. econstructor; [ | eapply SIM].
  intros. edestruct LE0; eauto.
Qed.

Theorem paco2_mult_strong: forall r,
  paco2 gf (paco2 gf r \2/ r) <2= paco2 gf r.
Proof.
  cofix CIH; intros.
  destruct PR. econstructor; [ | eapply SIM].
  intros. edestruct LE; eauto.
Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof.
  intros; eapply paco2_mult_strong, paco2_mon; eauto.
Qed.

Theorem paco2_fold: forall r,
  gf (paco2 gf r \2/ r) <2= paco2 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (paco2 gf r \2/ r).
Proof. unfold monotone2; intros; destruct PR; eauto. Qed.

End Arg2_1.

Hint Unfold monotone2.
Hint Resolve paco2_fold.

Arguments paco2_acc [T0 T1] gf l r OBG x0 x1 PR .
Arguments paco2_mon [T0 T1] gf x0 x1 r r' IN LE.
Arguments paco2_mult_strong [T0 T1] gf r x0 x1 PR.
Arguments paco2_mult  [T0 T1] gf r x0 x1 PR.
Arguments paco2_fold           [ T0 T1 ] gf r x0 x1 PR.
Arguments paco2_unfold         [ T0 T1 ] gf MON r x0 x1 PR.


Definition rel3 T0 T1 T2 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1), Prop.
Arguments rel3 : clear implicits.

Notation bot3 := (fun _ _ _ => False).

Notation "p \3/ q" :=
  (fun x0 x1 x2 => p x0 x1 x2 \/ q x0 x1 x2)
  (at level 50, no associativity).

Notation "p <3= q" :=
  (forall x0 x1 x2 (P: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 50, no associativity).

Section Arg3_def.
Variable T0 : Type.
Variable T1 : forall (x0: T0), Type.
Variable T2 : forall (x0: T0) (x1:T1 x0), Type.
Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Implicit Arguments gf [].

CoInductive paco3 (r: rel3 T0 T1 T2) x0 x1 x2 : Prop :=
| paco3_pfold pco
    (LE : pco <3= (paco3 r \3/ r))
    (SIM: gf pco x0 x1 x2)
.
End Arg3_def.
Arguments paco3 [ T0 T1 T2] gf r x0 x1 x2.

Section Arg3_1.

Definition monotone3 T0 T1 T2 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r r' (IN: gf r x0 x1 x2) (LE: r <3= r'), gf r' x0 x1 x2.

Variable T0 : Type.
Variable T1 : forall (x0: T0), Type.
Variable T2 : forall (x0: T0) (x1:T1 x0), Type.
Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.

Theorem paco3_acc: forall
    l r
    (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= paco3 gf rr),
  l <3= paco3 gf r.
Proof.
  intros; assert (SIM: paco3 gf (r \3/ l) x0 x1 x2) by eauto.
  clear P. revert x0 x1 x2 SIM. cofix; intros.
  destruct SIM.
  econstructor; [ | eapply SIM].
  intros. edestruct LE as [? | [?|?]]; eauto.
  - left. eapply paco3_acc.
    eapply OBG; eauto.
Qed.

Theorem paco3_mon: monotone3 (paco3 gf).
Proof.
  hnf. cofix CIH; intros.
  destruct IN. econstructor; [ | eapply SIM].
  intros. edestruct LE0; eauto.
Qed.

Theorem paco3_mult_strong: forall r,
  paco3 gf (paco3 gf r \3/ r) <3= paco3 gf r.
Proof.
  cofix CIH; intros.
  destruct P. econstructor; [ | eapply SIM].
  intros. edestruct LE; eauto.
Qed.

Corollary paco3_mult: forall r,
  paco3 gf (paco3 gf r) <3= paco3 gf r.
Proof.
  intros; eapply paco3_mult_strong, paco3_mon; eauto.
Qed.

Theorem paco3_fold: forall r,
  gf (paco3 gf r \3/ r) <3= paco3 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco3_unfold: forall (MON: monotone3 gf) r,
  paco3 gf r <3= gf (paco3 gf r \3/ r).
Proof. unfold monotone3; intros. destruct P; eauto. Qed.

End Arg3_1.

Hint Unfold monotone3.
Hint Resolve paco3_fold.

Arguments paco3_acc [T0 T1 T2] gf l r OBG x0 x1 x2 P.
Arguments paco3_mon [T0 T1 T2] gf x0 x1 x2 r r' IN LE.
Arguments paco3_mult_strong [T0 T1 T2] gf r x0 x1 x2 P.
Arguments paco3_mult [T0 T1 T2] gf r x0 x1 x2 P.
Arguments paco3_fold [ T0 T1 T2] gf r x0 x1 x2 P.
Arguments paco3_unfold [ T0 T1 T2] gf MON r x0 x1 x2 P.




Definition sim' t {S} `{StateType S} {S'} `{StateType S'} (σ1:S) (σ2:S')
  := paco3 (@sim_gen S _ S' _) bot3 t σ1 σ2.
Hint Unfold sim'.

Definition sim'r {S} `{StateType S} {S'} `{StateType S'} r t (σ1:S) (σ2:S')
  := paco3 (@sim_gen S _ S' _) r t σ1 σ2.
Hint Unfold sim'r.

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

Lemma sim_sim' {S} `{StateType S} {S'} `{StateType S'} t (σ1:S) (σ2:S')
: sim t σ1 σ2 -> sim' t σ1 σ2.
Proof.
  revert σ1 σ2. intros. eapply paco3_acc; [ | eapply H1]; intros.
  intros. econstructor. eauto.
  inv H2; eauto using sim_gen.
  - econstructor 2; eauto; intros.
    + edestruct H6; eauto; dcr. eexists; eauto.
    + edestruct H7; eauto; dcr. eexists; eauto.
Qed.


Lemma sim'_sim {S} `{StateType S} {S'} `{StateType S'} t (σ1:S) (σ2:S')
: sim' t σ1 σ2 -> sim t σ1 σ2.
Proof.
  revert t σ1 σ2. cofix CIH.
  intros.
  assert (sim_gen (paco3 (@sim_gen S _ S' _) bot3 \3/ bot3) t σ1 σ2).
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

Lemma sim'_refl {S} `{StateType S} (σ:S) t
      : sim' t σ σ.
Proof.
  eapply sim_sim'. eapply sim_refl.
Qed.
