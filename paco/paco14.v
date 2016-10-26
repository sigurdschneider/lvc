Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 14
*)

(** 1 Mutual Coinduction *)

Section Arg14_1.

Definition monotone14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE: r <14= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf [].

Theorem paco14_acc: forall
  l r (OBG: forall rr (INC: r <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14 gf rr),
  l <14= paco14 gf r.
Proof.
  intros; assert (SIM: paco14 gf (r \14/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_mon: monotone14 (paco14 gf).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14= paco14 gf r.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Corollary paco14_mult: forall r,
  paco14 gf (paco14 gf r) <14= paco14 gf r.
Proof. intros; eapply paco14_mult_strong, paco14_mon; eauto. Qed.

Theorem paco14_fold: forall r,
  gf (upaco14 gf r) <14= paco14 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco14_unfold: forall (MON: monotone14 gf) r,
  paco14 gf r <14= gf (upaco14 gf r).
Proof. unfold monotone14; intros; destruct PR; eauto. Qed.

End Arg14_1.

Hint Unfold monotone14.
Hint Resolve paco14_fold.

Implicit Arguments paco14_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].

Instance paco14_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_acc gf;
  pacomult   := paco14_mult gf;
  pacofold   := paco14_fold gf;
  pacounfold := paco14_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg14_2.

Definition monotone14_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco14_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14_2_0 gf_0 gf_1 rr r_1),
  l <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco14_2_0 gf_0 gf_1 (r_0 \14/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14_2_1 gf_0 gf_1 r_0 rr),
  l <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco14_2_1 gf_0 gf_1 r_0 (r_1 \14/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_2_0_mon: monotone14_2 (paco14_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_2_1_mon: monotone14_2 (paco14_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_2_0_mult_strong: forall r_0 r_1,
  paco14_2_0 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_2_1_mult_strong: forall r_0 r_1,
  paco14_2_1 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Corollary paco14_2_0_mult: forall r_0 r_1,
  paco14_2_0 gf_0 gf_1 (paco14_2_0 gf_0 gf_1 r_0 r_1) (paco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco14_2_0_mult_strong, paco14_2_0_mon; eauto. Qed.

Corollary paco14_2_1_mult: forall r_0 r_1,
  paco14_2_1 gf_0 gf_1 (paco14_2_0 gf_0 gf_1 r_0 r_1) (paco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco14_2_1_mult_strong, paco14_2_1_mon; eauto. Qed.

Theorem paco14_2_0_fold: forall r_0 r_1,
  gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco14_2_1_fold: forall r_0 r_1,
  gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco14_2_0_unfold: forall (MON: monotone14_2 gf_0) (MON: monotone14_2 gf_1) r_0 r_1,
  paco14_2_0 gf_0 gf_1 r_0 r_1 <14= gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone14_2; intros; destruct PR; eauto. Qed.

Theorem paco14_2_1_unfold: forall (MON: monotone14_2 gf_0) (MON: monotone14_2 gf_1) r_0 r_1,
  paco14_2_1 gf_0 gf_1 r_0 r_1 <14= gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone14_2; intros; destruct PR; eauto. Qed.

End Arg14_2.

Hint Unfold monotone14_2.
Hint Resolve paco14_2_0_fold.
Hint Resolve paco14_2_1_fold.

Implicit Arguments paco14_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].

Instance paco14_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_2_0_acc gf_0 gf_1;
  pacomult   := paco14_2_0_mult gf_0 gf_1;
  pacofold   := paco14_2_0_fold gf_0 gf_1;
  pacounfold := paco14_2_0_unfold gf_0 gf_1 }.

Instance paco14_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_2_1_acc gf_0 gf_1;
  pacomult   := paco14_2_1_mult gf_0 gf_1;
  pacofold   := paco14_2_1_fold gf_0 gf_1;
  pacounfold := paco14_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg14_3.

Definition monotone14_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1)(LE_2: r_2 <14= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco14_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco14_3_0 gf_0 gf_1 gf_2 (r_0 \14/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco14_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \14/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <14= rr) (CIH: l <_paco_14= rr), l <_paco_14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \14/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) by eauto.
  clear PR; repeat (try left; do 15 paco_revert; paco_cofix_auto).
Qed.

Theorem paco14_3_0_mon: monotone14_3 (paco14_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_3_1_mon: monotone14_3 (paco14_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_3_2_mon: monotone14_3 (paco14_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_3_0_mult_strong: forall r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_3_1_mult_strong: forall r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Theorem paco14_3_2_mult_strong: forall r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 15 paco_revert; paco_cofix_auto). Qed.

Corollary paco14_3_0_mult: forall r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_0_mult_strong, paco14_3_0_mon; eauto. Qed.

Corollary paco14_3_1_mult: forall r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_1_mult_strong, paco14_3_1_mon; eauto. Qed.

Corollary paco14_3_2_mult: forall r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_2_mult_strong, paco14_3_2_mon; eauto. Qed.

Theorem paco14_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco14_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco14_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco14_3_0_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone14_3; intros; destruct PR; eauto. Qed.

Theorem paco14_3_1_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone14_3; intros; destruct PR; eauto. Qed.

Theorem paco14_3_2_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone14_3; intros; destruct PR; eauto. Qed.

End Arg14_3.

Hint Unfold monotone14_3.
Hint Resolve paco14_3_0_fold.
Hint Resolve paco14_3_1_fold.
Hint Resolve paco14_3_2_fold.

Implicit Arguments paco14_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].
Implicit Arguments paco14_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 ].

Instance paco14_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco14_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco14_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_2_unfold gf_0 gf_1 gf_2 }.

