Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 13
*)

(** 1 Mutual Coinduction *)

Section Arg13_1.

Definition monotone13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE: r <13= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

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
Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf [].

Theorem paco13_acc: forall
  l r (OBG: forall rr (INC: r <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13 gf rr),
  l <13= paco13 gf r.
Proof.
  intros; assert (SIM: paco13 gf (r \13/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_mon: monotone13 (paco13 gf).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_mult_strong: forall r,
  paco13 gf (paco13 gf r \13/ r) <13= paco13 gf r.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Corollary paco13_mult: forall r,
  paco13 gf (paco13 gf r) <13= paco13 gf r.
Proof. intros; eapply paco13_mult_strong, paco13_mon; eauto. Qed.

Theorem paco13_fold: forall r,
  gf (paco13 gf r \13/ r) <13= paco13 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco13_unfold: forall (MON: monotone13 gf) r,
  paco13 gf r <13= gf (paco13 gf r \13/ r).
Proof. unfold monotone13; intros; destruct PR; eauto. Qed.

End Arg13_1.

Hint Unfold monotone13.
Hint Resolve paco13_fold.

Implicit Arguments paco13_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].

Instance paco13_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_acc gf;
  pacomult   := paco13_mult gf;
  pacofold   := paco13_fold gf;
  pacounfold := paco13_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg13_2.

Definition monotone13_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

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
Variable gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco13_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13_2_0 gf_0 gf_1 rr r_1),
  l <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco13_2_0 gf_0 gf_1 (r_0 \13/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13_2_1 gf_0 gf_1 r_0 rr),
  l <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco13_2_1 gf_0 gf_1 r_0 (r_1 \13/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_2_0_mon: monotone13_2 (paco13_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_2_1_mon: monotone13_2 (paco13_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_2_0_mult_strong: forall r_0 r_1,
  paco13_2_0 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_2_1_mult_strong: forall r_0 r_1,
  paco13_2_1 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Corollary paco13_2_0_mult: forall r_0 r_1,
  paco13_2_0 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1) (paco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco13_2_0_mult_strong, paco13_2_0_mon; eauto. Qed.

Corollary paco13_2_1_mult: forall r_0 r_1,
  paco13_2_1 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1) (paco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco13_2_1_mult_strong, paco13_2_1_mon; eauto. Qed.

Theorem paco13_2_0_fold: forall r_0 r_1,
  gf_0 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco13_2_1_fold: forall r_0 r_1,
  gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco13_2_0_unfold: forall (MON: monotone13_2 gf_0) (MON: monotone13_2 gf_1) r_0 r_1,
  paco13_2_0 gf_0 gf_1 r_0 r_1 <13= gf_0 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1).
Proof. unfold monotone13_2; intros; destruct PR; eauto. Qed.

Theorem paco13_2_1_unfold: forall (MON: monotone13_2 gf_0) (MON: monotone13_2 gf_1) r_0 r_1,
  paco13_2_1 gf_0 gf_1 r_0 r_1 <13= gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1 \13/ r_0) (paco13_2_1 gf_0 gf_1 r_0 r_1 \13/ r_1).
Proof. unfold monotone13_2; intros; destruct PR; eauto. Qed.

End Arg13_2.

Hint Unfold monotone13_2.
Hint Resolve paco13_2_0_fold.
Hint Resolve paco13_2_1_fold.

Implicit Arguments paco13_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].

Instance paco13_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_2_0_acc gf_0 gf_1;
  pacomult   := paco13_2_0_mult gf_0 gf_1;
  pacofold   := paco13_2_0_fold gf_0 gf_1;
  pacounfold := paco13_2_0_unfold gf_0 gf_1 }.

Instance paco13_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_2_1_acc gf_0 gf_1;
  pacomult   := paco13_2_1_mult gf_0 gf_1;
  pacofold   := paco13_2_1_fold gf_0 gf_1;
  pacounfold := paco13_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg13_3.

Definition monotone13_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1)(LE_2: r_2 <13= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

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
Variable gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco13_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco13_3_0 gf_0 gf_1 gf_2 (r_0 \13/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco13_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \13/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <13= rr) (CIH: l <_paco_13= rr), l <_paco_13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \13/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) by eauto.
  clear PR; repeat (try left; do 14 paco_revert; paco_cofix_auto).
Qed.

Theorem paco13_3_0_mon: monotone13_3 (paco13_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_3_1_mon: monotone13_3 (paco13_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_3_2_mon: monotone13_3 (paco13_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_3_0_mult_strong: forall r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_3_1_mult_strong: forall r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Theorem paco13_3_2_mult_strong: forall r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 14 paco_revert; paco_cofix_auto). Qed.

Corollary paco13_3_0_mult: forall r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_0_mult_strong, paco13_3_0_mon; eauto. Qed.

Corollary paco13_3_1_mult: forall r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_1_mult_strong, paco13_3_1_mon; eauto. Qed.

Corollary paco13_3_2_mult: forall r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_2_mult_strong, paco13_3_2_mon; eauto. Qed.

Theorem paco13_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco13_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco13_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco13_3_0_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_0 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2).
Proof. unfold monotone13_3; intros; destruct PR; eauto. Qed.

Theorem paco13_3_1_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_1 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2).
Proof. unfold monotone13_3; intros; destruct PR; eauto. Qed.

Theorem paco13_3_2_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_0) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_1) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \13/ r_2).
Proof. unfold monotone13_3; intros; destruct PR; eauto. Qed.

End Arg13_3.

Hint Unfold monotone13_3.
Hint Resolve paco13_3_0_fold.
Hint Resolve paco13_3_1_fold.
Hint Resolve paco13_3_2_fold.

Implicit Arguments paco13_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].
Implicit Arguments paco13_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 ].

Instance paco13_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco13_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco13_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_2_unfold gf_0 gf_1 gf_2 }.

