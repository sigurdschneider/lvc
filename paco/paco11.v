Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 11
*)

(** 1 Mutual Coinduction *)

Section Arg11_1.

Definition monotone11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE: r <11= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

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
Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf [].

Theorem paco11_acc: forall
  l r (OBG: forall rr (INC: r <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11 gf rr),
  l <11= paco11 gf r.
Proof.
  intros; assert (SIM: paco11 gf (r \11/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_mon: monotone11 (paco11 gf).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_mult_strong: forall r,
  paco11 gf (paco11 gf r \11/ r) <11= paco11 gf r.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Corollary paco11_mult: forall r,
  paco11 gf (paco11 gf r) <11= paco11 gf r.
Proof. intros; eapply paco11_mult_strong, paco11_mon; eauto. Qed.

Theorem paco11_fold: forall r,
  gf (paco11 gf r \11/ r) <11= paco11 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco11_unfold: forall (MON: monotone11 gf) r,
  paco11 gf r <11= gf (paco11 gf r \11/ r).
Proof. unfold monotone11; intros; destruct PR; eauto. Qed.

End Arg11_1.

Hint Unfold monotone11.
Hint Resolve paco11_fold.

Implicit Arguments paco11_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].

Instance paco11_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_acc gf;
  pacomult   := paco11_mult gf;
  pacofold   := paco11_fold gf;
  pacounfold := paco11_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg11_2.

Definition monotone11_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

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
Variable gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco11_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11_2_0 gf_0 gf_1 rr r_1),
  l <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco11_2_0 gf_0 gf_1 (r_0 \11/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11_2_1 gf_0 gf_1 r_0 rr),
  l <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco11_2_1 gf_0 gf_1 r_0 (r_1 \11/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_2_0_mon: monotone11_2 (paco11_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_2_1_mon: monotone11_2 (paco11_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_2_0_mult_strong: forall r_0 r_1,
  paco11_2_0 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_2_1_mult_strong: forall r_0 r_1,
  paco11_2_1 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Corollary paco11_2_0_mult: forall r_0 r_1,
  paco11_2_0 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1) (paco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco11_2_0_mult_strong, paco11_2_0_mon; eauto. Qed.

Corollary paco11_2_1_mult: forall r_0 r_1,
  paco11_2_1 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1) (paco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco11_2_1_mult_strong, paco11_2_1_mon; eauto. Qed.

Theorem paco11_2_0_fold: forall r_0 r_1,
  gf_0 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco11_2_1_fold: forall r_0 r_1,
  gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco11_2_0_unfold: forall (MON: monotone11_2 gf_0) (MON: monotone11_2 gf_1) r_0 r_1,
  paco11_2_0 gf_0 gf_1 r_0 r_1 <11= gf_0 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1).
Proof. unfold monotone11_2; intros; destruct PR; eauto. Qed.

Theorem paco11_2_1_unfold: forall (MON: monotone11_2 gf_0) (MON: monotone11_2 gf_1) r_0 r_1,
  paco11_2_1 gf_0 gf_1 r_0 r_1 <11= gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1 \11/ r_0) (paco11_2_1 gf_0 gf_1 r_0 r_1 \11/ r_1).
Proof. unfold monotone11_2; intros; destruct PR; eauto. Qed.

End Arg11_2.

Hint Unfold monotone11_2.
Hint Resolve paco11_2_0_fold.
Hint Resolve paco11_2_1_fold.

Implicit Arguments paco11_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].

Instance paco11_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_2_0_acc gf_0 gf_1;
  pacomult   := paco11_2_0_mult gf_0 gf_1;
  pacofold   := paco11_2_0_fold gf_0 gf_1;
  pacounfold := paco11_2_0_unfold gf_0 gf_1 }.

Instance paco11_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_2_1_acc gf_0 gf_1;
  pacomult   := paco11_2_1_mult gf_0 gf_1;
  pacofold   := paco11_2_1_fold gf_0 gf_1;
  pacounfold := paco11_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg11_3.

Definition monotone11_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1)(LE_2: r_2 <11= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

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
Variable gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco11_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco11_3_0 gf_0 gf_1 gf_2 (r_0 \11/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco11_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \11/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <11= rr) (CIH: l <_paco_11= rr), l <_paco_11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \11/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) by eauto.
  clear PR; repeat (try left; do 12 paco_revert; paco_cofix_auto).
Qed.

Theorem paco11_3_0_mon: monotone11_3 (paco11_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_3_1_mon: monotone11_3 (paco11_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_3_2_mon: monotone11_3 (paco11_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_3_0_mult_strong: forall r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_3_1_mult_strong: forall r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Theorem paco11_3_2_mult_strong: forall r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 12 paco_revert; paco_cofix_auto). Qed.

Corollary paco11_3_0_mult: forall r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_0_mult_strong, paco11_3_0_mon; eauto. Qed.

Corollary paco11_3_1_mult: forall r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_1_mult_strong, paco11_3_1_mon; eauto. Qed.

Corollary paco11_3_2_mult: forall r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_2_mult_strong, paco11_3_2_mon; eauto. Qed.

Theorem paco11_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco11_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco11_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco11_3_0_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_0 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2).
Proof. unfold monotone11_3; intros; destruct PR; eauto. Qed.

Theorem paco11_3_1_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_1 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2).
Proof. unfold monotone11_3; intros; destruct PR; eauto. Qed.

Theorem paco11_3_2_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_0) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_1) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \11/ r_2).
Proof. unfold monotone11_3; intros; destruct PR; eauto. Qed.

End Arg11_3.

Hint Unfold monotone11_3.
Hint Resolve paco11_3_0_fold.
Hint Resolve paco11_3_1_fold.
Hint Resolve paco11_3_2_fold.

Implicit Arguments paco11_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].
Implicit Arguments paco11_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 ].

Instance paco11_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco11_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco11_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_2_unfold gf_0 gf_1 gf_2 }.

