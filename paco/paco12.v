Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 12
*)

(** 1 Mutual Coinduction *)

Section Arg12_1.

Definition monotone12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE: r <12= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

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
Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf [].

Theorem paco12_acc: forall
  l r (OBG: forall rr (INC: r <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12 gf rr),
  l <12= paco12 gf r.
Proof.
  intros; assert (SIM: paco12 gf (r \12/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_mon: monotone12 (paco12 gf).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_mult_strong: forall r,
  paco12 gf (paco12 gf r \12/ r) <12= paco12 gf r.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Corollary paco12_mult: forall r,
  paco12 gf (paco12 gf r) <12= paco12 gf r.
Proof. intros; eapply paco12_mult_strong, paco12_mon; eauto. Qed.

Theorem paco12_fold: forall r,
  gf (paco12 gf r \12/ r) <12= paco12 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco12_unfold: forall (MON: monotone12 gf) r,
  paco12 gf r <12= gf (paco12 gf r \12/ r).
Proof. unfold monotone12; intros; destruct PR; eauto. Qed.

End Arg12_1.

Hint Unfold monotone12.
Hint Resolve paco12_fold.

Implicit Arguments paco12_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].

Instance paco12_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_acc gf;
  pacomult   := paco12_mult gf;
  pacofold   := paco12_fold gf;
  pacounfold := paco12_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg12_2.

Definition monotone12_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

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
Variable gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco12_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12_2_0 gf_0 gf_1 rr r_1),
  l <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco12_2_0 gf_0 gf_1 (r_0 \12/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12_2_1 gf_0 gf_1 r_0 rr),
  l <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco12_2_1 gf_0 gf_1 r_0 (r_1 \12/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_2_0_mon: monotone12_2 (paco12_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_2_1_mon: monotone12_2 (paco12_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_2_0_mult_strong: forall r_0 r_1,
  paco12_2_0 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_2_1_mult_strong: forall r_0 r_1,
  paco12_2_1 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Corollary paco12_2_0_mult: forall r_0 r_1,
  paco12_2_0 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1) (paco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco12_2_0_mult_strong, paco12_2_0_mon; eauto. Qed.

Corollary paco12_2_1_mult: forall r_0 r_1,
  paco12_2_1 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1) (paco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco12_2_1_mult_strong, paco12_2_1_mon; eauto. Qed.

Theorem paco12_2_0_fold: forall r_0 r_1,
  gf_0 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco12_2_1_fold: forall r_0 r_1,
  gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco12_2_0_unfold: forall (MON: monotone12_2 gf_0) (MON: monotone12_2 gf_1) r_0 r_1,
  paco12_2_0 gf_0 gf_1 r_0 r_1 <12= gf_0 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1).
Proof. unfold monotone12_2; intros; destruct PR; eauto. Qed.

Theorem paco12_2_1_unfold: forall (MON: monotone12_2 gf_0) (MON: monotone12_2 gf_1) r_0 r_1,
  paco12_2_1 gf_0 gf_1 r_0 r_1 <12= gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1 \12/ r_0) (paco12_2_1 gf_0 gf_1 r_0 r_1 \12/ r_1).
Proof. unfold monotone12_2; intros; destruct PR; eauto. Qed.

End Arg12_2.

Hint Unfold monotone12_2.
Hint Resolve paco12_2_0_fold.
Hint Resolve paco12_2_1_fold.

Implicit Arguments paco12_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].

Instance paco12_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_2_0_acc gf_0 gf_1;
  pacomult   := paco12_2_0_mult gf_0 gf_1;
  pacofold   := paco12_2_0_fold gf_0 gf_1;
  pacounfold := paco12_2_0_unfold gf_0 gf_1 }.

Instance paco12_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_2_1_acc gf_0 gf_1;
  pacomult   := paco12_2_1_mult gf_0 gf_1;
  pacofold   := paco12_2_1_fold gf_0 gf_1;
  pacounfold := paco12_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg12_3.

Definition monotone12_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1)(LE_2: r_2 <12= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

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
Variable gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco12_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco12_3_0 gf_0 gf_1 gf_2 (r_0 \12/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco12_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \12/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <12= rr) (CIH: l <_paco_12= rr), l <_paco_12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \12/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) by eauto.
  clear PR; repeat (try left; do 13 paco_revert; paco_cofix_auto).
Qed.

Theorem paco12_3_0_mon: monotone12_3 (paco12_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_3_1_mon: monotone12_3 (paco12_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_3_2_mon: monotone12_3 (paco12_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_3_0_mult_strong: forall r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_3_1_mult_strong: forall r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Theorem paco12_3_2_mult_strong: forall r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 13 paco_revert; paco_cofix_auto). Qed.

Corollary paco12_3_0_mult: forall r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_0_mult_strong, paco12_3_0_mon; eauto. Qed.

Corollary paco12_3_1_mult: forall r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_1_mult_strong, paco12_3_1_mon; eauto. Qed.

Corollary paco12_3_2_mult: forall r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_2_mult_strong, paco12_3_2_mon; eauto. Qed.

Theorem paco12_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco12_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco12_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco12_3_0_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_0 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2).
Proof. unfold monotone12_3; intros; destruct PR; eauto. Qed.

Theorem paco12_3_1_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_1 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2).
Proof. unfold monotone12_3; intros; destruct PR; eauto. Qed.

Theorem paco12_3_2_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_0) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_1) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 \12/ r_2).
Proof. unfold monotone12_3; intros; destruct PR; eauto. Qed.

End Arg12_3.

Hint Unfold monotone12_3.
Hint Resolve paco12_3_0_fold.
Hint Resolve paco12_3_1_fold.
Hint Resolve paco12_3_2_fold.

Implicit Arguments paco12_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].
Implicit Arguments paco12_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 ].

Instance paco12_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco12_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco12_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_2_unfold gf_0 gf_1 gf_2 }.

