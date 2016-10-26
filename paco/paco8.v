Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 8
*)

(** 1 Mutual Coinduction *)

Section Arg8_1.

Definition monotone8 T0 T1 T2 T3 T4 T5 T6 T7 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7) (LE: r <8= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf [].

Theorem paco8_acc: forall
  l r (OBG: forall rr (INC: r <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8 gf rr),
  l <8= paco8 gf r.
Proof.
  intros; assert (SIM: paco8 gf (r \8/ l) x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_mon: monotone8 (paco8 gf).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8= paco8 gf r.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Corollary paco8_mult: forall r,
  paco8 gf (paco8 gf r) <8= paco8 gf r.
Proof. intros; eapply paco8_mult_strong, paco8_mon; eauto. Qed.

Theorem paco8_fold: forall r,
  gf (upaco8 gf r) <8= paco8 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco8_unfold: forall (MON: monotone8 gf) r,
  paco8 gf r <8= gf (upaco8 gf r).
Proof. unfold monotone8; intros; destruct PR; eauto. Qed.

End Arg8_1.

Hint Unfold monotone8.
Hint Resolve paco8_fold.

Implicit Arguments paco8_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].

Instance paco8_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8 gf r x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_acc gf;
  pacomult   := paco8_mult gf;
  pacofold   := paco8_fold gf;
  pacounfold := paco8_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg8_2.

Definition monotone8_2 T0 T1 T2 T3 T4 T5 T6 T7 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) (LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco8_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8_2_0 gf_0 gf_1 rr r_1),
  l <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco8_2_0 gf_0 gf_1 (r_0 \8/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8_2_1 gf_0 gf_1 r_0 rr),
  l <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco8_2_1 gf_0 gf_1 r_0 (r_1 \8/ l) x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_2_0_mon: monotone8_2 (paco8_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_2_1_mon: monotone8_2 (paco8_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_2_0_mult_strong: forall r_0 r_1,
  paco8_2_0 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_2_1_mult_strong: forall r_0 r_1,
  paco8_2_1 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Corollary paco8_2_0_mult: forall r_0 r_1,
  paco8_2_0 gf_0 gf_1 (paco8_2_0 gf_0 gf_1 r_0 r_1) (paco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco8_2_0_mult_strong, paco8_2_0_mon; eauto. Qed.

Corollary paco8_2_1_mult: forall r_0 r_1,
  paco8_2_1 gf_0 gf_1 (paco8_2_0 gf_0 gf_1 r_0 r_1) (paco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco8_2_1_mult_strong, paco8_2_1_mon; eauto. Qed.

Theorem paco8_2_0_fold: forall r_0 r_1,
  gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco8_2_1_fold: forall r_0 r_1,
  gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco8_2_0_unfold: forall (MON: monotone8_2 gf_0) (MON: monotone8_2 gf_1) r_0 r_1,
  paco8_2_0 gf_0 gf_1 r_0 r_1 <8= gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone8_2; intros; destruct PR; eauto. Qed.

Theorem paco8_2_1_unfold: forall (MON: monotone8_2 gf_0) (MON: monotone8_2 gf_1) r_0 r_1,
  paco8_2_1 gf_0 gf_1 r_0 r_1 <8= gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone8_2; intros; destruct PR; eauto. Qed.

End Arg8_2.

Hint Unfold monotone8_2.
Hint Resolve paco8_2_0_fold.
Hint Resolve paco8_2_1_fold.

Implicit Arguments paco8_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].

Instance paco8_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_2_0_acc gf_0 gf_1;
  pacomult   := paco8_2_0_mult gf_0 gf_1;
  pacofold   := paco8_2_0_fold gf_0 gf_1;
  pacounfold := paco8_2_0_unfold gf_0 gf_1 }.

Instance paco8_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_2_1_acc gf_0 gf_1;
  pacomult   := paco8_2_1_mult gf_0 gf_1;
  pacofold   := paco8_2_1_fold gf_0 gf_1;
  pacounfold := paco8_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg8_3.

Definition monotone8_3 T0 T1 T2 T3 T4 T5 T6 T7 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) (LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1)(LE_2: r_2 <8= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco8_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco8_3_0 gf_0 gf_1 gf_2 (r_0 \8/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco8_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \8/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <8= rr) (CIH: l <_paco_8= rr), l <_paco_8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \8/ l) x0 x1 x2 x3 x4 x5 x6 x7) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8_3_0_mon: monotone8_3 (paco8_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_3_1_mon: monotone8_3 (paco8_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_3_2_mon: monotone8_3 (paco8_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_3_0_mult_strong: forall r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_3_1_mult_strong: forall r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8_3_2_mult_strong: forall r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Corollary paco8_3_0_mult: forall r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_0_mult_strong, paco8_3_0_mon; eauto. Qed.

Corollary paco8_3_1_mult: forall r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_1_mult_strong, paco8_3_1_mon; eauto. Qed.

Corollary paco8_3_2_mult: forall r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_2_mult_strong, paco8_3_2_mon; eauto. Qed.

Theorem paco8_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco8_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco8_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco8_3_0_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone8_3; intros; destruct PR; eauto. Qed.

Theorem paco8_3_1_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone8_3; intros; destruct PR; eauto. Qed.

Theorem paco8_3_2_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone8_3; intros; destruct PR; eauto. Qed.

End Arg8_3.

Hint Unfold monotone8_3.
Hint Resolve paco8_3_0_fold.
Hint Resolve paco8_3_1_fold.
Hint Resolve paco8_3_2_fold.

Implicit Arguments paco8_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].
Implicit Arguments paco8_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 ].

Instance paco8_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco8_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco8_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_2_unfold gf_0 gf_1 gf_2 }.

