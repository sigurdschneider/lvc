Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 9
*)

(** 1 Mutual Coinduction *)

Section Arg9_1.

Definition monotone9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE: r <9= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf [].

Theorem paco9_acc: forall
  l r (OBG: forall rr (INC: r <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9 gf rr),
  l <9= paco9 gf r.
Proof.
  intros; assert (SIM: paco9 gf (r \9/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_mon: monotone9 (paco9 gf).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9= paco9 gf r.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Corollary paco9_mult: forall r,
  paco9 gf (paco9 gf r) <9= paco9 gf r.
Proof. intros; eapply paco9_mult_strong, paco9_mon; eauto. Qed.

Theorem paco9_fold: forall r,
  gf (upaco9 gf r) <9= paco9 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco9_unfold: forall (MON: monotone9 gf) r,
  paco9 gf r <9= gf (upaco9 gf r).
Proof. unfold monotone9; intros; destruct PR; eauto. Qed.

End Arg9_1.

Hint Unfold monotone9.
Hint Resolve paco9_fold.

Implicit Arguments paco9_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].

Instance paco9_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_acc gf;
  pacomult   := paco9_mult gf;
  pacofold   := paco9_fold gf;
  pacounfold := paco9_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg9_2.

Definition monotone9_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco9_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9_2_0 gf_0 gf_1 rr r_1),
  l <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco9_2_0 gf_0 gf_1 (r_0 \9/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9_2_1 gf_0 gf_1 r_0 rr),
  l <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco9_2_1 gf_0 gf_1 r_0 (r_1 \9/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_2_0_mon: monotone9_2 (paco9_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_2_1_mon: monotone9_2 (paco9_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_2_0_mult_strong: forall r_0 r_1,
  paco9_2_0 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_2_1_mult_strong: forall r_0 r_1,
  paco9_2_1 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Corollary paco9_2_0_mult: forall r_0 r_1,
  paco9_2_0 gf_0 gf_1 (paco9_2_0 gf_0 gf_1 r_0 r_1) (paco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco9_2_0_mult_strong, paco9_2_0_mon; eauto. Qed.

Corollary paco9_2_1_mult: forall r_0 r_1,
  paco9_2_1 gf_0 gf_1 (paco9_2_0 gf_0 gf_1 r_0 r_1) (paco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco9_2_1_mult_strong, paco9_2_1_mon; eauto. Qed.

Theorem paco9_2_0_fold: forall r_0 r_1,
  gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco9_2_1_fold: forall r_0 r_1,
  gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco9_2_0_unfold: forall (MON: monotone9_2 gf_0) (MON: monotone9_2 gf_1) r_0 r_1,
  paco9_2_0 gf_0 gf_1 r_0 r_1 <9= gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone9_2; intros; destruct PR; eauto. Qed.

Theorem paco9_2_1_unfold: forall (MON: monotone9_2 gf_0) (MON: monotone9_2 gf_1) r_0 r_1,
  paco9_2_1 gf_0 gf_1 r_0 r_1 <9= gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone9_2; intros; destruct PR; eauto. Qed.

End Arg9_2.

Hint Unfold monotone9_2.
Hint Resolve paco9_2_0_fold.
Hint Resolve paco9_2_1_fold.

Implicit Arguments paco9_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].

Instance paco9_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_2_0_acc gf_0 gf_1;
  pacomult   := paco9_2_0_mult gf_0 gf_1;
  pacofold   := paco9_2_0_fold gf_0 gf_1;
  pacounfold := paco9_2_0_unfold gf_0 gf_1 }.

Instance paco9_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_2_1_acc gf_0 gf_1;
  pacomult   := paco9_2_1_mult gf_0 gf_1;
  pacofold   := paco9_2_1_fold gf_0 gf_1;
  pacounfold := paco9_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg9_3.

Definition monotone9_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1)(LE_2: r_2 <9= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco9_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco9_3_0 gf_0 gf_1 gf_2 (r_0 \9/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco9_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \9/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <9= rr) (CIH: l <_paco_9= rr), l <_paco_9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \9/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8) by eauto.
  clear PR; repeat (try left; do 10 paco_revert; paco_cofix_auto).
Qed.

Theorem paco9_3_0_mon: monotone9_3 (paco9_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_3_1_mon: monotone9_3 (paco9_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_3_2_mon: monotone9_3 (paco9_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_3_0_mult_strong: forall r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_3_1_mult_strong: forall r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Theorem paco9_3_2_mult_strong: forall r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 10 paco_revert; paco_cofix_auto). Qed.

Corollary paco9_3_0_mult: forall r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_0_mult_strong, paco9_3_0_mon; eauto. Qed.

Corollary paco9_3_1_mult: forall r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_1_mult_strong, paco9_3_1_mon; eauto. Qed.

Corollary paco9_3_2_mult: forall r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_2_mult_strong, paco9_3_2_mon; eauto. Qed.

Theorem paco9_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco9_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco9_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco9_3_0_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone9_3; intros; destruct PR; eauto. Qed.

Theorem paco9_3_1_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone9_3; intros; destruct PR; eauto. Qed.

Theorem paco9_3_2_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone9_3; intros; destruct PR; eauto. Qed.

End Arg9_3.

Hint Unfold monotone9_3.
Hint Resolve paco9_3_0_fold.
Hint Resolve paco9_3_1_fold.
Hint Resolve paco9_3_2_fold.

Implicit Arguments paco9_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].
Implicit Arguments paco9_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 ].

Instance paco9_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco9_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco9_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_2_unfold gf_0 gf_1 gf_2 }.

