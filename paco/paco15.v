Require Export paconotation pacotac pacodef pacotacuser.
Set Implicit Arguments.

(** ** Predicates of Arity 15
*)

(** 1 Mutual Coinduction *)

Section Arg15_1.

Definition monotone15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE: r <15= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

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
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf [].

Theorem paco15_acc: forall
  l r (OBG: forall rr (INC: r <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15 gf rr),
  l <15= paco15 gf r.
Proof.
  intros; assert (SIM: paco15 gf (r \15/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_mon: monotone15 (paco15 gf).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_mult_strong: forall r,
  paco15 gf (upaco15 gf r) <15= paco15 gf r.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Corollary paco15_mult: forall r,
  paco15 gf (paco15 gf r) <15= paco15 gf r.
Proof. intros; eapply paco15_mult_strong, paco15_mon; eauto. Qed.

Theorem paco15_fold: forall r,
  gf (upaco15 gf r) <15= paco15 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco15_unfold: forall (MON: monotone15 gf) r,
  paco15 gf r <15= gf (upaco15 gf r).
Proof. unfold monotone15; intros; destruct PR; eauto. Qed.

End Arg15_1.

Hint Unfold monotone15.
Hint Resolve paco15_fold.

Implicit Arguments paco15_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].

Instance paco15_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_acc gf;
  pacomult   := paco15_mult gf;
  pacofold   := paco15_fold gf;
  pacounfold := paco15_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg15_2.

Definition monotone15_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

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
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].

Theorem paco15_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15_2_0 gf_0 gf_1 rr r_1),
  l <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco15_2_0 gf_0 gf_1 (r_0 \15/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15_2_1 gf_0 gf_1 r_0 rr),
  l <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco15_2_1 gf_0 gf_1 r_0 (r_1 \15/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_2_0_mon: monotone15_2 (paco15_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_2_1_mon: monotone15_2 (paco15_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_2_0_mult_strong: forall r_0 r_1,
  paco15_2_0 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_2_1_mult_strong: forall r_0 r_1,
  paco15_2_1 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Corollary paco15_2_0_mult: forall r_0 r_1,
  paco15_2_0 gf_0 gf_1 (paco15_2_0 gf_0 gf_1 r_0 r_1) (paco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco15_2_0_mult_strong, paco15_2_0_mon; eauto. Qed.

Corollary paco15_2_1_mult: forall r_0 r_1,
  paco15_2_1 gf_0 gf_1 (paco15_2_0 gf_0 gf_1 r_0 r_1) (paco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco15_2_1_mult_strong, paco15_2_1_mon; eauto. Qed.

Theorem paco15_2_0_fold: forall r_0 r_1,
  gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco15_2_1_fold: forall r_0 r_1,
  gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco15_2_0_unfold: forall (MON: monotone15_2 gf_0) (MON: monotone15_2 gf_1) r_0 r_1,
  paco15_2_0 gf_0 gf_1 r_0 r_1 <15= gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone15_2; intros; destruct PR; eauto. Qed.

Theorem paco15_2_1_unfold: forall (MON: monotone15_2 gf_0) (MON: monotone15_2 gf_1) r_0 r_1,
  paco15_2_1 gf_0 gf_1 r_0 r_1 <15= gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone15_2; intros; destruct PR; eauto. Qed.

End Arg15_2.

Hint Unfold monotone15_2.
Hint Resolve paco15_2_0_fold.
Hint Resolve paco15_2_1_fold.

Implicit Arguments paco15_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].

Instance paco15_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_2_0_acc gf_0 gf_1;
  pacomult   := paco15_2_0_mult gf_0 gf_1;
  pacofold   := paco15_2_0_fold gf_0 gf_1;
  pacounfold := paco15_2_0_unfold gf_0 gf_1 }.

Instance paco15_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_2_1_acc gf_0 gf_1;
  pacomult   := paco15_2_1_mult gf_0 gf_1;
  pacofold   := paco15_2_1_fold gf_0 gf_1;
  pacounfold := paco15_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg15_3.

Definition monotone15_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1)(LE_2: r_2 <15= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

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
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Implicit Arguments gf_0 [].
Implicit Arguments gf_1 [].
Implicit Arguments gf_2 [].

Theorem paco15_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco15_3_0 gf_0 gf_1 gf_2 (r_0 \15/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco15_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \15/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <15= rr) (CIH: l <_paco_15= rr), l <_paco_15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \15/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) by eauto.
  clear PR; repeat (try left; do 16 paco_revert; paco_cofix_auto).
Qed.

Theorem paco15_3_0_mon: monotone15_3 (paco15_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_3_1_mon: monotone15_3 (paco15_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_3_2_mon: monotone15_3 (paco15_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_3_0_mult_strong: forall r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_3_1_mult_strong: forall r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Theorem paco15_3_2_mult_strong: forall r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 16 paco_revert; paco_cofix_auto). Qed.

Corollary paco15_3_0_mult: forall r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_0_mult_strong, paco15_3_0_mon; eauto. Qed.

Corollary paco15_3_1_mult: forall r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_1_mult_strong, paco15_3_1_mon; eauto. Qed.

Corollary paco15_3_2_mult: forall r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_2_mult_strong, paco15_3_2_mon; eauto. Qed.

Theorem paco15_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco15_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco15_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco15_3_0_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone15_3; intros; destruct PR; eauto. Qed.

Theorem paco15_3_1_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone15_3; intros; destruct PR; eauto. Qed.

Theorem paco15_3_2_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone15_3; intros; destruct PR; eauto. Qed.

End Arg15_3.

Hint Unfold monotone15_3.
Hint Resolve paco15_3_0_fold.
Hint Resolve paco15_3_1_fold.
Hint Resolve paco15_3_2_fold.

Implicit Arguments paco15_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].
Implicit Arguments paco15_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 ].

Instance paco15_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco15_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco15_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_2_unfold gf_0 gf_1 gf_2 }.

