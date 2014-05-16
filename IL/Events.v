Require Import List.
Require Export Util Relations Relations2 Val Exp AutoIndTac.

Set Implicit Arguments.

Definition external := nat.

Inductive extern :=
  ExternI {
      extern_fnc : external;
      extern_args : list val;
      extern_res  : val
    }.

Inductive event :=
  | EvtExtern (call:extern)
(*  | EvtTerminate   (res:val) *)
  | EvtTau.

Definition internally_deterministic {X : Type} (R : X -> event -> X -> Prop)
:= forall x y x1 x2, R x EvtTau x1 -> R x y x2 -> x1 = x2 /\ y = EvtTau.

Definition filter_tau (o:event) (L:list event) : list event :=
  match o with
      | EvtTau => L
      | e => e :: L
  end.

Lemma filter_tau_nil evt B
 : (filter_tau evt nil ++ B)%list = filter_tau evt B.
Proof.
  destruct evt; simpl; eauto.
Qed.

Lemma filter_tau_app evt A B
 :  (filter_tau evt A ++ B)%list = filter_tau evt (A ++ B).
Proof.
  destruct evt; eauto.
Qed.

Inductive plus2 (X : Type) (R : X -> event -> X -> Prop)
: X -> list event -> X -> Prop :=
  plus2O  x y x' el
  : R x y x'
    -> el = (filter_tau y nil)
    -> plus2 R x el x'
| plus2S x y x' yl z el
  : R x y x'
    -> el = (filter_tau y yl)
    -> plus2 R x' yl z
    -> plus2 R x el z.


Inductive star2 (X : Type) (R : X -> event -> X -> Prop) : X -> list event -> X -> Prop :=
    star2_refl : forall x : X, star2 R x nil x
  | S_star2 : forall y x x' yl z, R x y x' -> star2 R x' yl z -> star2 R x (filter_tau y yl) z.


Lemma star2_plus2_plus2
     : forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> plus2 R y B z -> plus2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto using plus2.
  - econstructor 2; eauto. rewrite filter_tau_app; eauto.
Qed.

Lemma star2_trans
 :  forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> star2 R y B z -> star2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto.
  rewrite filter_tau_app.
  eapply S_star2; eauto.
Qed.

Lemma plus2_destr_nil
: forall (X : Type) R  (x z : X),
    plus2 R x nil z -> exists y : X, R x EvtTau y /\ star2 R y nil z.
Proof.
  intros. remember nil. induction H; subst.
  - destruct y; isabsurd. eexists; split; eauto using star2_refl.
  - destruct y; isabsurd. edestruct IHplus2; eauto; dcr.
    destruct yl; isabsurd.
    eexists; split; eauto.
    rewrite H0. econstructor 2; eauto.
Qed.

Lemma star2_plus2
: forall (X : Type) (R: X -> event -> X -> Prop) (x y z : X),
    R x EvtTau y -> star2 R y nil z -> plus2 R x nil z.
Proof.
  intros. general induction H0; eauto using plus2.
  - destruct y,yl; isabsurd.
    exploit IHstar2; eauto.
    econstructor 2; eauto.
Qed.

Lemma star2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros.
  general induction H; eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + right. econstructor 2; eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      edestruct (IHstar2 _ eq_refl H6); eauto.
Qed.

Lemma star2_reach_normal X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> normal2 R σ2a
  -> star2 R σ2b nil σ2a.
Proof.
  intros.
  general induction H0; eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + exfalso. eapply H3. do 2 eexists. eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      eapply IHstar2; eauto.
Qed.

Lemma plus2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: plus2 R σ1 nil σ2a
  -> plus2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros. eapply plus2_destr_nil in H. eapply plus2_destr_nil in H0.
  destruct H, H0; dcr.
  assert (x0 = x). eapply H1; eauto. subst.
  edestruct (star2_reach H4 H3); eauto using star2_trans.
Qed.


Inductive star2n (X : Type) (R : X -> event -> X -> Prop) : nat -> X -> list event -> X -> Prop :=
    star2n_refl : forall x : X, star2n R 0 x nil x
  | S_star2n n : forall y x x' yl z,
                   R x y x'
                   -> star2n R n x' yl z
                   -> star2n R (S n) x (filter_tau y yl) z.

Inductive plus2n (X : Type) (R : X -> event -> X -> Prop)
: nat -> X -> list event -> X -> Prop :=
  plus2nO x y x' el
  : R x y x'
    -> el = (filter_tau y nil)
    -> plus2n R 0 x el x'
| plus2nS n x y x' yl z el
  : R x y x'
    -> el = (filter_tau y yl)
    -> plus2n R n x' yl z
    -> plus2n R (S n)  x el z.

Lemma plus2_plus2n X (R: X -> event -> X -> Prop) x A y
: plus2 R x A y
  -> exists n, plus2n R n x A y.
Proof.
  intros. general induction H.
  - eexists; eauto using plus2n.
  - destruct IHplus2; eexists; eauto using plus2n.
Qed.

Lemma star2n_star2 X (R: X -> event -> X -> Prop) x A y n
: star2n R n x A y
  -> star2 R x A y.
Proof.
  intros. general induction H; eauto using star2.
Qed.

Lemma plus2n_star2n X (R: X -> event -> X -> Prop) x A y n
: plus2n R n x A y
  -> star2n R (S n) x A y.
Proof.
  intros. general induction H; eauto using star2n.
Qed.

Lemma star2_star2n X (R: X -> event -> X -> Prop) x A y
: star2 R x A y
  -> exists n, star2n R n x A y.
Proof.
  intros. general induction H; eauto using star2n.
  - destruct IHstar2; eexists; econstructor; eauto.
Qed.

Lemma star2n_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b n n'
: star2n R n σ1 nil σ2a
  -> star2n R n' σ1 nil σ2b
  -> internally_deterministic R
  -> (star2n R (n'-n) σ2a nil σ2b \/ star2n R (n-n') σ2b nil σ2a).
Proof.
  intros.
  general induction H; eauto.
  - left. orewrite (n' - 0 = n'). eauto.
  - destruct y, yl; isabsurd; eauto.
    inv H1.
    + right. orewrite (S n - 0 = S n). econstructor; eauto.
    + destruct y, yl; isabsurd.
      assert (x'0 = x'). eapply H2; eauto. subst.
      eapply IHstar2n; eauto.
Qed.


Lemma plus2_star2 X R (x y:X) A
: plus2 R x A y
  -> star2 R x A y.
Proof.
  intros. general induction H; simpl; eauto using star2.
Qed.




Lemma star2_normal X R (x y:X)
  : star2 R x nil y
    -> normal2 R x
    -> x = y.
Proof.
  intros. inv H; eauto.
  exfalso. firstorder.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
