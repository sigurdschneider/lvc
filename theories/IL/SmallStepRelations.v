Require Import Util Get Events StateType.

Set Implicit Arguments.

Definition functional2 :=
  fun (X Y : Type) (R : X -> Y -> X -> Prop)
  => forall x (y:Y) x1 x2, R x y x1 -> R x y x2 -> x1 = x2.

Lemma no_normal_step S Y R (σ σ':S) (e:Y)
 :  normal2 R σ
  -> R σ e σ'
  -> False.
Proof.
  intros. destruct H. hnf; eauto.
Qed.

Definition activated {S} `{StateType S} (σ:S) :=
  exists ext σ', step σ (EvtExtern ext) σ'.

Lemma no_activated_tau_step {S} `{StateType S} (σ σ':S)
 :  activated σ
  -> step σ EvtTau σ'
  -> False.
Proof.
  intros Act Step. destruct Act as [? [? Act]].
  eapply step_internally_deterministic in Act; eauto; dcr.
  congruence.
Qed.

Lemma activated_normal S `{StateType S} (σ:S)
  : activated σ
    -> normal2 step σ
    -> False.
Proof.
  intros Act Norm. inv Act. firstorder.
Qed.

Arguments activated_normal [S] [H] σ _ _.


(** ** [plus2] - transitive closure for event-labeled relations *)

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


(** ** [plus2] - reflexive, transitive closure for event-labeled relations *)

Inductive star2 (X : Type) (R : X -> event -> X -> Prop) : X -> list event -> X -> Prop :=
    star2_refl : forall x : X, star2 R x nil x
  | star2_step : forall y x x' yl z, R x y x' -> star2 R x' yl z -> star2 R x (filter_tau y yl) z.

Lemma plus2_star2 X (R: X -> event -> X -> Prop) σ1 σ2 L
  : plus2 R σ1 L σ2 -> star2 R σ1 L σ2.
Proof.
  intros Plus. general induction Plus; eauto using star2.
Qed.


Lemma star2_silent X (R:X -> event -> X -> Prop)
  :  forall (x x' : X) (L : 〔event〕) (z : X),
    R x EvtTau x' -> star2 R x' L z -> star2 R x L z.
Proof.
  intros. eapply (star2_step EvtTau); eauto.
Qed.

Lemma plus2_silent X (R:X -> event -> X -> Prop)
  :  forall (x x' : X) (L : 〔event〕) (z : X),
    R x EvtTau x' -> plus2 R x' L z -> plus2 R x L z.
Proof.
  intros. eapply (plus2S _ _ H eq_refl H0); eauto.
Qed.

Lemma star2_plus2_plus2
     : forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> plus2 R y B z -> plus2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto using plus2.
  - econstructor 2; eauto. rewrite filter_tau_app; eauto.
Qed.

Lemma star2_plus2_plus2_silent (X : Type) R (x y z : X) B
  : star2 R x nil y -> plus2 R y B z -> plus2 R x B z.
Proof.
  intros H1 H2. eapply (star2_plus2_plus2 H1 H2).
Qed.

Lemma star2_trans
 :  forall (X : Type) R (x y z : X) A B,
       star2 R x A y -> star2 R y B z -> star2 R x (A++B) z.
Proof.
  intros. general induction H; simpl; eauto.
  rewrite filter_tau_app.
  eapply star2_step; eauto.
Qed.

Lemma star2_trans_silent (X : Type) R (x y z : X) B
  : star2 R x nil y -> star2 R y B z -> star2 R x B z.
Proof.
  intros H1 H2. eapply (star2_trans H1 H2).
Qed.


Ltac relsimpl_help1 :=
  match goal with
  | [ H : ?R ?σ EvtTau _, H' : ?R ?σ _ _, IDet : internally_deterministic ?R
      |- _ ] =>
    edestruct (IDet _ _ _ _ H H');
    clear_trivial_eqs; try clear_dup
  | [ H : filter_tau ?y ?yl = nil |- _ ] =>
    try (is_var y; destruct y); try (is_var yl; destruct yl);
    invc H; simpl filter_tau in *
  | [ H : nil = filter_tau ?y ?yl |- _ ] =>
    try (is_var y; destruct y); try (is_var yl; destruct yl);
    invc H; simpl filter_tau in *
  | [ H: activated ?σ, H' : step ?σ EvtTau _ |- _ ] =>
    exfalso; eapply (no_activated_tau_step _ H H')
  | [ H : @step ?S ?ST ?σ EvtTau _, H' : step ?σ _ _ |- _ ] =>
    edestruct (@step_internally_deterministic S ST _ _ _ _ H H');
    clear_trivial_eqs; try clear_dup
  | [ H : normal2 ?R ?σ, H' : ?R ?σ _ _ |- _ ]
    => exfalso; eapply (no_normal_step _ _ H H')
  | [ H : star2 _ ?σ nil ?σ |- _ ] => clear H
  | [ H : activated ?σ, H' : normal2 _ ?σ |- _ ] =>
    exfalso; eapply (activated_normal _ H H')
  end.

Ltac relsimpl'' :=
    repeat relsimpl_help1.

Lemma activated_star_eq S `{StateType S} (σ1 σ2:S)
: star2 step σ1 nil σ2
  -> activated σ1
  -> σ1 = σ2.
Proof.
  intros Step1 Act. inv Step1; relsimpl''; eauto.
Qed.

Lemma normal_star_eq X (R:X -> event -> X -> Prop) (σ1 σ2:X)
: star2 R σ1 nil σ2
  -> normal2 R σ1
  -> σ1 = σ2.
Proof.
  intros Step1 Act. inv Step1; relsimpl''; eauto.
Qed.

Lemma activated_step_reach S `{StateType S} (σ σ' σ'':S) L
 : step σ EvtTau σ'
   -> activated σ''
   -> star2 step σ L σ''
   -> star2 step σ' L σ''.
Proof.
  intros. inv H2; eauto; relsimpl''; eauto.
Qed.

Lemma normal_step_reach S `{StateType S} (σ σ' σ'':S) L
 : step σ EvtTau σ'
   -> normal2 step σ''
   -> star2 step σ L σ''
   -> star2 step σ' L σ''.
Proof.
  intros. inv H2; eauto; relsimpl''; eauto.
Qed.

Lemma inv_plus2_step X (R:X -> event -> X -> Prop) σ1 σ2 σ3 L
  : R σ1 EvtTau σ2
    -> internally_deterministic R
    -> plus2 R σ1 L σ3
    -> star2 R σ2 L σ3.
Proof.
  intros Single IDet Plus.
  invc Plus.
  - relsimpl''. simpl. econstructor.
  - relsimpl''; simpl. eauto using plus2_star2.
Qed.

Ltac relsimpl_help2 :=
  match goal with
  | [ H : step ?σ EvtTau _, H' : star2 step ?σ _ ?σ', H'' : activated ?σ' |- _ ]
    => eapply (activated_step_reach _ H H'') in H'
  | [ H : step ?σ EvtTau _, H' : star2 step ?σ _ ?σ', H'' : normal2 _ ?σ' |- _ ]
    => eapply (normal_step_reach _ H H'') in H'
  | [ H : @step ?S ?ST ?σ EvtTau _,
          H' : @plus2 ?S (@step ?S ?ST) ?σ _ _ |- _ ] =>
    eapply (inv_plus2_step _ H (@step_internally_deterministic S ST)) in H'
  | [ Star2 : star2 ?R ?σ _ ?σ', Norm: normal2 ?R ?σ |- _ ] =>
    let EQ := fresh "EQ" in
    pose proof (normal_star_eq Star2 Norm) as EQ;
    try (is_var σ; subst σ); try (is_var σ'; subst σ')
  | [ Star2 : star2 ?R ?σ nil ?σ', Act: activated ?σ |- _ ] =>
    let EQ := fresh "EQ" in
    pose proof (activated_star_eq Star2 Act) as EQ;
    try (is_var σ; subst σ); try (is_var σ'; subst σ')
  end.

Ltac relsimpl' :=
  repeat (first [ relsimpl_help1 | relsimpl_help2 ]).

Lemma star2_reach_normal X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> normal2 R σ2a
  -> internally_deterministic R
  -> star2 R σ1 nil σ2b
  -> star2 R σ2b nil σ2a.
Proof.
  intros Star1 Normal IDet Star2.
  general induction Star2; relsimpl'; eauto.
  - invc Star1; relsimpl'.
    eauto using star2_silent.
Qed.

Lemma activated_star_reach S `{StateType S} (σ σ' σ'':S)
: activated σ''
  -> star2 step σ nil σ''
  -> star2 step σ nil σ'
  -> star2 step σ' nil σ''.
Proof.
  intros Act Star1 Star2. general induction Star2; relsimpl'; eauto.
Qed.

Lemma both_activated S `{StateType S} (σ1 σ2 σ3:S)
: star2 step σ1 nil σ2
  -> star2 step σ1 nil σ3
  -> activated σ2
  -> activated σ3
  -> σ2 = σ3.
Proof.
  intros Step1 Step2 Act1 Act2. general induction Step2; relsimpl'; eauto.
Qed.

Lemma star2_reach_normal2 X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> normal2 R σ2a
  -> normal2 R σ2b
  -> σ2a = σ2b.
Proof.
  intros Star1 Star2 IDet Normal1 Normal2.
  general induction Star1; relsimpl'; eauto.
  - general induction Star2; relsimpl'; eauto.
Qed.

Ltac relsimpl_help3 :=
  match goal with
  | [ H : star2 ?R ?σ nil _, H' : star2 ?R ?σ _ ?σ',
                                    H'' : activated ?σ' |- _ ]
    => eapply (activated_star_reach H'' H') in H
  | [ H : star2 step ?σ nil _, H' : star2 (@step ?S ?ST) ?σ _ ?σ',
                                    H'' : normal2 _ ?σ' |- _ ]
    => eapply (star2_reach_normal H' H'' (@step_internally_deterministic S ST)) in H
  end.

Ltac relsimpl :=
  repeat (first [ relsimpl_help1 | relsimpl_help2 | relsimpl_help3]).

Lemma activated_normal_star S `{StateType S} (σ σ' σ'':S)
  : star2 step σ nil σ'
    -> activated σ'
    -> star2 step σ nil σ''
    -> normal2 step σ''
    -> False.
Proof.
  intros Star1 Act Star2 Norm; relsimpl.
Qed.


Ltac not_normal H :=
  destruct H; econstructor; eexists; econstructor; eauto.


Lemma plus2_destr_nil (X : Type) R  (x z : X)
  : plus2 R x nil z -> exists y : X, R x EvtTau y /\ star2 R y nil z.
Proof.
  intros Plus. remember nil.
  induction Plus; subst; relsimpl''; eauto using star2_refl.
  - edestruct IHPlus; eauto; dcr.
    eauto using star2_silent.
Qed.

Lemma star2_plus2
: forall (X : Type) (R: X -> event -> X -> Prop) (x y z : X),
    R x EvtTau y -> star2 R y nil z -> plus2 R x nil z.
Proof.
  intros. general induction H0; relsimpl'; eauto using plus2.
  - exploit IHstar2; eauto using plus2.
    econstructor 2; eauto; reflexivity.
Qed.

Lemma star2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: star2 R σ1 nil σ2a
  -> star2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros.
  general induction H; relsimpl''; eauto using star2_silent.
  - inv H1; relsimpl''; eauto using star2_silent.
Qed.

Inductive star2n (X : Type) (R : X -> event -> X -> Prop) : nat -> X -> list event -> X -> Prop :=
    star2n_refl : forall x : X, star2n R 0 x nil x
  | S_star2n n : forall y x x' yl z,
                   R x y x'
                   -> star2n R n x' yl z
                   -> star2n R (S n) x (filter_tau y yl) z.


Lemma star2n_star2 X (R: X -> event -> X -> Prop) x A y n
: star2n R n x A y
  -> star2 R x A y.
Proof.
  intros. general induction H; eauto using star2.
Qed.

Lemma star2_star2n X (R: X -> event -> X -> Prop) x A y
: star2 R x A y
  -> exists n, star2n R n x A y.
Proof.
  intros. general induction H; eauto using star2n.
  - destruct IHstar2; eexists; econstructor; eauto.
Qed.

Lemma star2n_plus2 X (R: X -> event -> X -> Prop) x A y n
: star2n R (S n) x A y
  -> plus2 R x A y.
Proof.
  general induction n.
  - inv H. inv H2. econstructor; eauto.
  - inv H.
    econstructor 2; eauto.
Qed.

Lemma plus2_star2n X (R: X -> event -> X -> Prop) x A y
: plus2 R x A y
  -> exists n, star2n R (S n) x A y.
Proof.
  intros. general induction H; eauto using star2n.
  - destruct IHplus2; eexists; econstructor; eauto.
Qed.

Lemma star2_normal X R (x y:X)
  : star2 R x nil y
    -> normal2 R x
    -> x = y.
Proof.
  intros. inv H; eauto.
  exfalso. firstorder.
Qed.

Lemma star2_reach_silent_step (X : Type) (R:X -> event -> X -> Prop) (x y z : X)
: R x EvtTau y
  -> star2 R x nil z
  -> internally_deterministic R
  -> x = z \/ star2 R y nil z.
Proof.
  intros. inv H0; eauto.
  exploit H1; eauto. dcr; subst; eauto.
Qed.

Ltac stuck :=
  let A := fresh "A" in let v := fresh "v" in intros [v A]; inv A; repeat get_functional; isabsurd.

Ltac stuck2 :=
  let A := fresh "A" in
  let v := fresh "v" in
  let evt := fresh "evt" in
  intros [v [evt A]]; inv A; repeat get_functional; isabsurd.


Ltac not_activated H :=
  let STEP := fresh "STEP" in
  destruct H as [? [? STEP]]; inv STEP.

Lemma plus2_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b
: plus2 R σ1 nil σ2a
  -> plus2 R σ1 nil σ2b
  -> internally_deterministic R
  -> (star2 R σ2a nil σ2b \/ star2 R σ2b nil σ2a).
Proof.
  intros Plus1 Plus2 IDet.
  eapply plus2_destr_nil in Plus1. eapply plus2_destr_nil in Plus2.
  dcr. relsimpl.
  edestruct (star2_reach H1 H3); eauto using star2_trans.
Qed.

Lemma star2n_reach X (R:X -> event -> X -> Prop) σ1 σ2a σ2b n n'
: star2n R n σ1 nil σ2a
  -> star2n R n' σ1 nil σ2b
  -> internally_deterministic R
  -> (star2n R (n'-n) σ2a nil σ2b \/ star2n R (n-n') σ2b nil σ2a).
Proof.
  intros Star1 Star2 IDet.
  general induction Star1; eauto.
  - left. orewrite (n' - 0 = n'). eauto.
  - relsimpl. invc Star2; relsimpl; simpl; eauto.
    right. eapply (S_star2n _ _ H Star1).
Qed.

Lemma star2n_trans_silent (X : Type) (R : X -> event -> X -> Prop) n m x y z
  : star2n R n x nil y
    -> star2n R m y nil z
    -> star2n R (n + m) x nil z.
Proof.
  intros A B.
  general induction A; simpl; eauto.
  econstructor; eauto.
  destruct y, yl; isabsurd.
  eapply IHA; eauto.
Qed.

Lemma star2n_decomp_right (X : Type) (R : X -> event -> X -> Prop) n x y
  : star2n R (S n) x nil y
    -> exists z, star2n R n x nil z /\ R z EvtTau y.
Proof.
  general induction n.
  - repeat invtc star2n.
    destruct y0; isabsurd.
    eauto using star2n.
  - invtc star2n.
    destruct y0, yl; isabsurd.
    eapply IHn in H4; dcr.
    eauto using star2n.
Qed.
