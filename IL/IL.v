Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events.

Set Implicit Arguments.

Ltac stuck2 :=
  let σ := fresh "σ" in
  let A := fresh "A" in
  let v := fresh "v" in
  let evt := fresh "evt" in
  intros [v [evt A]]; inv A; isabsurd.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Notation "'args'" := (list exp) (at level 0).
(** ... while [params] is the type of the list of formal parameters *)
Notation "'params'" := (list var) (at level 0).


Inductive stmt : Type :=
| stmtExp    (x : var) (e: exp) (s : stmt) : stmt
| stmtIf     (e : exp) (s : stmt) (t : stmt) : stmt
| stmtGoto   (l : lab) (Y:args) : stmt
| stmtReturn (e : exp) : stmt
| stmtExtern (x : var) (f:external) (Y:args) (s:stmt)
(* block f Z : rt = s in b *)
| stmtLet    (Z:params) (s : stmt) (t : stmt) : stmt.

Inductive notOccur (G:set var) : stmt -> Prop :=
  | ncExp x e s
    : x ∉ G
      -> notOccur G s
      -> Exp.notOccur G e
      -> notOccur G (stmtExp x e s)
  | ncIf e s t
    : Exp.notOccur G e
      -> notOccur G s
      -> notOccur G t
      -> notOccur G (stmtIf e s t)
  | ncRet e : Exp.notOccur G e -> notOccur G (stmtReturn e)
  | ncGoto l (Y:list exp)
    : (forall n e, get Y n e -> Exp.notOccur G e)
      -> notOccur G (stmtGoto l Y)
  | ncExtern x f Y s
    : (forall n e, get Y n e -> Exp.notOccur G e)
      -> x ∉ G
      -> notOccur G s
      -> notOccur G (stmtExtern x f Y s)
  | ncLet s Z t
    : of_list Z ∩ G [=] ∅
      -> notOccur G s
      -> notOccur G t
      -> notOccur G (stmtLet Z s t).

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => (freeVars s0 \ {{x}}) ∪ Exp.freeVars e
    | stmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Exp.freeVars e
    | stmtGoto l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtExtern x f Y s => (freeVars s \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | stmtLet Z s1 s2 => (freeVars s1 \ of_list Z) ∪ freeVars s2
  end.

Fixpoint occurVars (s:stmt) : set var :=
  match s with
    | stmtExp x e s0 => occurVars s0 ∪ {{x}}
    | stmtIf e s1 s2 => occurVars s1 ∪ occurVars s2 ∪ Exp.freeVars e
    | stmtGoto l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtExtern x f Y s => freeVars s ∪ {{x}} ∪ list_union (List.map Exp.freeVars Y)
    | stmtLet Z s1 s2 => freeVars s1 ∪ freeVars s2 ∪ of_list Z
  end.

Fixpoint rename (ϱ:env var) (s:stmt) : stmt :=
  match s with
    | stmtExp x e s => stmtExp (ϱ x) (rename_exp ϱ e) (rename ϱ s)
    | stmtIf e s t => stmtIf (rename_exp ϱ e) (rename ϱ s) (rename ϱ t)
    | stmtGoto l Y => stmtGoto l (List.map (rename_exp ϱ) Y)
    | stmtReturn e => stmtReturn (rename_exp ϱ e)
    | stmtExtern x f e s => stmtExtern (ϱ x) f (List.map (rename_exp ϱ) e) (rename ϱ s)
    | stmtLet Z s t => stmtLet (lookup_list ϱ Z) (rename ϱ s) (rename ϱ t)
  end.

Fixpoint label_closed (n:nat) (s:stmt) : Prop :=
  match s with
    | stmtExp _ _ s => label_closed n s
    | stmtIf _ s t => label_closed n s /\ label_closed n t
    | stmtGoto l _ => counted l < n
    | stmtReturn _ => True
    | stmtExtern _ _ _ s => label_closed n s
    | stmtLet _ s t => label_closed (S n) s /\ label_closed (S n) t
  end.

Lemma notOccur_incl G G' s
  : G' ⊆ G -> notOccur G s -> notOccur G' s.
Proof.
  intros A B. general induction B;
              eauto 20 using notOccur, incl_not_member, incl_meet_empty,
              Exp.notOccur_antitone.
Qed.

Add Parametric Morphism : notOccur with
  signature Subset ==> eq ==> flip impl as incl_notOccur_morphism.
Proof.
  intros; hnf; intros. general induction H0; eauto 20 using notOccur, Exp.notOccur_antitone.
  - econstructor; eauto.
    eapply incl_eq; eauto using incl_empty. rewrite <- H.
    eapply incl_meet_lr; intuition.
Qed.

Add Parametric Morphism : notOccur with
  signature Equal ==> eq ==> iff as eq_cset_notOccur_morphism.
Proof.
  intros. split; intros.
  assert (Subset y x); intuition.
  rewrite H1; eauto.
  assert (Subset x y); intuition.
  rewrite H1; eauto.
Qed.

(** ** Semantics *)

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
      block_E : onv val;
      block_Z : params;
      block_s : stmt
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * onv val * stmt)%type.

  Inductive step : state -> event -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtExp x e b) EvtTau (L, E[x<-Some v], b)

  | stepIfT L E
    e (b1 b2 : stmt) v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b1)

  | stepIfF L E
    e (b1 b2:stmt) v
    (def:exp_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b2)

  | stepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (exp_eval E) Y = Some vl) E'
    (updOk:(block_E blk) [block_Z blk <-- List.map Some vl] = E')
    : step  (L, E, stmtGoto l Y)
            EvtTau
            (drop (counted l) L, E', block_s blk)

  | stepLet L E
    s Z (t:stmt)
    : step (L, E, stmtLet Z s t) EvtTau (blockI E Z s::L, E, t)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, stmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).

  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros.
    inv H; inv H0; split; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_dec
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. do 2 eexists. eauto 20 using step.
      right. stuck.
    - case_eq (exp_eval V e); intros.
      left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?].
      decide (length (block_Z blk) = length Y).
      case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      + left. do 2 eexists. econstructor; eauto.
      + right. stuck2. get_functional; subst; eauto.
      + right. stuck2. eauto.
    - right. stuck2.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left; eexists (EvtExtern (ExternI f l (default_val))). eexists; eauto using step.
    - left. eexists. eauto using step.
  Qed.

End F.

(** *** Imperative Semantics *)

Module I.
  Inductive block : Type :=
    blockI {
      block_Z : params;
      block_s : stmt
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * onv val * stmt)%type.

  Inductive step : state -> event -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtExp x e b) EvtTau (L, E[x<-Some v], b)

  | stepIfT L E
    e (b1 b2 : stmt) v
    (def:exp_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b1)

  | stepIfF L E
    e (b1 b2:stmt) v
    (def:exp_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b2)

  | stepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (exp_eval E) Y = Some vl) E'
    (updOk:E[block_Z blk  <-- List.map Some vl] = E')
    : step  (L, E, stmtGoto l Y)
            EvtTau
            (drop (counted l) L, E', block_s blk)


  | stepLet L E
    s Z (b:stmt)
    : step (L, E, stmtLet Z s b) EvtTau (blockI Z s::L, E, b)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, stmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).


  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros.
    inv H; inv H0; split; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_dec
  : reddec step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - case_eq (exp_eval V e); intros. left. do 2 eexists. eauto 20 using step.
      right. stuck.
    - case_eq (exp_eval V e); intros.
      left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?].
      decide (length (block_Z blk) = length Y).
      case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      + left. do 2 eexists. econstructor; eauto.
      + right. stuck2. get_functional; subst; eauto.
      + right. stuck2. eauto.
    - right. stuck2.
    - case_eq (omap (exp_eval V) Y); intros; try now (right; stuck).
      left; eexists (EvtExtern (ExternI f l default_val)). eexists; eauto using step.
    - left. eexists. eauto using step.
  Qed.

End I.

Fixpoint labenvRmE (L:F.labenv) : I.labenv
  :=
  match L with
    | nil => nil
    | F.blockI E Z s::L => I.blockI Z s :: labenvRmE L
  end.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
