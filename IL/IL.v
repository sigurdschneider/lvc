Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events Size.
Require Import SetOperations.

Set Implicit Arguments.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Notation "'args'" := (list exp) (at level 0).
(** ... while [params] is the type of the list of formal parameters *)
Notation "'params'" := (list var) (at level 0).


Inductive stmt : Type :=
| stmtLet    (x : var) (e: exp) (s : stmt) : stmt
| stmtIf     (e : exp) (s : stmt) (t : stmt) : stmt
| stmtApp    (l : lab) (Y:args) : stmt
| stmtReturn (e : exp) : stmt
| stmtExtern (x : var) (f:external) (Y:args) (s:stmt)
(* block f Z : rt = s in b *)
| stmtFun    (s:list (params * stmt)) (t : stmt) : stmt.

Instance Stmt_size : Size stmt. gen_Size. Defined.

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => (freeVars s0 \ {{x}}) ∪ Exp.freeVars e
    | stmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Exp.freeVars e
    | stmtApp l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtExtern x f Y s => (freeVars s \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | stmtFun s t =>
      list_union (List.map (fun f => (freeVars (snd f) \ of_list (fst f))) s) ∪ freeVars t
  end.

Fixpoint definedVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => {x; definedVars s0}
    | stmtIf e s1 s2 => definedVars s1 ∪ definedVars s2
    | stmtApp l Y => ∅
    | stmtReturn e => ∅
    | stmtExtern x f Y s => {x; definedVars s}
    | stmtFun s t =>
      list_union (List.map (fun f => (definedVars (snd f) ∪ of_list (fst f))) s) ∪ definedVars t
  end.

Fixpoint occurVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => {x; occurVars s0} ∪ Exp.freeVars e
    | stmtIf e s1 s2 => occurVars s1 ∪ occurVars s2 ∪ Exp.freeVars e
    | stmtApp l Y => list_union (List.map Exp.freeVars Y)
    | stmtReturn e => Exp.freeVars e
    | stmtExtern x f Y s => {x; occurVars s} ∪ list_union (List.map Exp.freeVars Y)
    | stmtFun s t =>
      list_union (List.map (fun f => (occurVars (snd f) ∪ of_list (fst f))) s) ∪ occurVars t
  end.

Lemma list_union_f_incl X `{OrderedType X} Y (f g:Y->set X) s
: (forall n y, get s n y -> f y ⊆ g y)
  -> list_union (List.map f s) ⊆ list_union (List.map g s).
Proof.
  intros. general induction s; simpl; eauto.
  norm_lunion.
  rewrite IHs, H0; eauto using get; reflexivity.
Qed.

Lemma list_union_f_eq X `{OrderedType X} Y (f g:Y->set X) s
: (forall n y, get s n y -> f y [=] g y)
  -> list_union (List.map f s) [=] list_union (List.map g s).
Proof.
  intros. general induction s; simpl; eauto.
  norm_lunion.
  rewrite IHs, H0; eauto using get; eauto.
Qed.

Lemma freeVars_occurVars s
: freeVars s ⊆ occurVars s.
Proof.
  sind s; destruct s; simpl in * |- *; eauto.
  - rewrite IH; cset_tac; intuition.
  - repeat rewrite IH; eauto.
  - rewrite IH; eauto. cset_tac; intuition.
  - rewrite IH, list_union_f_incl; eauto. reflexivity.
    intros. destruct y; simpl. rewrite IH; cset_tac; intuition; eauto.
Qed.

Hint Resolve incl_empty : cset.

Lemma list_union_f_union X `{OrderedType X} Y (f g:Y->set X) s
: list_union (List.map f s) ∪ list_union (List.map g s) [=]
             list_union (List.map (fun x => f x ∪ g x) s).
Proof.
  intros. general induction s; simpl; eauto.
  - cset_tac; intuition.
  - norm_lunion.
    rewrite <- IHs; eauto using get. cset_tac; intuition.
Qed.



Lemma occurVars_freeVars_definedVars s
: occurVars s [=] freeVars s ∪ definedVars s.
Proof.
  sind s; destruct s; simpl in * |- *; eauto with cset.
  - rewrite IH; eauto. clear_all; cset_tac; intuition; eauto.
    decide (x === a); intuition; eauto.
  - repeat rewrite IH; eauto. clear_all; cset_tac; intuition; eauto.
  - cset_tac; intuition.
  - cset_tac; intuition.
  - rewrite IH; eauto. clear_all; cset_tac; intuition; eauto.
    decide (x === a); intuition; eauto.
  - rewrite IH; eauto.
    repeat setoid_rewrite union_assoc at 1.
    setoid_rewrite union_comm at 5.
    repeat setoid_rewrite <- union_assoc.
    erewrite list_union_f_union.
    rewrite list_union_f_eq. cset_tac; intuition; eauto.
    simpl. intros. rewrite IH; eauto.
    clear_all; cset_tac; intuition; eauto. simpl in *.
    decide (a ∈ of_list a0); intuition; eauto.
Qed.

Lemma definedVars_occurVars s
: definedVars s ⊆ occurVars s.
Proof.
  sind s; destruct s; simpl in * |- *; eauto with cset.
  - rewrite IH; cset_tac; intuition.
  - repeat rewrite IH; eauto.
  - rewrite IH; eauto.
  - rewrite IH, list_union_f_incl; eauto. reflexivity.
    intros. destruct y; simpl. rewrite IH; cset_tac; intuition; eauto.
Qed.


(** ** Semantics *)

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
      block_E : onv val;
      block_Z : params;
      block_s : stmt;
      block_n : nat
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * onv val * stmt)%type.

  Definition mkBlock E n f :=
    blockI E (fst f) (snd f) n.

  Definition mkBlocks E F :=
    mapi (mkBlock E) F.

  Inductive step : state -> event -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtLet x e b) EvtTau (L, E[x<-Some v], b)

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
    : step  (L, E, stmtApp l Y)
            EvtTau
            (drop (counted l - block_n blk) L, E', block_s blk)

  | stepLet L E
    s (t:stmt)
    : step (L, E, stmtFun s t) EvtTau ((mkBlocks E s ++ L)%list, E, t)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, stmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).

  Lemma step_internally_deterministic
  : internally_deterministic step.
  Proof.
    hnf; intros.
    inv H; inv H0; split; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_externally_determined
  : externally_determined step.
  Proof.
    hnf; intros.
    inv H; inv H0; eauto; try get_functional; try congruence.
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
      left; eexists (EvtExtern (ExternI f l 0)). eexists; eauto using step.
    - left. eexists. eauto using step.
  Qed.

End F.

(** *** Imperative Semantics *)

Module I.
  Inductive block : Type :=
    blockI {
      block_Z : params;
      block_s : stmt;
      block_n : nat
    }.

  Definition labenv := list block.
  Definition state : Type := (labenv * onv val * stmt)%type.
  Definition mkBlock n f := blockI (fst f) (snd f) n.
  Definition mkBlocks F := mapi mkBlock F.

  Inductive step : state -> event -> state -> Prop :=
  | stepExp L E x e b v
    (def:exp_eval E e = Some v)
    : step (L, E, stmtLet x e b) EvtTau (L, E[x<-Some v], b)

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
    : step  (L, E, stmtApp l Y)
            EvtTau
            (drop (counted l - block_n blk) L, E', block_s blk)


  | stepLet L E
    s (t:stmt)
    : step (L, E, stmtFun s t) EvtTau ((mkBlocks s ++ L)%list, E, t)

  | stepExtern L E x f Y s vl v
    (def:omap (exp_eval E) Y = Some vl)
    : step  (L, E, stmtExtern x f Y s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s).


  Lemma step_internally_deterministic
  : internally_deterministic step.
  Proof.
    hnf; intros.
    inv H; inv H0; split; eauto; try get_functional; try congruence.
  Qed.

  Lemma step_externally_determined
  : externally_determined step.
  Proof.
    hnf; intros.
    inv H; inv H0; eauto; try get_functional; try congruence.
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
      left; eexists (EvtExtern (ExternI f l 0)). eexists; eauto using step.
    - left. eexists. eauto using step.
  Qed.

End I.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
