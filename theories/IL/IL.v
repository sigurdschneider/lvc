Require Import List.
Require Export Util Get Drop Var Val Op Exp Env Map CSet AutoIndTac MoreList OptionMap.
Require Export Events SizeInduction SmallStepRelations StateType.
Require Import SetOperations.

Set Implicit Arguments.

(** * Intermediate Language IL *)

(** ** Syntax *)

(** [args] is the type of the list of variables passed at a goto ... *)
Notation "'args'" := (list op) (at level 0).
(** ... while [params] is the type of the list of formal parameters *)
Notation "'params'" := (list var) (at level 0).

Inductive stmt : Type :=
| stmtLet    (x : var) (e: exp) (s : stmt) : stmt
| stmtIf     (e : op) (s : stmt) (t : stmt) : stmt
| stmtApp    (l : lab) (Y:args) : stmt
| stmtReturn (e : op) : stmt
(*| stmtExtern (x : var) (f:external) (Y:args) (s:stmt)*)
(* block f Z : rt = s in b *)
| stmtFun    (F:list (params * stmt)) (t : stmt) : stmt.

Instance Stmt_size : Size stmt. gen_Size. Defined.

(** *** Free, Defined and Occuring Variables *)

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => (freeVars s0 \ singleton x) ∪ Exp.freeVars e
    | stmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Op.freeVars e
    | stmtApp l Y => list_union (List.map Op.freeVars Y)
    | stmtReturn e => Op.freeVars e
    | stmtFun s t =>
      list_union (List.map (fun f => (freeVars (snd f) \ of_list (fst f))) s) ∪ freeVars t
  end.

Fixpoint definedVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => {x; definedVars s0}
    | stmtIf e s1 s2 => definedVars s1 ∪ definedVars s2
    | stmtApp l Y => ∅
    | stmtReturn e => ∅
    | stmtFun s t =>
      list_union (List.map (fun f => (definedVars (snd f) ∪ of_list (fst f))) s) ∪ definedVars t
  end.

Fixpoint occurVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => {x; occurVars s0} ∪ Exp.freeVars e
    | stmtIf e s1 s2 => occurVars s1 ∪ occurVars s2 ∪ Op.freeVars e
    | stmtApp l Y => list_union (List.map Op.freeVars Y)
    | stmtReturn e => Op.freeVars e
    | stmtFun s t =>
      list_union (List.map (fun f => (occurVars (snd f) ∪ of_list (fst f))) s) ∪ occurVars t
  end.

Lemma freeVars_occurVars s
: freeVars s ⊆ occurVars s.
Proof.
  sind s; destruct s; simpl in * |- *; repeat rewrite IH; eauto.
  - cset_tac.
  - rewrite list_union_f_incl. reflexivity.
    intros. destruct y; simpl.
    rewrite IH; cset_tac; intuition; eauto.
Qed.

Lemma occurVars_freeVars_definedVars s
: occurVars s [=] freeVars s ∪ definedVars s.
Proof.
  sind s; destruct s; simpl in * |- *; eauto with cset.
  - rewrite IH; eauto.
    clear_all; cset_tac.
    decide (x === a); eauto.
  - repeat rewrite IH; eauto.
    clear_all; cset_tac.
  - cset_tac.
  - cset_tac.
  - rewrite IH; eauto.
    repeat setoid_rewrite union_assoc at 1.
    setoid_rewrite union_comm at 5.
    repeat setoid_rewrite <- union_assoc.
    erewrite list_union_f_union.
    rewrite list_union_f_eq. cset_tac.
    simpl. intros. rewrite IH; eauto.
    clear_all; cset_tac. simpl in *.
    decide (a ∈ of_list a0); eauto.
Qed.

Lemma definedVars_occurVars s
: definedVars s ⊆ occurVars s.
Proof.
  sind s; destruct s; simpl in * |- *; eauto with cset.
  - rewrite IH; cset_tac.
  - rewrite IH, list_union_f_incl; eauto. reflexivity.
    intros. destruct y; simpl. rewrite IH; cset_tac.
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

  Inductive step : state -> event -> state -> Prop :=
  | StepLet L E x e b v
    (def:op_eval E e = Some v)
    : step (L, E, stmtLet x (Operation e) b) EvtTau (L, E[x<-Some v], b)

  | StepExtern L E x f Y s vl v
    (def:omap (op_eval E) Y = Some vl)
    : step  (L, E, stmtLet x (Call f Y) s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s)

  | StepIfT L E
    e (b1 b2 : stmt) v
    (def:op_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b1)

  | StepIfF L E
    e (b1 b2:stmt) v
    (def:op_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b2)

  | StepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (op_eval E) Y = Some vl) E'
    (updOk:(block_E blk) [block_Z blk <-- List.map Some vl] = E')
    : step  (L, E, stmtApp l Y)
            EvtTau
            (drop (counted l - block_n blk) L, E', block_s blk)

  | StepFun L E
    F (t:stmt)
    : step (L, E, stmtFun F t) EvtTau ((mapi (mkBlock E) F ++ L)%list, E, t).

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
  : reddec2 step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - destruct e.
      + case_eq (op_eval V e); intros. left. do 2 eexists. eauto 20 using step.
        right. stuck.
      + case_eq (omap (op_eval V) Y); intros; try now (right; stuck).
        left; eexists (EvtExtern (ExternI f l (default_val))). eexists; eauto using step.
    - case_eq (op_eval V e); intros.
      left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?]; [ | right; stuck2 ].
      decide (length (block_Z blk) = length Y); [ | right; stuck2 ].
      case_eq (omap (op_eval V) Y); intros; [ | right; stuck2 ].
      left. do 2 eexists. econstructor; eauto.
    - right; stuck.
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

  Inductive step : state -> event -> state -> Prop :=
  | StepLet L E x e b v
    (def:op_eval E e = Some v)
    : step (L, E, stmtLet x (Operation e) b) EvtTau (L, E[x<-Some v], b)

  | StepExtern L E x f Y s vl v
               (def:omap (op_eval E) Y = Some vl)
    : step  (L, E, stmtLet x (Call f Y) s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s)

  | StepIfT L E
    e (b1 b2 : stmt) v
    (def:op_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b1)

  | StepIfF L E
    e (b1 b2:stmt) v
    (def:op_eval E e = Some v)
    (condFalse: val2bool v = false)
    : step (L, E, stmtIf e b1 b2) EvtTau (L, E, b2)

  | StepGoto L E l Y blk vl
    (Ldef:get L (counted l) blk)
    (len:length (block_Z blk) = length Y)
    (def:omap (op_eval E) Y = Some vl) E'
    (updOk:E[block_Z blk  <-- List.map Some vl] = E')
    : step  (L, E, stmtApp l Y)
            EvtTau
            (drop (counted l - block_n blk) L, E', block_s blk)


  | StepFun L E
    s (t:stmt)
    : step (L, E, stmtFun s t) EvtTau ((mapi mkBlock s ++ L)%list, E, t).

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
  : reddec2 step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - destruct e.
      + case_eq (op_eval V e); intros. left. do 2 eexists. eauto 20 using step.
        right. stuck.
      + case_eq (omap (op_eval V) Y); intros; try now (right; stuck).
        left; eexists (EvtExtern (ExternI f l default_val)). eexists; eauto using step.
    - case_eq (op_eval V e); intros.
      left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
      right. stuck.
    - destruct (get_dec L (counted l)) as [[blk A]|?]; [| right; stuck2].
      decide (length (block_Z blk) = length Y); [| right; stuck2].
      case_eq (omap (op_eval V) Y); intros; [| right; stuck2].
      left. do 2 eexists. econstructor; eauto.
    - right. stuck2.
    - left. eexists. eauto using step.
  Qed.

End I.


Definition state_result X (s:X*onv val*stmt) : option val :=
  match s with
    | (_, E, stmtReturn e) => op_eval E e
    | _ => None
  end.

Instance statetype_F : StateType F.state := {
  step := F.step;
  result := (@state_result F.labenv);
  step_dec := F.step_dec;
  step_internally_deterministic := F.step_internally_deterministic;
  step_externally_determined := F.step_externally_determined
}.

Instance statetype_I : StateType I.state := {
  step := I.step;
  result := (@state_result I.labenv);
  step_dec := I.step_dec;
  step_internally_deterministic := I.step_internally_deterministic;
  step_externally_determined := I.step_externally_determined
}.

Ltac single_step :=
  match goal with
  | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = true |- step (_, ?E', stmtIf ?x _ _) _ ] =>
    econstructor; eauto; rewrite <- H; eauto; cset_tac; intuition
  | [ H : agree_on _ ?E ?E', I : val2bool (?E ?x) = false |- step (_, ?E', stmtIf ?x _ _) _ ] =>
    econstructor 3; eauto; rewrite <- H; eauto; cset_tac; intuition
  | [ H : val2bool _ = false |- _ ] => econstructor 4; try eassumption; try reflexivity
  | [ H : val2bool _ = true |- _ ] => econstructor 3; try eassumption; try reflexivity
  | [ H : step (?L, _ , stmtApp ?l _) _, H': get ?L (counted ?l) _ |- _] =>
    econstructor; try eapply H'; eauto
  | [ H': get ?L (counted ?l) _ |- step (?L, _ , stmtApp ?l _) _] =>
    econstructor; try eapply H'; eauto
  | _ => econstructor; eauto
  end.


Lemma ZL_mapi F L
  : I.block_Z ⊝ (mapi I.mkBlock F ++ L) = fst ⊝ F ++ I.block_Z ⊝ L.
Proof.
  rewrite List.map_app. rewrite map_mapi. unfold mapi.
  erewrite <- mapi_map_ext; [ reflexivity | simpl; reflexivity].
Qed.

Hint Extern 1 =>
match goal with
| [ |- context [ I.block_Z ⊝ (mapi I.mkBlock ?F ++ ?L) ] ] =>
  rewrite (ZL_mapi F L)
| [ |- context [ pair ⊜ (?A ++ ?B) (?C ++ ?D) ] ] =>
  rewrite (zip_app pair A C B D);
    [| eauto with len]
end.

Inductive noFun : stmt->Prop :=
| NoFunLet x e s :
   noFun s
   -> noFun (stmtLet x (Operation e) s)
| NoFunIf e s t :
   noFun s
   -> noFun t
   -> noFun (stmtIf e s t)
| NoFunCall l Y :
   noFun (stmtApp l Y)
| NoFunExp e :
   noFun (stmtReturn e).

Inductive notApp : stmt -> Prop :=
| NotAppLet x e s : notApp (stmtLet x e s)
| NotAppIf e s t : notApp (stmtIf e s t)
| NotAppReturn e : notApp (stmtReturn e)
| NotFun F t : notApp (stmtFun F t).
