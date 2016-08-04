Require Import List.
Require Import Util Var Val Exp Env Map CSet AutoIndTac IL.
Require Import Sim SimTactics Infra.Status.

Set Implicit Arguments.
Unset Printing Records.

Inductive nstmt : Type :=
| nstmtLet    (x : var) (e: exp) (s : nstmt)
| nstmtIf     (e : op) (s : nstmt) (t : nstmt)
| nstmtApp   (l : var) (Y:args)
| nstmtReturn (e : op)
| nstmtFun    (F : list (var * params * nstmt)) (t : nstmt).

Instance NStmt_size : Size nstmt. gen_Size. Defined.

Fixpoint freeVars (s:nstmt) : set var :=
  match s with
    | nstmtLet x e s0 => (freeVars s0 \ singleton x) ∪ Exp.freeVars e
    | nstmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Op.freeVars e
    | nstmtApp l Y => list_union (List.map Op.freeVars Y)
    | nstmtReturn e => Op.freeVars e
    | nstmtFun F s2 =>
      list_union (List.map (fun f => (freeVars (snd f) \ of_list (snd (fst f)))) F)
                 ∪ freeVars s2
  end.

(** *** Functional Semantics *)
Module F.

  Inductive block : Type :=
    blockI {
        block_L : onv block;
        block_E : onv val;
        block_F : list (var * params * nstmt);
        block_f : nat;
        block_Z := snd (fst (nth block_f block_F (0, nil, nstmtReturn (Con val_true))))
      }.

  Definition labenv := onv block.
  Definition state : Type := (labenv * onv val * nstmt)%type.

  Definition mkBlock L E F f (_:var * params * nstmt) :=
    blockI L E F f.

  Inductive step : state -> event -> state -> Prop :=
  | nstepExp L E x e b v
    (def:op_eval E e = Some v)
    : step (L, E, nstmtLet x (Operation e) b) EvtTau (L, E[x<-Some v], b)

  | stepExtern L E x f Y s vl v
    (def:omap (op_eval E) Y = Some vl)
    : step  (L, E, nstmtLet x (Call f Y) s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s)

  | nstepIfT L E
    e b1 b2 v
    (def:op_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b1)

  | nstepIfF L E
    e b1 b2 v
    (def:op_eval E e = Some v)
    (condFalse:val2bool v = false)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b2)


  | nstepGoto L E l l' Y Z s L' E' F f
    (len:length Z = length Y)
    (lEQ:l = l') (* hack: otherwise inversions confuse guardedness checker in
                  simulation proofs*)

    (Ldef:L l = Some (blockI L' E' F f)) E'' vl
    (def:omap (op_eval E) Y = Some vl)
    (sdef : get F f (l', Z, s))
    (updOk:E'[Z <-- List.map Some vl]  = E'')
    : step (L, E, nstmtApp l Y)
           EvtTau
           (L'[List.map (fst ∘ fst) F <-- List.map Some (mapi (mkBlock L' E' F) F)], E'', s)

  | stepLet (L:onv block) E F t
    : step (L, E, nstmtFun F t) EvtTau (L[List.map (fst ∘ fst) F <--
                                                   List.map Some (mapi (mkBlock L E F) F)], E, t).

  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros. inv H; inv H0; split; eauto; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. repeat (get_functional; subst); congruence.
  Qed.

  Lemma step_dec
  : reddec2 step.
  Proof.
    hnf; intros. destruct x as [[L V] []].
    - destruct e.
      + case_eq (op_eval V e); intros. left. eexists EvtTau; eauto using step.
        right. stuck.
      + case_eq (omap (op_eval V) Y); intros; try now (right; stuck).
        left. eexists (EvtExtern (ExternI f l default_val)). eauto using step.
    - case_eq (op_eval V e); intros.
      left. case_eq (val2bool v); intros; eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (L l); intros.
      + destruct b as [L' E' F' f'].
        destruct (get_dec F' f') as [[[[l' Z] s] ?]|].
        * decide (l = l'); subst.
          decide (length Z = length Y).
          case_eq (omap (op_eval V) Y); intros; [| right; stuck2].
          left. eexists EvtTau. econstructor. econstructor; eauto.
          orewrite (l' + 0=l'). eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - left. exists EvtTau. eauto using step.
  Qed.

End F.


(** *** Imperative Semantics *)
Module I.

  Inductive block : Type :=
    blockI {
        block_L : onv block;
        block_F : list (var * params * nstmt);
        block_f : nat;
        block_Z := snd (fst (nth block_f block_F (0, nil, nstmtReturn (Con val_true))))
      }.

  Definition labenv := onv block.
  Definition state : Type := (labenv * onv val * nstmt)%type.
  Definition labenv_empty : labenv := fun _ => None.

  Definition mkBlock L F f (_:var *params*nstmt):=
    blockI L F f.

  Inductive step : state -> event -> state -> Prop :=
  | nstepExp L E x e b v
    (def:op_eval E e = Some v)
    : step (L, E, nstmtLet x (Operation e) b) EvtTau (L, E[x<-Some v], b)

  | stepExtern L E x f Y s vl v
    (def:omap (op_eval E) Y = Some vl)
    : step  (L, E, nstmtLet x (Call f Y) s)
            (EvtExtern (ExternI f vl v))
            (L, E[x <- Some v], s)

  | nstepIfT L E e b1 b2 v
    (def:op_eval E e = Some v)
    (condTrue: val2bool v = true)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b1)

  | nstepIfF L E e b1 b2 v
    (def:op_eval E e = Some v)
    (condFalse:val2bool v = false)
    : step (L, E, nstmtIf e b1 b2) EvtTau (L, E, b2)

  | nstepGoto L E l l' Y Z s L' F f
    (len:length Z = length Y)
    (lEQ:l = l') (* hack: otherwise inversions confuse guardedness checker in
                  simulation proofs*)

    (Ldef:L l = Some (blockI L' F f)) E'' vl
    (def:omap (op_eval E) Y = Some vl)
    (sdef : get F f (l', Z, s))
    (updOk:E[Z <-- List.map Some vl]  = E'')
    : step (L, E, nstmtApp l Y)
           EvtTau
           (L'[List.map (fst ∘ fst) F <-- List.map Some (mapi (mkBlock L' F) F)], E'', s)

  | stepLet L E F t
    : step (L, E, nstmtFun F t)
           EvtTau
           (L[List.map (fst ∘ fst) F <-- List.map Some (mapi (mkBlock L F) F)], E, t).

  Lemma step_internally_deterministic :
    internally_deterministic step.
  Proof.
    hnf; intros. inv H; inv H0; split; eauto; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. get_functional; subst. congruence.
  Qed.

  Lemma step_externally_determined
  : externally_determined step.
  Proof.
    hnf; intros.
    inv H; inv H0; eauto; try get_functional; try congruence.
    rewrite Ldef0 in Ldef. inv Ldef. get_functional; subst. congruence.
  Qed.


  Lemma step_dec
  : reddec2 step.
  Proof.
      hnf; intros. destruct x as [[L V] []].
      - destruct e.
        + case_eq (op_eval V e); intros. left. eexists EvtTau; eauto using step.
          right. stuck.
        + case_eq (omap (op_eval V) Y); intros; try now (right; stuck).
          left. eexists (EvtExtern (ExternI f l default_val)). eauto using step.
    - case_eq (op_eval V e); intros.
      left. case_eq (val2bool v); intros; eexists EvtTau; eauto using step.
      right. stuck.
    - case_eq (L l); intros.
      + destruct b as [L' F' f'].
        destruct (get_dec F' f') as [[[[l' Z] s] ?]|].
        * decide (l = l').
          decide (length Z = length Y).
          case_eq (omap (op_eval V) Y); intros;[| now (right; stuck2)].
          left. eexists EvtTau. econstructor. econstructor; eauto.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
          right; stuck2. rewrite Ldef in H. inv H. get_functional; subst. congruence.
        * right; stuck2. rewrite Ldef in H. inv H. eauto.
      + right. stuck.
    - right. stuck.
    - left. exists EvtTau. eauto using step.
  Qed.

End I.

Definition state_result X (s:X*onv val*nstmt) : option val :=
  match s with
    | (_, E, nstmtReturn e) => op_eval E e
    | _ => None
  end.

Instance statetype_I : StateType I.state := {
  step := I.step;
  result := (@state_result I.labenv);
  step_dec := I.step_dec;
  step_internally_deterministic := I.step_internally_deterministic;
  step_externally_determined := I.step_externally_determined
}.
