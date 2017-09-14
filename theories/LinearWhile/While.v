Require Import List.
Require Export Util Get Drop Var Val Isa.Ops IL.Exp
        Envs Map CSet AutoIndTac MoreList OptionMap.
Require Export IL.Events SizeInduction SmallStepRelations StateType.
Require Import SetOperations.

Inductive statement :=
| WhileCond (e:op) (s t:list statement)
| WhileWhile (e:op) (s:list statement)
| WhileLet (x:var) (e:exp)
| WhileReturn (e:op).

Instance statement_size : Size statement. gen_Size. Defined.

Definition program := list statement.

Definition state : Type := (onv val * list statement)%type.

Inductive step : state -> event -> state -> Prop :=
| StepLet p E x e v
          (def:op_eval E e = Some v)
  : step (E, WhileLet x (Operation e)::p) EvtTau (E[x<-Some v], p)
| StepExtern p E x f Y vl v
             (def:omap (op_eval E) Y = Some vl)
  : step  (E, WhileLet x (Call f Y)::p)
          (EvtExtern (ExternI f vl v))
          (E[x <- Some v], p)
| StepIfT p E e b1 b2 v
          (def:op_eval E e = Some v)
          (condTrue: val2bool v = true)
  : step (E, WhileCond e b1 b2::p) EvtTau (E, b1 ++ p)
| StepIfF p E e b1 b2 v
          (def:op_eval E e = Some v)
          (condFalse: val2bool v = false)
  : step (E, WhileCond e b1 b2::p) EvtTau (E, b2 ++ p)
| StepWhileF p E e s v
            (def:op_eval E e = Some v)
            (condFalse: val2bool v = false)
  : step (E, WhileWhile e s::p) EvtTau (E, p)
| StepWhileT p E e s v
          (def:op_eval E e = Some v)
          (condFalse: val2bool v = true)
  : step (E, WhileWhile e s::p) EvtTau (E, s ++ WhileWhile e s::p).

Lemma step_dec
  : reddec2 step.
Proof.
  hnf; intros. destruct x as [V [|[| | |]]].
  - right. stuck.
  - case_eq (op_eval V e); intros.
    left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
    right. stuck.
  - case_eq (op_eval V e); intros.
    left. case_eq (val2bool v); intros; do 2 eexists; eauto using step.
    right. stuck.
  - destruct e.
    + case_eq (op_eval V e); intros. left. do 2 eexists. eauto 20 using step.
      right. stuck.
    + case_eq (omap (op_eval V) Y); intros; try now (right; stuck).
      left; eexists (EvtExtern (ExternI f l0 (default_val))).
      eexists; eauto using step.
  - right. stuck.
Qed.


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

Definition state_result (s:state) : option val :=
  match s with
    | (E, WhileReturn e::_) => op_eval E e
    | _ => None
  end.

Instance statetype_While : StateType state := {
  step := step;
  result := state_result;
  step_dec := step_dec;
  step_internally_deterministic := step_internally_deterministic;
  step_externally_determined := step_externally_determined
}.
