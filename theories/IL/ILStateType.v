Require Import IL.

Inductive isReturn : stmt -> Prop :=
| ReturnIsReturn e : isReturn (stmtReturn e).

Class ILStateType X :=
  {
    statetype :> StateType (X * onv val * stmt);
    step_let_op :  forall L E x e b v (def:op_eval E e = Some v),
        step (L, E, stmtLet x (Operation e) b) EvtTau (L, E[x<-Some v], b);
    step_let_call : forall L E x f Y s vl v (def:omap (op_eval E) Y = Some vl),
        step  (L, E, stmtLet x (Call f Y) s) (EvtExtern (ExternI f vl v)) (L, E[x <- Some v], s);
    let_op_normal :  forall L E x e b (def:op_eval E e = None),
        normal2 step (L, E, stmtLet x (Operation e) b);
    let_call_normal :  forall L E x f Y s (def:omap (op_eval E) Y = None),
        normal2 step (L, E, stmtLet x (Call f Y) s);
    let_call_inversion : forall L E x f Y s evt σ,
        step  (L, E, stmtLet x (Call f Y) s) evt σ
        -> exists vl v, omap (op_eval E) Y = Some vl
                /\ evt = (EvtExtern (ExternI f vl v))
                /\ σ = (L, E[x <- Some v], s);
    step_cond_true : forall L E e b1 b2 v
                  (def:op_eval E e = Some v) (condTrue: val2bool v = true),
        step (L, E, stmtIf e b1 b2) EvtTau (L, E, b1);
    step_cond_false : forall L E e b1 b2 v
                   (def:op_eval E e = Some v) (condFalse: val2bool v = false),
        step (L, E, stmtIf e b1 b2) EvtTau (L, E, b2);
    cond_normal : forall L E e b1 b2 (def:op_eval E e = None),
        normal2 step (L, E, stmtIf e b1 b2);
    result_none : forall L E s, ~isReturn s -> result (L, E, s) = None
  }.

Instance il_statetype_F : ILStateType F.labenv :=
  {
    statetype := statetype_F;
    step_let_op := F.StepLet;
    step_let_call := F.StepExtern;
    step_cond_true := F.StepIfT;
    step_cond_false := F.StepIfF
  }.
Proof.
  - intros. stuck2.
  - intros. stuck2.
  - intros; inv H; eauto.
  - intros. stuck2.
  - intros; simpl; eauto; destruct s; eauto; exfalso; eauto using isReturn.
Defined.

Instance il_statetype_I : ILStateType I.labenv :=
  {
    statetype := statetype_I;
    step_let_op := I.StepLet;
    step_let_call := I.StepExtern;
    step_cond_true := I.StepIfT;
    step_cond_false := I.StepIfF
  }.
Proof.
  - intros. stuck2.
  - intros. stuck2.
  - intros; inv H; eauto.
  - intros; stuck2.
  - intros; simpl; eauto; destruct s; eauto; exfalso; eauto using isReturn.
Defined.
