Require Import IL.


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
    let_result : forall L E x e s, result (L, E, stmtLet x e s) = None
  }.


Instance il_statetype_F : ILStateType F.labenv :=
  {
    statetype := statetype_F;
    step_let_op := F.StepLet;
    step_let_call := F.StepExtern
  }.
Proof.
  - intros. stuck2.
  - intros. stuck2.
  - intros; inv H; eauto.
  - intros; simpl; eauto.

Defined.

Instance il_statetype_I : ILStateType I.labenv :=
  {
    statetype := statetype_I;
    step_let_op := I.StepLet;
    step_let_call := I.StepExtern
  }.
Proof.
  - intros. stuck2.
  - intros. stuck2.
  - intros; inv H; eauto.
  - intros; simpl; eauto.
Defined.
