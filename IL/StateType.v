Require Import List.
Require Export Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList OptionMap Events IL.

Set Implicit Arguments.


Class StateType S := {
  step : S -> event -> S -> Prop;
  result : S -> option val;
  step_dec : reddec step;
  step_internally_deterministic : internally_deterministic step;
  step_externally_determined : externally_determined step
}.

Definition state_result X (s:X*onv val*stmt) : option val :=
  match s with
    | (_, E, stmtReturn e) => exp_eval E e
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
