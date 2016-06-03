Require Import List Util paco3.
Require Export SmallStepRelations StateType.

Set Implicit Arguments.
Unset Printing Records.

Class ProgramEquivalence X S S' `{StateType S} `{StateType S'} :=
  {
    progeq : (X -> S -> S' -> Prop) -> X -> S -> S' -> Prop;
    progeq_mon : monotone3 progeq
  }.

Arguments ProgramEquivalence X S S' {H} {H0}.
