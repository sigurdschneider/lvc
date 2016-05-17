Require Import List Util.
Require Export SmallStepRelations StateType.

Set Implicit Arguments.
Unset Printing Records.

Class ProgramEquivalence S S' `{StateType S} `{StateType S'} :=
  {
    progeq : (S -> S' -> Prop) -> S -> S' -> Prop;
    progeq_mon : monotone2 progeq
  }.

Arguments ProgramEquivalence S S' {H} {H0}.
