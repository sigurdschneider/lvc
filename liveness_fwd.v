Require Import List CSet.
Require Export Env.

Export BSet.

Open Scope cset_scope.

Set Implicit Arguments.

Definition live := BSet.cset var.

