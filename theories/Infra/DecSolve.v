Require Import Util Computable Get.


Ltac dec_solve := solve [ left; econstructor; eauto
                        | let H := fresh "H" in right; intro H; inv H; repeat get_functional; isabsurd; eauto ].


Tactic Notation "dec_right" :=
  let A := fresh "A" in
  right; intro A; inv A; repeat get_functional; eauto.

Tactic Notation "ensure" constr(P) := decide P; [ | dec_right].
