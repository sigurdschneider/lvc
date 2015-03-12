Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega Containers.OrderedTypeEx.
Require Export Infra.Option EqDec AutoIndTac Get.

Set Implicit Arguments.

Definition indexwise_R {A} {B} (R:A->B->Prop) LA LB :=
forall n a b, get LA n a -> get LB n b -> R a b.

Definition indexwise_R_dec {A} {B} {R:A->B->Prop} (Rdec:(forall a b, Computable (R a b))) LA LB
      : Computable (indexwise_R R LA LB) .
unfold Computable. revert LA LB. fix 2. intros LA LB.
destruct LA, LB; try now left; isabsurd.
intros. destruct (Rdec a b).
- destruct (indexwise_R_dec LA LB).
  + left. hnf; intros. destruct n; inv H; inv H0; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.

Definition indexwise_R_dec' {A} {B} {R:A->B->Prop} LA LB (Rdec:(forall n a b, get LA n a -> get LB n b -> Computable (R a b)))
      : Computable (indexwise_R R LA LB).
unfold Computable. revert LA LB Rdec. fix 2. intros LA LB Rdec.
destruct LA, LB; try now left; isabsurd.
intros. destruct (Rdec 0 a b).
- eauto using get.
- eauto using get.
- destruct (indexwise_R_dec' LA LB).
  + intros. eauto using get.
  + left. hnf; intros. destruct n; inv H; inv H0; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
