Require Import Arith Coq.Lists.List Setoid Coq.Lists.SetoidList Omega Containers.OrderedTypeEx.
Require Export Infra.Option EqDec AutoIndTac Get.

Set Implicit Arguments.

Definition indexwise_R {A} {B} (R:A->B->Prop) LA LB :=
forall n a b, get LA n a -> get LB n b -> R a b.

Definition indexwise_R2_dec {A} {B} {R:A->B->Prop} LA LB (Rdec:(forall n a b, get LA n a -> get LB n b -> Computable (R a b)))
      : Computable (indexwise_R R LA LB).
unfold Computable. revert LA LB Rdec. fix 2. intros LA LB Rdec.
destruct LA, LB; try now left; isabsurd.
intros. destruct (Rdec 0 a b).
- eauto using get.
- eauto using get.
- destruct (indexwise_R2_dec LA LB).
  + intros. eauto using get.
  + left. hnf; intros. destruct n; inv H; inv H0; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.

Definition indexwise_R3 {A} {B} {C} (R:A -> B -> C -> Prop) LA LB LC :=
forall n a b c, get LA n a -> get LB n b -> get LC n c -> R a b c.

Definition indexwise_R3_dec {A} {B} {C} {R:A -> B -> C -> Prop} LA LB LC
           (Rdec:(forall n a b c, get LA n a -> get LB n b -> get LC n c -> Computable (R a b c)))
      : Computable (indexwise_R3 R LA LB LC).
unfold Computable. revert LA LB LC Rdec. fix 2. intros LA LB LC Rdec.
destruct LA, LB, LC; try now left; isabsurd.
intros. destruct (Rdec 0 a b c).
- eauto using get.
- eauto using get.
- eauto using get.
- destruct (indexwise_R3_dec LA LB LC).
  + intros. eauto using get.
  + left. hnf; intros. destruct n; inv H; inv H0; inv H1; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.

Definition indexwise_R4 {A} {B} {C} {D} (R:A -> B -> C -> D -> Prop) LA LB LC LD :=
forall n a b c d, get LA n a -> get LB n b -> get LC n c -> get LD n d -> R a b c d.

Definition indexwise_R4_dec {A} {B} {C} {D} {R:A -> B -> C -> D -> Prop} LA LB LC LD
           (Rdec:(forall n a b c d, get LA n a -> get LB n b -> get LC n c -> get LD n d
                             -> Computable (R a b c d)))
      : Computable (indexwise_R4 R LA LB LC LD).
unfold Computable. revert LA LB LC LD Rdec. fix 2. intros LA LB LC LD Rdec.
destruct LA, LB, LC, LD; try now left; isabsurd.
intros. destruct (Rdec 0 a b c d); try now eapply getLB.
- destruct (indexwise_R4_dec LA LB LC LD).
  + intros. eapply Rdec; eauto using get.
  + left. hnf; intros n ? ? ? ? GET1 GET2 GET3 GET4.
    destruct n; inv GET1; inv GET2; inv GET3; inv GET4; eauto.
  + right; intro HH. eapply n; hnf; intros; eapply HH; eauto using get.
- right; intro. eapply n; hnf; intros. eapply H; eauto using get.
Defined.
