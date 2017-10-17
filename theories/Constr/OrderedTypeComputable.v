Require Import Util Computable Containers.OrderedTypeEx.

Instance equiv_computable X `{OrderedType X} (x y: X) : Computable (_eq x y).
hnf.
pose proof (_compare_spec x y).
destruct (_cmp x y); intros.
- left. inversion H0; eauto.
- right. inversion H0. intro. rewrite H2 in H1.
  eapply (StrictOrder_Irreflexive _ _ H1). reflexivity.
- right. inversion H0. intro. rewrite H2 in H1.
  eapply (StrictOrder_Irreflexive _ _ H1). reflexivity.
Defined.

Instance ordered_type_lt_dec A `{OrderedType A} (a b: A)
  : Computable (_lt a b).
Proof.
pose proof (_compare_spec a b).
destruct (_cmp a b).
right; inv H0. hnf; intros. eapply (lt_not_eq H2 H1).
left. inv H0; eauto.
right; inv H0. intro. eapply (lt_not_gt H1 H2).
Defined.

Hint Extern 0 =>
match goal with
  [ H : _lt ?x ?x |- _ ] =>
  exfalso; eapply OrderedType.StrictOrder_Irreflexive in H; eauto
end.