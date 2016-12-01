Require Export Setoid Coq.Classes.Morphisms Util.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Export SetDecide.

Require Import EqDec CSetNotation CSetTac.


Global Instance inst_eq_dec_ordered_type X `(OrderedType X)
  : @EqDec X _ OT_Equivalence.
destruct H. hnf; intros.
case_eq(_cmp x y); intros;
pose proof (_compare_spec x y ); rewrite H in H0. left.
inversion H0. eapply H1.
right. inversion H0. destruct OT_StrictOrder. eauto.
right. inversion H0. destruct OT_StrictOrder. symmetry. eauto.
Defined.

Instance inst_computable_In X `(OrderedType X) x s
  : Computable(x ∈ s).
case_eq (mem x s); intros.
left. eapply mem_iff; eauto.
right. eapply not_mem_iff; eauto.
Defined.

Instance Subset_computable {X} `{OrderedType X} {s t:set X}
  : Computable (Subset s t).
Proof.
  case_eq (subset s t); intro A.
  + eapply subset_iff in A. firstorder.
  + right; intro B. rewrite subset_iff in B. congruence.
Defined.

Instance Equal_computable X `{OrderedType X} (s t:set X) : Computable (s [=] t).
case_eq (equal s t); intros.
left. eapply equal_iff in H0. eauto.
right. intro. eapply equal_iff in H1. congruence.
Defined.

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

Extraction Inline inst_computable_In Subset_computable Equal_computable.

Instance exists_in_set_computable X `{OrderedType X} (s:set X) (P:X->Prop)
         `{forall x, Computable (P x)} `{Proper _ (_eq ==> iff) P}
  : Computable (exists x, x ∈ s /\ P x).
Proof.
  hnf. pattern s. eapply set_induction; intros.
  - right; intro; dcr. eapply empty_is_empty_1 in H2. cset_tac.
  - destruct H2;[left|]; dcr.
    + rewrite Add_Equal in H4. cset_tac.
    + rewrite Add_Equal in H4.
      decide (P x).
      * left. exists x. cset_tac.
      * right. intro; eapply n. dcr.
        rewrite H4 in *; clear H4. cset_tac'.
        exfalso. eapply n0. rewrite H2. eauto.
Qed.

Instance set_not_in_proper X `{OrderedType X} (s:set X)
  : Proper (_eq ==> iff) (fun x : X => x ∈ s -> False).
Proof.
  unfold Proper, respectful;
  intros x y EQ; rewrite EQ; reflexivity.
Qed.

Instance set_not_in_proper' X `{OrderedType X} (s:set X)
  : Proper (_eq ==> iff) (fun x : X => x ∉ s).
Proof.
  unfold Proper, respectful;
  intros x y EQ; rewrite EQ; reflexivity.
Qed.

Instance set_in_proper X `{OrderedType X} (s:set X)
  : Proper (_eq ==> iff) (fun x : X => x ∈ s).
Proof.
  unfold Proper, respectful;
  intros x y EQ; rewrite EQ; reflexivity.
Qed.

Hint Extern 5 (Proper (_eq ==> iff) _) => unfold Proper, respectful;
                                         let x := fresh "x" in let y := fresh "y" in
                                                              let EQ := fresh "EQ" in
                                                              intros x y EQ; rewrite EQ; reflexivity.