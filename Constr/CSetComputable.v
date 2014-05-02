Require Export Setoid Coq.Classes.Morphisms.  
Require Export Sets SetInterface SetConstructs SetProperties.
Require Export SetDecide.

Require Import EqDec CSetNotation.


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

Extraction Inline inst_computable_In Subset_computable Equal_computable.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)



