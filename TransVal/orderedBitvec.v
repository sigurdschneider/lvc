Require Import Util List OrderedType bitvec.

(** Inductive lt predicate for bits **)
Inductive ltBit :bit-> bit -> Prop :=
|ltBitO :  ltBit O I.

(** Equality predicate for bits *)
Inductive eqBit : bit->bit -> Prop :=
|eqBitO :  eqBit O O
|eqBitI :  eqBit I I.

Definition bitCmp (b1:bit) (b2:bit) :=
match b1,b2 with
|O, O => Eq
|O,I => Lt
| I, O => Gt
| I, I => Eq
end.

Lemma bitEq_reflexive :
Reflexive eqBit.

Proof.
unfold Reflexive. intros. destruct x; econstructor.
Qed.

Lemma bitEq_symm:
Symmetric eqBit.

Proof.
unfold Symmetric. intros. general induction H; econstructor.
Qed.

Lemma bitEq_trans:
Transitive eqBit.

Proof.
unfold Transitive. intros. general induction H.
- assumption.
- assumption.
Qed.

Instance equiv_eqbit: Equivalence eqBit.
econstructor.
- exact bitEq_reflexive.
- exact bitEq_symm.
- exact bitEq_trans.
Defined.

Lemma ltBit_trans:
Transitive ltBit.

Proof.
unfold Transitive. intros. general induction H.
- general induction H0.
Qed.

Lemma ltBit_irrefl:
Irreflexive ltBit.

Proof.
hnf; intros. unfold RelationClasses.complement. induction x.
- intros. inversion H.
- intros. inversion H.
Qed.

Instance  rewrite_eqBit: forall x, Proper (eqBit ==> flip impl) (ltBit x).
unfold Proper, respectful. intros.  unfold flip.  unfold impl.  intros.  general induction H0.
- general induction H. econstructor.
Defined.

Instance lt_eq_bit_strict: OrderedType.StrictOrder ltBit eqBit.
econstructor.
- exact ltBit_trans.
- intros. intro. apply (ltBit_irrefl x). rewrite <- H0 in H. assumption.
Defined.

Instance OrderedType_bit : OrderedType bit :=
{ _eq := eqBit;
  _lt := ltBit;
  _cmp := bitCmp}.
intros. general induction x; destruct y; simpl; try now (econstructor; eauto using ltBit).
Qed.

(** Inductive lt predicate for bitvectors **)
Inductive ltBitvec : bitvec -> bitvec -> Prop :=
|ltBitvecNil a b: ltBitvec nil (a::b)
|ltBitvecCons a b c d : _lt a c ->  ltBitvec (a::b) (c::d)
|ltBitvecEq a b c d: _eq a c -> ltBitvec b d -> ltBitvec (a::b) (c::d).

(** Equality predicate for bitvectors **)
Inductive eqBitvec:  bitvec -> bitvec -> Prop :=
|eqNil: eqBitvec nil nil
|eqCons a b c d: _eq a c -> eqBitvec b d -> eqBitvec (a::b) (c::d).

Fixpoint bvCmp  (a:bitvec) ( b:bitvec) :=
match a,b with
| nil, nil => Eq
| nil, _ => Lt
| _, nil => Gt
|a1::a' ,b1::b' => match( _cmp a1 b1 ) with
                         | Eq => bvCmp a' b'
                         | z => z
                   end
end.
(*                       | Lt, Lt => Lt
                       | Lt, Gt => Lt (* TODO *)
                       | Lt, Eq => Lt
                       |Eq, Lt => Lt
                       |Eq, Eq => Eq
                       |Eq, Gt => Gt
                       |Gt, Lt => Gt (* TODO *)
                       |Gt, Eq => Gt
                       |Gt, Gt => Gt
                                    end
end.*)

Lemma bitvecEq_reflexive :
Reflexive eqBitvec.

Proof.
unfold Reflexive. intros. general induction x.
- econstructor.
-  econstructor.
   * eauto.
   * assumption.
Qed. 

Lemma bitvecEq_symm:
Symmetric eqBitvec.

Proof.
unfold Symmetric. intros. general induction H.
- econstructor.
- econstructor.  
  * eauto.
  * assumption.
Qed.

Lemma bitvecEq_trans:
Transitive eqBitvec.

Proof.
unfold Transitive. intros. general induction H.
- assumption.
-  general induction H1.
   + econstructor. 
     *  apply transitivity with c0; eauto.
     * eapply (IHeqBitvec0). assumption.
Qed.

Instance equiv_eqbitvec : Equivalence eqBitvec.
econstructor.
- exact bitvecEq_reflexive.
- exact bitvecEq_symm.
- exact bitvecEq_trans.
Defined.  

Lemma ltBitvec_trans:
Transitive ltBitvec.

Proof.
unfold Transitive. intros. general induction H.
- general induction H0. 
  + econstructor.
  + econstructor.
-  general induction H0.
   +  econstructor. 
      * eapply transitivity with c0; eauto. 
   + econstructor.
     * rewrite <- H. assumption.
  -  general induction H1.
     + econstructor.
       * rewrite H0. assumption.
     + specialize (IHltBitvec0 d). rewrite H in H0. exact (ltBitvecEq a0 b0 c d H0 (IHltBitvec0 H1)).
Qed.

Lemma ltBitvec_irrefl:
Irreflexive ltBitvec.

Proof.
hnf; intros. unfold RelationClasses.complement.  induction x; inversion 1; subst; eauto using StrictOrder_Irreflexive.  
eapply (StrictOrder_Irreflexive a a H1). intuition.
Qed.

 Instance rewrite_equal_bitvec: forall x, Proper (equiv ==> impl) (ltBitvec x) .
unfold Proper, respectful. intros.  unfold impl. intros. general induction H0.
- general induction H. econstructor.
- general induction H0. econstructor. rewrite H in H1; assumption.
- general induction H1. rewrite H in H0. exact (ltBitvecEq a0 b0 c d H0 (IHltBitvec d H1)).
Defined.

Instance lt_eq_strict : OrderedType.StrictOrder ltBitvec eqBitvec.
econstructor.
- exact ltBitvec_trans.
- intros. intro. apply (ltBitvec_irrefl x).   rewrite <-  H0 in H.  assumption. 
Defined.

Instance OrderedType_bitvec : OrderedType bitvec := 
  { _eq := eqBitvec;
     _lt := ltBitvec;
      _cmp := bvCmp}.
intros. general induction x; destruct y; simpl; try now (econstructor; eauto using ltBitvec).
pose proof (_compare_spec a b); destruct (IHx y);
inv H;  try now (econstructor; eauto using ltBitvec).
-  econstructor.  econstructor; assumption.
Defined. 

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)