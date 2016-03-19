Require Import Util List OrderedType.

(**
First define bits to be a binary type with the two constructors O and I.
**)
Inductive bit:Type :=
|O:bit
|I:bit.

(**
A bitvector is now simply a list of bits. Convention: The LSB is always the first bit to ease
recursive function definitions.
**)
Definition bitvec := list bit.

(** Define the length of a bitvector k **)
(*Definition k:= 32.*)
Parameter k: nat.

Axiom K_ge1 : 1 <= k.

(** Inductive lt predicate for bits **)
Inductive ltBit :bit-> bit -> Prop :=
|ltBitO :  ltBit O I.

Definition bitCmp (b1:bit) (b2:bit) :=
match b1,b2 with
|O, O => Eq
|O,I => Lt
| I, O => Gt
| I, I => Eq
end.

Instance ltBit_trans:
Transitive ltBit.

unfold Transitive. intros. general induction H.
- general induction H0.
Defined.

Instance ltBit_irrefl:
Irreflexive ltBit.

hnf; intros. unfold RelationClasses.complement. induction x.
- intros. inversion H.
- intros. inversion H.
Defined.

Instance  rewrite_eqBit: forall x, Proper (eq ==> flip impl) (ltBit x).
unfold Proper, respectful. intros.  unfold flip.  unfold impl.  intros.  general induction H0.
-  econstructor.
Defined.

Instance lt_eq_bit_strict: OrderedType.StrictOrder ltBit eq.
econstructor.
- exact ltBit_trans.
- intros. intro. apply (ltBit_irrefl x). rewrite <- H0 in H. assumption.
Defined.

Instance OrderedType_bit : OrderedType bit :=
{ _eq := eq;
  _lt := ltBit;
  _cmp := bitCmp}.
intros. general induction x; destruct y; simpl; try now (econstructor; eauto using ltBit).
Defined.

(** Inductive lt predicate for bitvectors **)
Inductive ltBitvec : bitvec -> bitvec -> Prop :=
|ltBitvecNil a b: ltBitvec nil (a::b)
|ltBitvecCons a b c d : _lt a c ->  ltBitvec (a::b) (c::d)
|ltBitvecEq a b c d: _eq a c -> ltBitvec b d -> ltBitvec (a::b) (c::d).

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

Instance ltBitvec_trans:
Transitive ltBitvec.

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
Defined.

Instance ltBitvec_irrefl:
Irreflexive ltBitvec.
hnf; intros. unfold RelationClasses.complement.  induction x; inversion 1; subst; eauto using StrictOrder_Irreflexive.
eapply (StrictOrder_Irreflexive a a H1). intuition.
Defined.

 Instance rewrite_equal_bitvec: forall x, Proper (eq ==> impl) (ltBitvec x) .
unfold Proper, respectful. intros.  unfold impl. intros. general induction H0.
-  econstructor.
- econstructor.  assumption.
- exact (ltBitvecEq a  b c d H H0).
Defined.

Instance lt_eq_strict : OrderedType.StrictOrder ltBitvec eq.
econstructor.
- exact ltBitvec_trans.
- intros. intro. apply (ltBitvec_irrefl x).   rewrite <-  H0 in H.  assumption.
Defined.

Instance OrderedType_bitvec : OrderedType bitvec :=
  { _eq := eq;
     _lt := ltBitvec;
      _cmp := bvCmp}.
intros. general induction x; destruct y; simpl; try now (econstructor; eauto using ltBitvec).
pose proof (_compare_spec a b); destruct (IHx y);
inv H;  try now (econstructor; eauto using ltBitvec).
-  econstructor. f_equal. rewrite H2. reflexivity.
Defined.


Instance bitvec_eq_computable (s t : bitvec) : Computable (s = t).
pose proof (_compare_spec s t).
destruct (_cmp s t); simpl in *.
- left. inv H. eauto.
- right. inv H. intro; subst.
  eapply ltBitvec_irrefl. eapply H0.
- right. inv H. intro; subst.
  eapply ltBitvec_irrefl. eapply H0.
Defined.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)