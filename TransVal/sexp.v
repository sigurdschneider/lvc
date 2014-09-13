
Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Filter Exp Coherence Fresh.

Set Implicit Arguments.

Local Hint Resolve incl_empty minus_incl incl_right incl_left.

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
Definition bitvec:Type := list bit.

(**
Define SMT expressions on bitvectors. For the moment I only add +,-_2,*,/,-_1constants and variables
**)
Inductive sexp :=
|plus: sexp -> sexp -> sexp
|sub: sexp -> sexp -> sexp
|mult: sexp -> sexp -> sexp
|div: sexp -> sexp -> sexp
|neg: sexp -> sexp
|const: bitvec -> sexp
|svar: var -> sexp.

Definition bitToNat (b1:bit) :nat :=
match b1 with
|I => 1
|O => 0
end.

Lemma exists_number_bit:
forall b:bit, exists n:nat, bitToNat b = n.

Proof.
intros. destruct b.
- exists 0. reflexivity.
- exists 1. reflexivity.
Qed.

Fixpoint bitvecToNat (b:bitvec) :nat :=
match b with
|nil => 0
|b1::b' => bitToNat b1 + 2 * bitvecToNat b'
end.

Lemma exists_number_bitvec:
forall b:bitvec, exists n:nat, bitvecToNat b = n.

Proof.
intros. general induction b.
- exists 0; reflexivity.
- destruct IHb.  destruct a.
  + simpl. rewrite H. exists (2*x). reflexivity.
  + simpl. rewrite H. exists ((2*x)+1). omega.
Qed.

Definition bitAnd (b1:bit) (b2:bit) :=
match b1, b2 with
|I,I => I
|_,_ => O
end.

Definition bitOr (b1:bit) (b2:bit) :=
match b1, b2 with
|O,O => O
|_,_ => I
end.

Definition bitXor (b1:bit) (b2:bit) :=
match b1, b2 with
|O,O => O
|I,I => O
|_,_ => I
end.

Fixpoint bvAnd (a:bitvec) (b:bitvec) :=
match a, b with
|b1::a', b2::b' 
  => (bitAnd b1 b2)::(bvAnd a' b')
|_, nil
  => a
|_, _ => b
end.

Fixpoint bvOr (a:bitvec) (b:bitvec) :=
match a,b with
|b1::a',b2::b' 
  => (bitOr b1 b2)::(bvOr a' b')
|_, nil
  => a
|_,_ 
  => b
end.

Fixpoint bvAdd (a:bitvec) (b:bitvec) (c:bit) :bitvec :=
match a with
|a1::a' => let fix bvAddn (b:bitvec) (c:bit) :bitvec :=
               match b with
               |b1::b' 
                  => let c' := (bitOr (bitAnd b1 c)(bitOr (bitAnd a1 c)(bitAnd a1 b1))) in
                     let r  := (bitXor a1 (bitXor b1 c)) in
                     r ::(bvAdd a' b' c' )
               |nil
                  => let r := bitXor a1 c in
                     let c':= bitAnd a1 c in
                     r::(bvAdd a' nil c') 
               end
           in
           bvAddn b c
|nil => let fix bvAddn (b:bitvec) (c:bit) :bitvec :=
            match b with
            |b1::b'
               => let r := bitXor b1 c in
                  let c':= bitAnd b1 c in
                      r::(bvAddn b' c' )
            |nil
               => nil
            end
        in
        bvAddn b c
end.

Lemma bit_bvAdd_lO:
forall (v:bit) (b:bitvec), bvAdd (v::b) nil O = v::bvAdd b nil O.

Proof.
intros. simpl. unfold bitXor. destruct v; reflexivity.
Qed.

Lemma bit_bvAdd_lI:
forall (v:bit) (b:bitvec), bvAdd (v::b) nil I = (bitXor v I)::bvAdd b nil v.

Proof.
intros. simpl. unfold bitXor. destruct v;  reflexivity.
Qed.

Lemma bit_bvAdd_rO:
forall (v:bit) (b:bitvec), bvAdd nil (v::b) O = v:: bvAdd nil b O.

Proof.
intros. simpl. unfold bitXor. destruct v; reflexivity.
Qed.

Lemma bit_bvAdd_rI:
forall (v:bit) (b:bitvec), bvAdd nil (v::b) I = (bitXor v I)::bvAdd nil b v.

Proof.
intros. simpl. unfold bitXor. destruct v; reflexivity.

Lemma bit_to_nat: 
forall (c:bit) (b:bitvec), bitvecToNat (c::b) = bitToNat c +  2 *bitvecToNat(b).

Proof.
intros. reflexivity.
Qed.

Lemma add_nil_l:
forall b:bitvec, bvAdd b nil O = b.

Proof.
intros; destruct b.

Lemma agree_on_add b1 b2 n1 n2:
bitvecToNat b1 = n1 
-> bitvecToNat b2 = n2 
-> bitvecToNat (bvAdd b1 b2 O) = n1 + n2.

Proof.
revert b2. revert n2.
general induction b1.
- general induction b2.
  + reflexivity.
  + destruct a.
    * rewrite (bit_bvAdd_rO O b2). erewrite bit_to_nat in *. rewrite IHb2. reflexivity.
    * rewrite (bit_bvAdd_rO I b2). erewrite bit_to_nat in *. rewrite IHb2. reflexivity.
- general induction b2.
  + destruct a.
    * rewrite (bit_bvAdd_lO O b1). rewrite (bit_to_nat O (bvAdd b1 nil O)). 
      assert( A: exists n1,bitvecToNat b1 = n1) by (exact (exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 x 0 nil); eauto.
        - simpl. rewrite H. omega. 
      }
    * rewrite (bit_bvAdd_lO I b1). rewrite (bit_to_nat I (bvAdd b1 nil O)).
      assert (A: exists n1, bitvecToNat b1 = n1) by (exact(exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 x 0 nil); eauto.
        - simpl. rewrite H. omega.
      }
  + assert (A: exists n1, bitvecToNat b1 = n1) by (exact (exists_number_bitvec b1)).
    assert (B: exists n2, bitvecToNat b2 = n2) by (exact (exists_number_bitvec b2)).
    destruct a, A, B.
    * destruct a0; simpl.
      { rewrite H. rewrite H0. rewrite (IHb1 x x0 b2 H H0). omega. }
      { rewrite H. rewrite H0. rewrite (IHb1 x x0 b2 H H0). omega. }
    * erewrite bit_to_nat. rewrite (bit_to_nat I b2).  rewrite H. rewrite H0. destruct a0; simpl. 
      { rewrite (IHb1 x x0 b2 H H0). omega. }
      { erewrite IHb2.  b2 x x0 H H0). omega.
    * rewrite H. rewrite H0. simpl. rewrite (IHb1 b2 x x0 H H0). omega.
(**
evalSexp evaluates an SMT expression given an environment with the variable bindings already 
introduced and the expression to evaluate. It's returntype is a bitvector option as it is
possible that
a) a variable occurs free
b) a variable has not been defined
c) evaluation can become stuck
**)
Fixpoint evalSexp (E: var -> option bitvec)(s:sexp):option bitvec :=
match s with
|plus a b 
  => Some (vec nil)
|sub a b
  => Some (vec nil)
|mult a b
  => Some (vec nil)
|div a b
  => Some (vec nil)
| const c
  => Some c
| svar v
  => match (E v) with
         | Some b => Some b
         | None => None
     end
end.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
