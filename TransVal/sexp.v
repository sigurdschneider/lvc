
Require Import AllInRel List Map Env DecSolve.
Require Import IL Annotation AutoIndTac Bisim Exp MoreExp Filter Exp Coherence Fresh.
Require Import NPeano.

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
Definition bitvec := list bit.

Definition senv:Type := var -> option bitvec.

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

Fixpoint bitvecToNat (b:list bit) :nat :=
match b with
|nil => 0
|b1::b' => bitToNat b1 + 2 * bitvecToNat b'
end.

Lemma exists_number_bitvec:
forall b:list bit, exists n:nat, bitvecToNat b = n.

Proof.
intros. general induction b.
- exists 0; reflexivity.
- destruct IHb.  destruct a.
  + exists (2*x).  simpl. rewrite H. omega.
  + exists ((2*x)+1). simpl. rewrite H. omega. 
Qed.

Fixpoint incr (b:bitvec) :=
match b with
| nil => I::nil
| O::nil => I::nil
| O::b' => I::b'
| I::b' => O:: incr b'
end .

Compute (incr (incr nil)). 

(* min = a-(a-b)  *)

Definition min a b :=
a-(a-b).

Fixpoint div2 n :=
match n with
|0 => 0
|S (0) => 0
|S (S n') => S(div2 (n'))
end.

(** TODO: Induction case of this proof. Maybe an additional Lemma is needed... *)
Lemma always_smaller:
forall n, min (S n) (S (div2 n)) = S (div2 n).

Proof.
intros.
general induction n.
- reflexivity.
- simpl. admit. (* TODO!!! *)
Qed.

Fixpoint natToBitvec (n:nat) :=
  match n with
    |0 => nil
    |S n' => let b' := natToBitvec (min n' (div2 n))  
             in
              match n mod 2 with
                  | 0 => O::b'
                  | _ => I::b'
              end
end.

Lemma exists_bitvec_number:
forall n:nat, exists b:bitvec, natToBitvec n = b.

Proof.
intros. destruct n.
- exists (nil). reflexivity.
- simpl. destruct n. 
  + destruct (snd (divmod 0 1 0 0)).
    * simpl. exists (I::nil). reflexivity.
    * simpl. exists (O::nil). reflexivity.
  + destruct (snd (divmod (S n) 1 0 0)).
    * rewrite always_smaller. exists (I:: (natToBitvec (S (div2 n)))). reflexivity.
    * rewrite always_smaller. exists (O:: (natToBitvec (S (div2 n)))). reflexivity.
Qed.

Lemma bijective_numbers:
forall n:nat,
bitvecToNat(natToBitvec n ) = n.

Proof.
intros. general induction n.
- reflexivity.
- assert (X: exists b, natToBitvec (S n) = b) by (exact (exists_bitvec_number (S n))).
  destruct X. rewrite H.
  assert (Y: exists n, bitvecToNat x = n) by (exact (exists_number_bitvec (x))).
  destruct Y.

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
|a1::a' =>  match b with
               |b1::b' 
                  => let c' := (bitOr (bitAnd b1 c)(bitOr (bitAnd a1 c)(bitAnd a1 b1))) in
                     let r  := (bitXor a1 (bitXor b1 c)) in
                     r ::(bvAdd a' b' c' )
               |nil
                  => let r := bitXor a1 c in
                     let c':= bitAnd a1 c in
                     r::(bvAdd a' nil c') 
               end
|nil => match b with
            |b1::b'
               => let r := bitXor b1 c in
                  let c':= bitAnd b1 c in
                      r::(bvAdd nil b' c' )
            |nil
               => c::nil
       end
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
Qed.

Lemma bit_to_nat: 
forall (c:bit) (b:bitvec), bitvecToNat (c::b) = bitToNat c +  2 *bitvecToNat(b).

Proof.
intros. reflexivity.
Qed.

Lemma agree_on_add b1 b2 n1 n2 c v:
bitToNat c = v
-> bitvecToNat b1 = n1 
-> bitvecToNat b2 = n2 
-> bitvecToNat (bvAdd b1 b2 c) = v + (n1 + n2).

Proof.
general induction b1.
- general induction b2.
  + reflexivity.
  + destruct a,c.
    * rewrite (bit_bvAdd_rO O b2). erewrite bit_to_nat in *. rewrite IHb2. reflexivity.
    * rewrite (bit_bvAdd_rI O b2). erewrite bit_to_nat in *. rewrite IHb2. unfold bitXor. reflexivity.
    * rewrite (bit_bvAdd_rO I b2). erewrite bit_to_nat in *. rewrite IHb2. reflexivity.
    * rewrite (bit_bvAdd_rI I b2). erewrite bit_to_nat in *. rewrite IHb2. unfold bitXor. simpl. omega.
- general induction b2.
  + destruct a,c.
    * rewrite (bit_bvAdd_lO O b1). rewrite (bit_to_nat O (bvAdd b1 nil O)). 
      assert( A: exists n1,bitvecToNat b1 = n1) by (exact (exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 nil x 0 O 0); eauto.
        - simpl. rewrite H. omega. 
      }
    * rewrite (bit_bvAdd_lI O b1). rewrite (bit_to_nat (bitXor O I) (bvAdd b1 nil O)).
      assert(A: exists n1, bitvecToNat b1 = n1) by (exact (exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 nil x 0 O 0); eauto.
        - simpl. rewrite H. omega.
      }
    * rewrite (bit_bvAdd_lO I b1). rewrite (bit_to_nat I (bvAdd b1 nil O)).
      assert (A: exists n1, bitvecToNat b1 = n1) by (exact(exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 nil x 0 O 0); eauto.
        - simpl. rewrite H. omega.
      }
    * rewrite (bit_bvAdd_lI I b1). rewrite (bit_to_nat (bitXor I I) (bvAdd b1 nil I)).
      assert( A: exists n1, bitvecToNat b1 = n1) by (exact(exists_number_bitvec b1)).
      { destruct A. rewrite (IHb1 nil x 0 I 1); eauto.
        - simpl. rewrite H. omega.
      }
  + assert (A: exists n1, bitvecToNat b1 = n1) by (exact (exists_number_bitvec b1)).
    assert (B: exists n2, bitvecToNat b2 = n2) by (exact (exists_number_bitvec b2)).
    assert(C: bitToNat O = 0 /\ bitToNat I = 1).
    * split; eauto.
    * destruct a,a0,c, A, B, C; simpl.
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 O 0 H1 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 O 0 H1 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 O 0 H1 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 I 1 H2 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 O 0 H1 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 I 1 H2 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 I 1 H2 H H0). omega. }
    { rewrite H. rewrite H0. rewrite (IHb1 b2 x x0 I 1 H2 H H0). omega. }
Qed.

Fixpoint nGeqBool l r :bool :=
match l, r with
| 0,0 => true
| 0,_ => false
|_, 0 => true
|S(l),S(r) => nGeqBool (l) (r)
end.

Lemma number_greaterequal_zero n   :
nGeqBool n 0 = true.

Proof.
destruct n; intros; simpl.
- reflexivity.
- reflexivity.
Qed.

Definition bvGeq (a:bitvec) (b:bitvec) :bool := 
let l := bitvecToNat a in
let r := bitvecToNat b in
nGeqBool l r.

Lemma bitvec_greaterequal_zero a b:
b = nil \/ b = O::nil -> bvGeq a b = true.

Proof.
intros. assert (X:exists n1, bitvecToNat a = n1) by (exact (exists_number_bitvec a)). destruct X. 
destruct H.
- unfold bvGeq. rewrite H. rewrite H0. simpl. rewrite number_greaterequal_zero. reflexivity.
- unfold bvGeq. rewrite H. rewrite H0. simpl. rewrite number_greaterequal_zero. reflexivity. 
Qed.

Definition isZero b :=
match b with
|nil => true
|O::nil => true
|a::b => false
end.

Lemma is_not_zero b:
b <> nil /\ b <> O::nil -> isZero b = false.

Proof.
intros. destruct b.
- destruct H. exfalso. apply H. reflexivity.
- destruct b0.
  + destruct b.
    * destruct H. exfalso. apply H0. reflexivity. 
    * reflexivity. 
  + simpl. destruct b; reflexivity.
Qed.

Fixpoint bvMult' n (b:bitvec) akk :=
match n with
|0 => O::nil
|1 => akk
|S n => match b with
            | nil => O::nil 
            | O::nil => O::nil
            | _ => bvMult' n b (bvAdd b akk O)
         end
end.

Definition bvMult b1 b2 :=
bvMult' (bitvecToNat b1) b2 b2.

Lemma agree_on_mult b1 b2 n1 n2:
bitvecToNat b1 = n1
->bitvecToNat b2 = n2
->bitvecToNat (bvMult b1 b2 ) = n1 * n2 .

Proof.
intros. general induction b1.
- reflexivity.
- simpl. destruct n1, b2. 
  + reflexivity. 
  +  destruct b2.
  + simpl. unfold bvMult. destruct b1.
    * destruct a.
      { reflexivity. }
      { reflexivity. }
    * assert (H: (a::b::b1) <> nil /\ (a::b::b1) <> O::nil) by (split; hnf; intros; discriminate). 
      { rewrite (is_not_zero H). simpl. omega. }
  + simpl. destruct a, b1, b, b2.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * simpl. omega. 
    * assert (H: (O::b0::b1) <> nil /\ (O::b0::b1) <> O::nil) by (split; hnf; intros; discriminate).
       { unfold bvMult. rewrite (is_not_zero H). 
         assert (H1: (O::b::b2) <> nil /\ (O::b::b2) <> O::nil) by (split; hnf; intros; discriminate).
         rewrite (is_not_zero H1). 
Fixpoint nbvSub b c :=
match b with 
  |a::b' => match  c,a with
              |O,O => O::b'
              |O,I => I::b'
              |I,O => I:: nbvSub b' I
              |I,I => O::b'
            end
  |nil => nil
end.

Fixpoint bvSub (b1:bitvec) (b2:bitvec) (c:bit):=
match bvGeq b1 b2 with
  |true =>  match b1 with
                |a::b1' => match b2 with
                               | b::b2' => match c,a,b with 
                                               |O,O,O => O:: bvSub b1' b2' O
                                               |I,O,O => I:: bvSub b1' b2' I
                                               |O,I,O => I:: bvSub b1' b2' O
                                               |I,I,O => O:: bvSub b1' b2' O
                                               |O,O,I => I:: bvSub b1' b2' I
                                               |I,O,I => O:: bvSub b1' b2' I
                                               |O,I,I => O:: bvSub b1' b2' O
                                               |I,I,I => I:: bvSub b1' b2' I
                                            end
                               | nil => nbvSub b1 c                                    
                             end
                |nil    => nil
            end
  |false => O::nil
end.

Lemma nbvSub_decrease b c :
bitvecToNat (nbvSub b c) = bitvecToNat b - bitToNat c.

Proof.
general induction b.
- reflexivity.
- simpl. destruct c.
  + destruct a.
    { rewrite bit_to_nat. simpl. omega.}
    { rewrite bit_to_nat. simpl. omega.}
  + simpl. destruct b.
    {  destruct a. 
       - rewrite bit_to_nat. simpl. destruct a.
    { simpl. rewrite (IHb I) in *. simpl.
      assert (X: exists n1, bitvecToNat b = n1) by (exact (exists_number_bitvec b)).
      destruct X. rewrite H. 

Lemma sub_nil_c :
forall (b1:bitvec) (c:bit),bitvecToNat (bvSub b1 nil c) =  (bitvecToNat b1) - (bitToNat c).

Proof.
intros. general induction b1.
- reflexivity.
- simpl. rewrite bitvec_greaterequal_zero. 
  + destruct c.
    * destruct a; rewrite bit_to_nat; simpl; omega.
    * destruct a; rewrite bit_to_nat.
      { simpl.  

Lemma agree_on_sub b1 b2 n1 n2 c v :
bitToNat c = v
-> bitvecToNat b1 = n1
-> bitvecToNat b2 = n2
-> bitvecToNat(bvSub b1 b2 c) = (n1-n2)-v.

Proof.
intros. general induction b1.
- general induction b2.
  + reflexivity.
  + unfold bvSub. destruct (bvGeq nil (a::b2)).
    * reflexivity.
    * reflexivity.
- general induction b2.
  + simpl. assert (X:bvGeq (a::b1) nil = true ).
    * apply bitvec_greaterequal_zero. left. reflexivity.
    * rewrite X.  destruct c; simpl.
      { destruct a.
        - rewrite bit_to_nat. omega.
        - rewrite bit_to_nat. omega.
      }
      { destruct a.
        - rewrite bit_to_nat. destruct b1.
          + admit.
          + simpl.
    
  
  + admit.

(**
evalSexp evaluates an SMT expression given an environment with the variable bindings already 
introduced and the expression to evaluate. It's returntype is a bitvector option as it is
possible that
a) a variable occurs free
b) a variable has not been defined
c) evaluation can become stuck
**)
Fixpoint evalSexp (E: senv)(s:sexp):option bitvec :=
match s with
|plus a b 
  => let v1 := evalSexp E a in
     let v2 := evalSexp E b in
     match v1,v2 with
         | Some v1, Some v2 => Some (bvAdd v1 v2 O)
         | _, _ => None
     end
|sub a b
  => Some (nil)
|mult a b
  => Some (nil)
|div a b  
  => Some (nil)
| neg a
  => Some (nil)
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
