Require Import List NPeano Decidable.
Require Import IL.

Set Implicit Arguments.

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
Definition k:= 32.

Definition senv:Type := var -> option bitvec.

(** Define SMT expressions on bitvectors. **)
Inductive sexp :=
(** a + b **)
|splus: sexp -> sexp -> sexp
(** a - b **)
|ssub: sexp -> sexp -> sexp
(** a * b **)
|smult: sexp -> sexp -> sexp
(** a / b **)
|sdiv: sexp -> sexp -> sexp
(** a == b **)
|seq: sexp -> sexp -> sexp
(** ! a **)
|sneg: sexp->sexp
(** constants **)
|sconst: bitvec -> sexp
(** variables **)
|svar: var -> sexp.

(** HELPER FUNCTIONS for definition of evaluation functions **)

(** zero extension **)
Fixpoint zext (k:nat) (bv:bitvec) :=
match k with
| 0 => nil
| S k' => match bv with
              |nil => O:: zext k' nil
              | a::b' => a::zext k' b'
          end
end.

(** sign extension **)
Fixpoint sext (k:nat) (bv:bitvec) (b:bit) :=
match k with
| 0 => nil
| S k' => match bv with
              | nil => b:: sext k' nil b
              | a::b' => a::sext k' b' a
          end
end.

Definition bitComplement b :=
match b with
| I => O
| O => I
end.

(* Complement *)
Fixpoint complement' k  b :=
match k with
| 0 => nil
| S k' => match sext k b O with
              | nil => nil
              | a::b' => bitComplement  a :: complement' k' b'
          end
end.

Definition complement b :=
complement' k b.

(** Left shift **)
Fixpoint shl s b :=
match s with 
|0 => b
| S s' => O::b
end.

(** Increment function based on the size of an argument**)
Fixpoint incr' (k:nat) (b:bitvec) :=
match k with
| 0 => nil
| S k' => match b with
            | nil => I::(sext k' nil I)
            | O::b' => I:: (sext k' b' I)
            | I::b' => O:: incr' k' b'
          end 
end.

(** increment function that uses the defined size **)
Definition incr (b:bitvec) :=
incr' k (sext k b O).

(** Decrement function TODO: Maybe remove it **)
Fixpoint decr (b:bitvec) :=
match b with
| nil => nil
| O::nil => O::nil
| I::b' => O::b'
| O::b' => I::decr b'
end.

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

Fixpoint bvAndBit k bv b :bitvec :=
match k with
| 0 => nil
| S k' => match bv with
              |b1:: bv' => (bitAnd b1 b) :: (bvAndBit k' bv' b)
              |nil => O::bvAndBit k' nil b
          end
end.

(* bounded addition for bitvectors such that we get the 2's complement semantics **)
Fixpoint bvAddBounded k a b c :=
match k with
| 0 => nil
| S k'=> match a with
             |a1::a' => match b with
                            |b1::b' 
                             => let c' := (bitOr (bitAnd b1 c)(bitOr (bitAnd a1 c)(bitAnd a1 b1))) in 
                                let r  := (bitXor a1 (bitXor b1 c)) in
                                r ::(bvAddBounded k' a' b' c' )
                            |nil 
                             => let r := bitXor a1 c in
                                 let c':= bitAnd a1 c in
                                 r:: (bvAddBounded k' a' nil c')
                        end
             |nil => match b with
                         |b1::b' 
                          => let r := bitXor b1 c in
                             let c' := bitAnd b1 c in
                             r:: (bvAddBounded k' nil b' c')
                          |nil => c::(bvAddBounded k' nil nil c)
                     end
         end
end.

(** Bitvector Addition for binary  numbers. Forwards the call to bvAddBounded with k defined before. **)
Definition bvAdd (a:bitvec) (b:bitvec)  :bitvec :=
bvAddBounded k (sext k a O) (sext k b O) O.

Definition bvSub (a:bitvec) (b:bitvec) :bitvec :=
bvAdd( bvAdd a (complement b) ) (zext k (I::nil)).

Fixpoint bvMult' k s a b :=
match k with
| 0 => nil
| S k' => match b with
            |b1::b' => bvAddBounded (2*k) (shl s (bvAndBit (k+s) a b1)) (bvMult' k' (S s) a b' ) O
            |nil => nil
                    end
end.


Definition bvMult a b :=
bvMult' (2*k) 0 (sext (2*k) a O) (sext (2*k) b O).

Definition neg b :=
bvAdd (complement b) (zext k (I::nil)).

Fixpoint bvEq b1 b2 :=
match b1, b2 with
| nil, nil => sext k (nil) I
| nil, _ => sext k nil O
| _, nil => sext k nil O
| a1::b1', a2::b2' => match bitAnd a1 a2 with
                        |I => bvEq b1' b2'
                        |O => sext k (nil) O
                      end

end.

Fixpoint toBool b :=
match b with
| nil => false
| I::b' => true
| O::b' => toBool b'
end.

(** Define a function to map a single bit to a natural number **)
Definition bitToNat (b1:bit) :nat :=
match b1 with
|I => 1
|O => 0
end.

(** For every bit there exists a number *)
Lemma exists_number_bit:
forall b:bit, exists n:nat, bitToNat b = n.

Proof.
intros. destruct b.
- exists 0. reflexivity.
- exists 1. reflexivity.
Qed.

(** Now define the natural number for bitvectors **)
Fixpoint bitvecToNat (b:list bit) :nat :=
match b with
|nil => 0
|b1::b' => bitToNat b1 + 2 * bitvecToNat b'
end.

(** For every bitvector there exists a number **)
Lemma exists_number_bitvec:
forall b:list bit, exists n:nat, bitvecToNat b = n.

Proof.
intros. general induction b.
- exists 0; reflexivity.
- destruct IHb.  destruct a.
  + exists (2*x).  simpl. rewrite H. omega.
  + exists ((2*x)+1). simpl. rewrite H. omega. 
Qed. 

Definition min a b :=
a-(a-b).

(** TODO: Find better division algorithm **)
(** a / b = None, b = 0, Some ( S (a -b)/b) **)
Fixpoint bvDiv' (a:nat) (b:nat) (akk:bitvec) :=
match a with
| 0 => Some akk
| S n' => match b with
           | 0 => None
           | _ => bvDiv' (min  n' (a - b)) b (incr akk)
          end
end.

Definition bvDiv (b1:bitvec) (b2:bitvec) :option bitvec:=
bvDiv' (bitvecToNat b1) (bitvecToNat b2) (O::nil).

Definition evalOn (o1:option bitvec) (o2:option bitvec) (f:bitvec->bitvec->option bitvec):=
match o1, o2 with
|Some v1, Some v2 =>  f v1 v2
| _, _ => None
end.

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
|splus a b 
  => evalOn ( evalSexp E a) (evalSexp E b) (fun a b => Some (bvAdd a b))
|ssub a b
  => evalOn  (evalSexp E a) (evalSexp E b) (fun a b => Some (bvSub a b))
|smult a b 
  => evalOn (evalSexp E a) ( evalSexp E b) (fun a b => Some (bvMult a b))
|sdiv a b  
  => evalOn ( evalSexp E a) ( evalSexp E b)  bvDiv
|seq a b
     => evalOn  (evalSexp E a) ( evalSexp E b) (fun a b => Some (bvEq a b))
| sneg v
 => let v' := evalSexp E v in
    match v' with
      | Some v => Some (neg v)
      | None => None
    end
| sconst c
  => Some c
| svar v
  => match (E v) with
         | Some b => Some b
         | None => None
     end
end.

(* Not needed stuff begins here *)
(*
Lemma incr_eq_plus_one:
forall (b:bitvec) (n:nat), bitvecToNat b = n -> bitvecToNat (incr b) = S n.

Proof.
intros. general induction b.
- reflexivity.
- assert (X: exists n', bitvecToNat (a::b) = n') by (exact (exists_number_bitvec (a::b))).
  assert (X': exists n'', bitvecToNat b = n'') by (exact (exists_number_bitvec b)).
  destruct X, X'. destruct a.
  + reflexivity.
  + simpl. rewrite (IHb x0 H0) in *. rewrite H0 in *. omega.
Qed.

(** TODO: Induction case of this proof. Maybe an additional Lemma is needed... **)
Lemma always_smaller:
forall n, min n (div2 n) = div2 n.

Proof.
intros.
general induction n.
- reflexivity.
- simpl. destruct n.
  + unfold min. omega.
  +  unfold min. simpl. 
Qed.

(** Define a min function for the recursion of the natToBitvec function. 
It must be computed with min = a-(a-b)  **)
Definition min a b :=
a-(a-b).

(** Define division by 2 as structural recursive function **)
Fixpoint div2 n :=
match n with
|0 => 0
|S (0) => 0
|S (S n') => S(div2 (n'))
end.

(* TODO: Is a lemma needed that min always evaluates to div2 n? *)
(** Define a function a function to compute the bitvector for a natural number **)
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

(** Forall natural numbers there exists a bitvector **)
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
    * exists (I:: (natToBitvec (min (S n) (S (div2 n))))). reflexivity.
    * exists (O:: (natToBitvec (min (S n) (S (div2 n))))). reflexivity.
Qed.

Lemma bijective_numbers:
forall (n:nat) (b:bitvec),
natToBitvec n = b 
<-> bitvecToNat b = n.

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

Proof.
intros.
- reflexivity.
- assert (X: exists b, natToBitvec (S n) = b) by (exact (exists_bitvec_number (S n))).
  destruct X. rewrite H.
  assert (Y: exists n, bitvecToNat x = n) by (exact (exists_number_bitvec (x))).
  destruct Y.

Lemma bit_bvAdd_lO:
forall (v:bit) (b:bitvec), bvAdd (v::b) nil O = v::bvAdd b nil O.

Proof.
intros. simpl. unfold bitXor. unfold bitAnd. destruct v.
- destruct b.
  * simpl. reflexivity.
  * simpl. unfold bitAnd. unfold bitXor. destruct b; reflexivity.
- destruct b.
  * reflexivity.
  * simpl. unfold bitAnd. unfold bitXor. destruct b; reflexivity.
Qed.

Lemma bvAdd_nil_O:
forall b, bvAdd b nil O = b.

Proof.
intros. general induction b.
- reflexivity.
- rewrite bit_bvAdd_lO. rewrite IHb. reflexivity.
Qed.


Lemma bit_bvAdd_lI:
forall (v:bit) (b:bitvec), bvAdd (v::b) nil I = (bitXor v I)::bvAdd b nil v.

Proof.
intros. simpl. unfold bitXor. destruct v.
- simpl. rewrite bvAdd_nil_O. reflexivity.
- unfold bitAnd. general induction b.
  + reflexivity.
  + simpl. unfold bitAnd. unfold bitXor. destruct a.
    * reflexivity.
    * reflexivity.
Qed.

Lemma bvAdd_nil_I:
forall b, bvAdd b nil I = incr b.

Proof.
intros. general induction b.
- reflexivity.
- simpl. unfold bitAnd. unfold bitXor. destruct a; reflexivity.
Qed.

Lemma bit_bvAdd_rO:
forall (v:bit) (b:bitvec), bvAdd nil (v::b) O = v:: bvAdd nil b O.

Proof.
intros. simpl. unfold bitAnd. unfold bitXor. destruct v. 
- destruct b. 
  + reflexivity.
  + destruct b; reflexivity.
- destruct b. 
  + reflexivity.
  + destruct b; reflexivity.
Qed.

Lemma bit_bvAdd_rI:
forall (v:bit) (b:bitvec), bvAdd nil (v::b) I = (bitXor v I)::bvAdd nil b v.

Proof.
intros. simpl. unfold bitAnd. unfold bitXor. destruct v. 
- destruct b. 
  + reflexivity.
  + destruct b; reflexivity.
- destruct b.
  + reflexivity.
  + destruct b; reflexivity.
Qed.

Lemma bit_to_nat: 
forall (c:bit) (b:bitvec), bitvecToNat (c::b) = bitToNat c +  2 *bitvecToNat(b).

Proof.
intros. reflexivity.
Qed.

Definition bvAdd b1 b2 :=
natToBitvec ((bitvecToNat b1) + (bitvecToNat b2)). 

Lemma agree_on_add b1 b2 n1 n2:
bitvecToNat b1 = n1
-> bitvecToNat b2 = n2
-> bvAdd b1 b2 O = natToBitvec(n1 + n2).

Proof.
intros. unfold bvAdd. rewrite H. rewrite H0. reflexivity.
Qed.

Definition bvSub b1 b2 :=
natToBitvec ((bitvecToNat b1) - (bitvecToNat b2)).

Lemma agree_on_sub b1 b2 n1 n2:
bitvecToNat b1  = n1
-> bitvecToNat b2 = n2
-> bvSub b1 b2 = natToBitvec (n1-n2).

Proof.
intros. unfold bvSub. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma agree_on_add b1 b2 n1 n2 c v:
bitToNat c = v
-> bitvecToNat b1 = n1 
-> bitvecToNat b2 = n2 
-> bitvecToNat (bvAdd b1 b2 c) = v + (n1 + n2).

Proof.
general induction b1.
- destruct b2.
  + destruct c. 
    * reflexivity.
    * reflexivity.
  + destruct b,c.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * simpl. assert (A:exists n, bitvecToNat b2 = n) by (exact (exists_number_bitvec b2)).
      destruct A. rewrite H in *.  rewrite (incr_eq_plus_one b2 H) in *. omega.
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

Lemma agree_on_mult b1 b2 n1 n2:
bitvecToNat b1 = n1
->bitvecToNat b2 = n2
->bitvecToNat (bvMult b1 b2 ) = n1 * n2 .

Proof.
intros. general induction b1.
- reflexivity.
- simpl.  destruct a. 
  + simpl. unfold bvMult. 
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
*)

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
