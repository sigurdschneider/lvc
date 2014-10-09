Require Import List.
Require Import AutoIndTac Util.

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

(** HELPER FUNCTIONS for bitvector functions **)

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
intros.  general induction b.
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

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
