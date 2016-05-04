Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.PeanoNat Omega.
Require Import AutoIndTac Util Get.

Require Export orderedBitvec.

Set Implicit Arguments.

(** HELPER FUNCTIONS for bitvector functions **)

(** zero extension **)
Fixpoint zext' (l:nat) (bv:bitvec) :=
match l with
| 0 => nil
| S l' => match bv with
         |nil => O:: zext' l' nil
         |a::b' => a::zext' l' b'
         end
end.

Lemma zext'_length : forall l bv, length (zext' l bv) = l.
Proof.
  intros. general induction l.
  - auto.
  - simpl. case bv; simpl.
    * rewrite (IHl nil); reflexivity.
    * intros. rewrite (IHl l0); reflexivity.
Qed.

Definition zext bv := zext' k bv.

Corollary zext_length : forall bv, length (zext bv) = k.
Proof.
  intros. unfold zext; rewrite (zext'_length k bv); reflexivity.
Qed.

Definition zero := zext (O::nil).

(** sign extension **)
Fixpoint sext' (l:nat) (bv:bitvec) (b:bit) :=
match l with
| 0 => nil
| S l' => match bv with
              | nil => b:: sext' l' nil b
              | a::b' => a::sext' l' b' a
          end
end.

Lemma sext'_length : forall l bv b, length (sext' l bv b) = l.
Proof.
  intros. general induction l.
  - auto.
  - simpl. case bv; simpl.
    * rewrite (IHl nil b); reflexivity.
    * intros. rewrite (IHl l0 b0); reflexivity.
Qed.

Lemma sext'_I : forall l, l > 0 -> exists bv', (sext' l nil I) = I::bv'.
Proof.
  intros. destruct l.
  - isabsurd.
  - simpl. eauto.
Qed.

Definition sext bv b := sext' k bv b.

Corollary sext_length : forall bv b, length (sext bv b) = k.
Proof.
  intros. unfold sext. rewrite (sext'_length k bv b); reflexivity.
Qed.

Definition bitComplement b :=
match b with
| I => O
| O => I
end.

(* Complement *)
Fixpoint complement' l bv :=
match l with
| 0 => nil
| S l' => match bv with
              | nil => sext' (S l') nil I
              | a::b' => bitComplement  a :: complement' l' b'
          end
end.

Lemma complement'_length : forall l bv, length (complement' l bv) = l.
Proof.
  intros. general induction l.
  - auto.
  - simpl. case bv.
    * simpl. rewrite (sext'_length l nil I); reflexivity.
    * intros; simpl. rewrite (IHl l0 ); reflexivity.
Qed.

Definition complement bv :=
  complement' k bv.

Corollary complement_length : forall bv, length (complement bv) = k.
Proof.
  intros; unfold complement. rewrite (complement'_length k bv); reflexivity.
Qed.

(** Left shift **)
Fixpoint shl s b :=
match s with
|0 => b
| S s' => O::b
end.

Fixpoint toBool b :=
match b with
| nil => false
| I::b' => true
| O::b' => toBool b'
end.

Lemma toBool_I_true:
  forall l,
    1 <= l
    -> toBool (sext' l (I::nil) I) = true.
Proof.
  intros l geq.
  destruct l; try auto; isabsurd.
Qed.

Lemma toBool_nil_ext_false:
  forall l,
    toBool (zext' l (nil)) = false.

Proof.
  intros l.
  induction l.
  - auto.
  - simpl; rewrite IHl; auto.
Qed.

Lemma toBool_O_false:
  forall l,
    toBool (zext' l (O::nil)) = false.

Proof.
  intros l; destruct l.
  - auto.
  - simpl. rewrite toBool_nil_ext_false; auto.
Qed.

Definition msb b :=
match List.rev b with
| nil => O
| a::b' => a
end.

(** Increment function based on the size of an argument**)
Fixpoint incr' (k:nat) (b:bitvec) :=
match k with
| 0 => nil
| S k' => match b with
            | nil => I::(sext' k' nil I)
            | O::b' => I:: (sext' k' b' I)
            | I::b' => O:: incr' k' b'
          end
end.

(** increment function that uses the defined size **)
Definition incr (b:bitvec) :=
incr' k (sext' k b O).

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

Fixpoint bvAndBounded k b1 b2 :=
match k with
| 0 => nil
| S k' => match b1,b2 with
              | nil, _ => nil
              | _, nil => nil
              |a::b1', b::b2' => bitAnd a b :: bvAndBounded k' b1' b2'
          end
end.

Definition bvAnd b1 b2 :=
bvAndBounded k (sext' k b1 O) (sext' k b2 O).

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
bvAddBounded k (sext' k a O) (sext' k b O) O.

Definition bvSub (a:bitvec) (b:bitvec) :bitvec :=
bvAdd( bvAdd a (complement b) ) (zext' k (I::nil)).

Fixpoint bvMult' k s a b :=
match k with
| 0 => nil
| S k' => match b with
            |b1::b' => bvAddBounded (2*k) (shl s (bvAndBit (k+s) a b1)) (bvMult' k' (S s) a b' ) O
            |nil => nil
                    end
end.


Definition bvMult a b :=
bvMult' (2*k) 0 (sext' (2*k) a O) (sext' (2*k) b O).

Definition neg b :=
bvAdd (complement b) (zext' k (I::nil)).

Definition bitEq b1 b2 :=
match b1, b2 with
|I,I => I
|O,O => I
|_,_ => O
end.

Fixpoint bvEq b1 b2 :=
match b1, b2 with
| nil, nil => sext' k (nil) I
| nil, _ => nil
| _, nil => nil
| a1::b1', a2::b2' => match bitEq a1 a2 with
                        |I => bvEq b1' b2'
                        |O => nil
                      end

end.

Fixpoint bvLessZero b1 :=
match msb b1 with
| I => true
| O => false
end.

Definition bvZero b :=
toBool (bvEq b zero).
(*
  match b with
| nil => true
| I::b' => false
| O::b' => bvZero b'
end.*)

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
  + exists (2*x).  simpl. rewrite H. auto.
  + exists ((2*x)+1). simpl. rewrite H. omega.

Qed.

(** TODO: Find better division algorithm **)
Fixpoint bvDiv' a b1 b2 :=
match a with
| 0 =>  O::nil
| S n' => match  toBool (bvEq b1 b2) with
           | true =>  (zext' k (I::nil))
           | false => incr( bvDiv' n' (bvSub b1 b2) b2)
          end
end.

Lemma sext'_nil_true : toBool (sext' k nil I) = true.
Proof.
  simpl. pose proof (sext'_I). destruct (H k).
  Focus 2.  rewrite H0. unfold toBool. econstructor.
  - pose K_ge1. apply le_lt_n_Sm in l. apply lt_S_n in l.
    change (0 < k); auto.
Qed.

(** Lemmas about the functions **)
Lemma bvEq_equiv_eq:
forall b1 b2, toBool(bvEq b1 b2) <-> eq b1 b2.

Proof.
intros; split; intros.
- general induction b1; destruct b2.
  + reflexivity.
  + simpl in H. unfold toBool in H. exfalso; assumption.
  + simpl in H. exfalso; assumption.
  + destruct a,b.
    * simpl. simpl in H. f_equal. eapply IHb1. assumption.
    * simpl in H; exfalso; assumption.
    * simpl in H; exfalso; assumption.
    * f_equal. simpl in H; eapply IHb1; assumption.
- general induction b1.
  + unfold bvEq. rewrite (sext'_nil_true); econstructor.
  + destruct a.
    * simpl. eapply (IHb1 b1). reflexivity.
    * simpl. eapply (IHb1 b1); reflexivity.
Qed.

Lemma bvEq_refl:
forall b,
toBool (bvEq b b) = true.

Proof.
intros. general induction b.
+ simpl. rewrite (sext'_nil_true); reflexivity.
+ destruct a; simpl; reflexivity.
Qed.

(** Division wrapper function. Starts the bvDiv' function with the size argument b1.
Because b1 is the biggest amount of steps needed to compute b1 / b2 (in the case where b2
is 1. As a bitvector can also be mapped to it's natural number counterpart we take this number as
the amount of steps. In the worst case this will only produce more steps then needed as 2^k is
the maximum number for natural numbers and 2^(k-1) for 2s complement.
There is also special threatening needed for signs.
Function is defined also for x/y where y = 0 because the smt solver always has total functions **)
Definition bvDiv (b1:bitvec) (b2:bitvec) :option bitvec:=
if [ b2 = zero ]
then None
else
Some (match bvLessZero b1, bvLessZero b2 with
| true, true => (bvDiv' (bitvecToNat b1) (neg b1) (neg b2))
| true, false => neg ( bvDiv' (bitvecToNat b1) (neg b1) b2)
| false, true => neg (bvDiv' (bitvecToNat b1) b1 (neg b2))
| false, false => bvDiv' (bitvecToNat b1) b1 b2
end).

Lemma not_zero:
 forall b, bvZero b = false ->  b  <> zero.

Proof.
 intros. general induction b.
- unfold bvZero in H. unfold zero. hnf; intros.
  rewrite H0 in H. unfold zero in H.
  rewrite (bvEq_refl (zext (O::nil))) in H; isabsurd.
- unfold bvZero in *; unfold zero in *. hnf; intros. rewrite H0 in H.
  rewrite (bvEq_refl (zext (O::nil))) in H; isabsurd.
Qed.

Lemma zext_nil_eq_sext:
  forall l, sext' l nil O = zext' l nil.

Proof.
  intros; general induction l.
  - simpl. reflexivity.
  - simpl. f_equal; eauto; assumption.
Qed.
