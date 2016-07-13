Time Require Import Sets.
Require Import ZArith.
Open Scope Z_scope.

(** Generating reeeeally-pseudo-random numbers *)
Definition seed := 50.
Definition a := 31415821.
Definition c := 1.
Definition max := 100000000.

Definition next z := (c+a*z) mod max.

Fixpoint mk_list z (acc : list Z) (n : nat) :=
  match n with
    | O => (z, acc)
    | S n0 => mk_list (next z) (z::acc) n0
  end.
Definition mk_randoms n := snd (mk_list seed nil n).
Time Eval vm_compute in mk_randoms 1000.

Module WithTypeClasses.
(** Filling in a set with random numbers *)
  Fixpoint fill_ (s : set Z) (c : Z) (n : nat) :=
    match n with
      | O => s
      | S n0 => fill_ {c; s} (next c) n0
    end.
  Definition fill := fill_ {} seed.
  Time Eval vm_compute in elements (fill 1000).

  (** Testing membership *)
  Fixpoint check_ (s : set Z) (c : Z) (n : nat) :=
    match n with
      | O => true
      | S n0 =>
        if c \in s then check_ s (next c) n0 else false
    end.
  Definition check n := check_ (fill n) seed n.

  Time Eval vm_compute in check 1000.
End WithTypeClasses.

(* obsolete with v8.3 *)
(* Module WithModules. *)
(*   Require Import FSetList OrderedTypeEx.  *)
(*   Require Bridge FSets.OrderedTypeEx. *)

(*   Module Z_OT <: Bridge.S.  *)
(*     Definition t := Z. *)
(*     Definition Ht : OrderedType Z := SOT_as_OT. *)
(*   End Z_OT. *)
(*   Module Z_FOT := Bridge.OT_to_FOT Z_OT. *)
(*   Print Z_FOT.compare. *)
(*   Print FSets.OrderedTypeEx.Z_as_OT.compare. *)
(*   Module S := Make(Z_FOT). *)

(*   (** Filling in a set with random numbers *) *)
(*   Fixpoint fill_ (s : S.t) (c : Z) (n : nat) := *)
(*     match n with *)
(*       | O => s *)
(*       | S n0 => fill_ (S.add c s) (next c) n0 *)
(*     end. *)
(*   Definition fill := fill_ S.empty seed. *)
(*   Time Eval vm_compute in S.elements (fill 1000). *)

(*   (** Testing membership *) *)
(*   Fixpoint check_ (s : S.t) (c : Z) (n : nat) := *)
(*     match n with *)
(*       | O => true *)
(*       | S n0 =>  *)
(*         if S.mem c s then check_ s (next c) n0 else false *)
(*     end. *)
(*   Definition check n := check_ (fill n) seed n. *)

(*   Time Eval vm_compute in check 1000. *)
(* End WithModules. *)

(** Benchmarking comparison of sets *)
Section ParamSets.
  Variable SSS : @FSet Z _.

  Fixpoint s_of_l (l : list Z) : set Z :=
    match l with
      | nil => {}
      | a::q => {a; s_of_l q}
    end.

  Fixpoint mk_random_sets (z : Z) (size n: nat) : list (set Z) :=
    match n with
      | O => nil
      | S n0 =>
        let (z', l) := mk_list z nil size in
          (s_of_l l)::(mk_random_sets z' size n0)
    end.

  Definition example :=
    List.map elements (mk_random_sets seed 100 20).

  Fixpoint make_compares (z : Z) (n size : nat) (s : list (set Z)) :=
    match n with
      | O => tt
      | S n0 =>
        let z1 := next z in
        let z2 := next z1 in
        let n1 := Zabs_nat (z1 mod (Z_of_nat size)) in
        let n2 := Zabs_nat (z2 mod (Z_of_nat size)) in
          match nth n1 s {} =?= nth n2 s {} with
            | _ => make_compares (next z2) n0 size s
          end
    end.
  Definition bench (size n comps : nat) :=
    let sets := mk_random_sets seed size n in
      make_compares seed comps size sets.
  Definition bench0 := bench 100 20 50.

  Fixpoint sofl (l : list (set Z)) :
    set (FSet:=SetAVLInstance.SetAVL_FSet) (set Z) :=
    match l with
      | nil => {}
      | a::q => {a; sofl q}
    end.
  Definition bench1 := List.map elements
    (elements (sofl (mk_random_sets seed 100 20))).
End ParamSets.

(** Same time for building the initial list of sets for AVLs and lists *)
Require SetListInstance.
Time Eval vm_compute in (example SetListInstance.SetList_FSet).
Time Eval vm_compute in (bench1 SetListInstance.SetList_FSet).
Time Eval vm_compute in (bench0 SetListInstance.SetList_FSet).
Require SetAVLInstance.
Time Eval vm_compute in (example SetAVLInstance.SetAVL_FSet).
Time Eval vm_compute in (bench1 SetAVLInstance.SetAVL_FSet).
Time Eval vm_compute in (bench0 SetAVLInstance.SetAVL_FSet).
