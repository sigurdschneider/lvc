Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness.
Require Import Bisim BisimTactics.


Inductive stmt : Type :=
 | stmtLet : var -> exp -> stmt -> stmt
 | stmtReturn : exp -> stmt
 | stmtIf : exp -> stmt -> stmt -> stmt.


(* TODO: Read IL/Annotation.v which defines annotations for programs
         and figure out which type X to choose such that ann X is
         the type of spilling annotations. *)
(* ann (set var * set var)*)

(* TODO: define the algorithm that takes a program and a spilling
         annotation and produces the spilled program
         assume a function [slot : var -> var] that yields the spill
         slot for a given variable *)
Fixpoint write_spills (slot: var->var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet (slot x) (Var x) (write_spills slot xs s) 
end.

Fixpoint write_loads (slot: var-> var) (xs:list var) (s:stmt) : stmt :=
match xs with
| nil => s
| x::xs => stmtLet x (Var (slot x)) (write_loads slot xs s)
end.


Fixpoint doSpill (slot: var -> var) (s:stmt) (a:ann (set var * set var)) : stmt :=
match s, a with
| stmtLet x e s, ann1 (Sp,L) a =>
    write_spills slot (to_list Sp)
                 (write_loads slot (to_list L) (stmtLet x e (doSpill slot s a)))
| _,_ => s
end.

(* TODO: read Liveness.v and figure out the type of the correctness
         predicate for spilling *)
Inductive spill_sound : nat -> (list (set var * set var)) -> (set var * set var) -> stmt -> ann (set var * set var) -> Prop :=
| SpillLet k Λ R M Sp L K Kx sl x e s
: spill_sound k Λ ({x;(R\K ∪ L)\Kx }, M ∪ Sp) s sl
->Exp.freeVars e ⊆ R\K ∪ L
->cardinal (R\K ∪ L) <= k
->cardinal ({x;((R\K) ∪ L)\Kx }) <= k
->spill_sound k Λ (R,M) (stmtLet x e s) (ann1 (Sp,L) sl)
| SpillReturn k Λ R M Sp L K e
: Exp.freeVars e ⊆ R\K ∪ L
 -> cardinal ((R\K) ∪ L) <= k
 ->spill_sound k Λ (R,M) (stmtReturn e) (ann0 (Sp,L))
| SpillIf k Λ R M Sp L K sl_s sl_t e s t
: Exp.freeVars e ⊆ R\K ∪ L
 -> cardinal (R\K ∪ L) <= k
 -> spill_sound k Λ (R\K ∪ L, M ∪ Sp) s sl_s
 -> spill_sound k Λ (R\K ∪ L, M ∪ Sp) t sl_t
 -> spill_sound k Λ (R,M) (stmtIf e s t) (ann2 (Sp,L) sl_s sl_t)
.

Fixpoint stupSpill (R : set var) (s : stmt) : ann (set var * set var) := 
(*fix stSp (R : set var) (s : stmt) : ann (set var * set var) := *)
match s with
| stmtLet x e t => ann1 (R, Exp.freeVars e) (stupSpill ((Exp.freeVars e) ∪ singleton x) t)
| stmtReturn e => ann0 (R, Exp.freeVars e)
| stmtIf e t v => ann2 (R, Exp.freeVars e) (stupSpill (Exp.freeVars e) t) (stupSpill (Exp.freeVars e) v)
(*| stmtApp f xs => ann0 (R, ∅)*)
(*| stmtFun f xs t v => ann2 (R, ∅) (stSp ∅ t) (stSp ∅ v)*)
(*| _ => ann0 (∅,∅)*)
end
(*) ∅ s*)
.

Fixpoint freeVars (s:stmt) : set var :=
  match s with
    | stmtLet x e s0 => (freeVars s0 \ singleton x) ∪ Exp.freeVars e
    | stmtIf e s1 s2 => freeVars s1 ∪ freeVars s2 ∪ Exp.freeVars e
    | stmtReturn e => Exp.freeVars e
  end.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma stupSpill_sat_spillSound (k:nat) (s:stmt) :
(* forall e : exp in s, cardinal (Exp.freeVars) <= k*)
freeVars s =  ∅ -> 
spill_sound k nil (∅,∅) s (stupSpill ∅ s).
assert (forall R M, freeVars s ⊆ R ∪ M -> spill_sound k nil (R,M) s (stupSpill R s)).
 - intros R M subs.
   induction s.
   + simpl. simpl in subs. admit.
   + admit.
   + admit.
 - intros. apply (H ∅ ∅). rewrite H0. admit.


 destruct. assert (exists K, K ⊆ R /\ cardinal K = cardinal (Exp.freeVars e)).



Theorem spill_sound_correct L E E' : spill_sound k Lsl (R,M) s alv asl
-> (forall x : var, In x R -> E x = E' x)
-> (forall x : var, In x S -> E x = E' (slot x))
-> bisim (L,E,s) (L,E', doSpill slot s asl).


(* TODO: define spilling predicate similarily to the liveness predicate
         in Liveness.v *)
