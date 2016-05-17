Require Import List Map Env AllInRel Exp MoreExp.
Require Import IL Annotation InRel AutoIndTac Liveness.

(* TODO: Read IL/Annotation.v which defines annotations for programs
         and figure out which type X to choose such that ann X is
         the type of spilling annotations. *)
(* ann (set var * set var)*)

(* TODO: define the algorithm that takes a program and a spilling
         annotation and produces the spilled program
         assume a function [slot : var -> var] that yields the spill
         slot for a given variable *)

Fixpoint doSpill (slot : var -> var) (s:stmt) (a:ann (set var * set var)) : stmt :=
  match s, a with
  | stmtLet x e s', ann1 (S, L) a =>
    write_spills S (write_loads L (stmtLet x e (doSpill slot s' a)))
  | _, _ => s
  end.


(* TODO: read Liveness.v and figure out the type of the correctness
         predicate for spilling *)

(* TODO: define spilling predicate similarily to the liveness predicate
         in Liveness.v *)
