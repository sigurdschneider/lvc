Require Import List NPeano Decidable.
Require Import IL Val bitvec TUtil.

Set Implicit Arguments.

(* An smt environment must be defined on every variable that occurs in the formula.
Hence it is safe to not use options here *)

(*
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
(** a <= b **)
|sleq: sexp -> sexp -> sexp
(** ! a **)
|sneg: sexp->sexp
(** constants **)
|sconst: bitvec -> sexp
(** variables **)
|svar: var -> sexp.
*)


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
