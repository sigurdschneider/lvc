(** This file is a wrapper for the typeclass-based library
   on finite sets. Importing it will include the stuff
   necessary to start using sets in a development.
   *)

(** * Exporting interface and facts, for direct access

   We export the existing instances of ordered types available,
   the interface of sets and the facts from [SetFacts]. We also
   open the scope of set notations.
   *)
Require Export OrderedTypeEx.
Require Export SetInterface.
Require Export SetFacts.
Open Scope set_scope.

(** Providing a short name to access other properties about sets *)
(* Require SetProperties. *)
(* Module SP := SetProperties. *)

(** * Loading an implementation

   We require an implementation of sets. No importation
   is required, we are only interested in the side effect
   of the instance of [FSet] being added to the database.
   We load AVLs by default.
   *)
Require SetAVLInstance.