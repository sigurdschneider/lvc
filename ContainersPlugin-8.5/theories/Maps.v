(** This file is a wrapper for the typeclass-based library
   on finite maps. Importing it will include the stuff
   necessary to start using maps in a development.
   *)

(** * Exporting interface and facts, for direct access

   We export the existing instances of ordered types available,
   the interface of sets and the facts from [SetFacts]. We also
   open the scope of map notations.
   *)
Require Export OrderedTypeEx.
Require Export MapInterface MapNotations.
Open Scope map_scope.

(* Providing a short name to access other facts about maps *)
Require MapFacts.
Module MF := MapFacts.

(** * Loading an implementation

   We require an implementation of maps. No importation
   is required, we are only interested in the side effect
   of the instance of [FMap] being added to the database.
   We load AVLs by default.
   *)
Require MapAVLInstance.