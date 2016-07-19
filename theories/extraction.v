Require Import Compiler.

(* Unset Extraction AccessOpaque. *)


Extraction Inline Status.bind Option.bind toString.

Extraction Blacklist List String Int.

Extraction "extraction/lvc.ml" toILF (* fromILF AllocationAlgo.regAssign optimize *) toDeBruijn.
