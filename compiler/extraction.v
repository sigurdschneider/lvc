Require Import ExtrOcamlBasic ExtrOcamlString.
(*Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.*)
Require Import Compiler OrderedType Parmov.

(* Unset Extraction AccessOpaque. *)

Definition foo := True.

Extraction Inline Status.bind Option.bind.

Extraction Blacklist List String Int.

Cd "compiler/extraction".

Separate Extraction AddParams.addParams DCVE (* toILF *) fromILF (* AllocationAlgo.regAssign optimize *) toDeBruijn OrderedType.SOT_as_OT parmove2.
