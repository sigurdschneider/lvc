Require Import ExtrOcamlBasic ExtrOcamlString.
(*Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.*)
Require Import Compiler OrderedType Parmov Infra.Lattice Status CSetPartialOrder.
Require AnalysisBackward AnnotationLattice LivenessAnalysis NaturalRep InfinitePartition.
(* Unset Extraction AccessOpaque. *)

Definition foo := True.

Extraction Inline Status.bind Option.bind Computable.inst_not_cm bottom
           CSetPartialOrder.PartialOrder_Subset_Equal AnalysisBackward.makeBackwardAnalysis.

(*Extraction Inline PartialOrder_sig poLe poEq poLe_dec poEq_dec PartialOrder_Subset_Equal_Bounded
           Annotation.PartialOrder_ann SOT_as_OT SOT_cmp.*)

Extraction Inline SOT_as_OT SOT_cmp.

Extraction Inline LivenessAnalysis.liveness_transform_dep set_var_lower_bounded.

Extraction Blacklist List String Int.

Extraction Inline NaturalRep.succ NaturalRep.max InfinitePartition.stable_fresh_part InfinitePartition.least_fresh_part InfinitePartition.least_fresh_P NaturalRep.ofNat NaturalRep.asNat.

Extraction Inline InfinitePartition.inf_subset_P.

Extraction Inline NaturalRep.NaturalRepresentationPositive
           NaturalRep.NaturalRepresentationSuccPositive.

Extraction Implicit SafeFirst.safe_first [ H H0 ].

Cd "compiler/extraction".

Separate Extraction AddParams.addParams DCVE toILF fromILF AllocationAlgo.regAssign optimize  toDeBruijn OrderedType.SOT_as_OT parmove2.
