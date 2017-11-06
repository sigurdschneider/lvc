Require Import ExtrOcamlBasic ExtrOcamlString.
(*Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.*)
Require Import Compiler OrderedType Parmov Infra.Lattice Status CSetPartialOrder.
Require AnalysisBackward AnnotationLattice LivenessAnalysis NaturalRep InfinitePartition.
(* Unset Extraction AccessOpaque. *)

Require ToLinear LinearToAsm IsLinearizable.
Require compcert.driver.Compiler.
Require compcert.lib.Floats.
Require compcert.common.Values.
Require compcert.cfrontend.Ctyping.

Load extractionMachdep.

Definition foo := True.

Extraction Inline Status.bind Option.bind Computable.inst_not_cm bottom
           CSetPartialOrder.PartialOrder_Subset_Equal AnalysisBackward.makeBackwardAnalysis.

(*Extraction Inline PartialOrder_sig poLe poEq poLe_dec poEq_dec PartialOrder_Subset_Equal_Bounded
           Annotation.PartialOrder_ann SOT_as_OT SOT_cmp.*)

Extraction Inline SOT_as_OT SOT_cmp.

Extraction Inline LivenessAnalysis.liveness_transform_dep set_var_lower_bounded.

Extraction Blacklist List String Int.

Extraction Inline NaturalRep.succ NaturalRep.max InfinitePartition.stable_fresh_part InfinitePartition.least_fresh_part InfinitePartition.least_fresh_P NaturalRep.ofNat NaturalRep.asNat.

Extraction Inline InfiniteSubset.inf_subset_P.

Extraction Inline NaturalRep.NaturalRepresentationPositive
           NaturalRep.NaturalRepresentationSuccPositive.

Extraction Implicit SafeFirst.safe_first [ H H0 ].

Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".

Cd "compiler/extraction".

Extraction Inline Compiler.apply_total Compiler.apply_partial.

Separate Extraction
         AddParams.addParams
         DCE
         toILF
         fromILF
         AllocationAlgo.regAssign
         optimize
         toDeBruijn
         OrderedType.SOT_as_OT
         parmove2
         LinearToAsm.transf_linear_program
         ToLinear.ILItoLinear
         ToLinear.max_reg
         IsLinearizable.isLinearizableStmt
         IsLinearizable.toLinearPreconditions
         compcert.driver.Compiler.apply_partial
         AST.signature_main
         (* For Camlcoq.ml *)
         Integers.Ptrofs.signed
         Floats.Float.of_bits
         Floats.Float.to_bits
         Floats.Float.from_parsed
         Floats.Float32.of_bits
         Floats.Float32.to_bits
         Floats.Float32.from_parsed
         Memdata.size_chunk
         Ctypes.composite_env
         Ctypes.noattr
         compcert.common.Values.Vzero
         Csyntax.expr
         Csyntax.statement
         Csyntax.function
         Csyntax.type_of_function
         Initializers.transl_init
         Ctypes.type_int32s
         Ctypes.composite_definition
         Ctypes.typlist_of_typelist
         Ctypes.signature_of_type
         Ctyping.size_t
         Ctyping.econst_single
         Ctyping.econst_int
         Ctyping.econst_long
         Ctyping.econst_float
         Ctyping.esizeof
         Ctyping.ealignof
         Ctyping.retype_expr
         Ctyping.retype_stmt
         Ctyping.eunop
         Ctyping.ebinop
         Ctyping.eaddrof
         Ctyping.epreincr
         Ctyping.epredecr
         Ctyping.epostincr
         Ctyping.epostdecr
         Ctyping.evalof
         Ctypes.fundef
         Ctypes.make_program
         Ctypes.build_composite_env
         Conventions1.callee_save_type Conventions1.is_float_reg
         Conventions1.int_caller_save_regs Conventions1.float_caller_save_regs
         Conventions1.int_callee_save_regs Conventions1.float_callee_save_regs
         Conventions1.dummy_int_reg Conventions1.dummy_float_reg
         powerpc.Op.condition
         powerpc.Asmgen.transl_cond
         powerpc.Asmgen.transf_program
.
