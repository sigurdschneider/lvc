Require Import CSet Le.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve Analysis Filter.

Instance PartialOrder_Subset_Equal X `{OrderedType X} : PartialOrder (set X) :=
{
  poLe := Subset;
  poLe_dec := @Subset_computable _ _;
  poEq := Equal;
  poEq_dec := @Equal_computable _ _
}.

Instance set_var_semilattice : BoundedSemiLattice (set var) := {
  bsl_partial_order := PartialOrder_Subset_Equal _;
  bottom := ∅;
  join := union
}.
- hnf; intros. eapply union_idem.
- hnf; intros. eapply union_comm.
- hnf; intros. eapply union_assoc.
Defined.

Definition liveness_transform (DL:list (set var * params)) st a :=
  match st, a with
    | stmtExp x e s as st, anni1 d =>
      (d \ {{x}}) ∪ (if [x ∈ d] then Exp.freeVars e else ∅)
    | stmtIf e s t as st, anni2 ds dt =>
      Exp.freeVars e ∪ ds ∪ dt
    | stmtApp f Y as st, anni0 =>
      let (lv,Z) := nth (counted f) DL (∅,nil) in
      lv \ of_list Z ∪ list_union (List.map Exp.freeVars (filter_by (fun x => B[x ∈ lv]) Z Y))
    | stmtReturn e as st, anni0 => Exp.freeVars e
    | stmtExtern x f Y s as st, anni1 d=>
      (d \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | stmtFun Z s t as st, anni2 ds dt =>
       (ds \ of_list Z) ∪ dt
    | _, an => ∅
  end.


Definition liveness_analysis := makeBackwardAnalysis _ liveness_transform (fun Z an => (getAnn an, Z)).



(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
