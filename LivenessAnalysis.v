Require Import CSet Le.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve AbsInt Filter.

Instance set_var_semilattice : SemiLattice (set var) := {
  bottom := ∅;
  join := union
}.
- hnf; intros. eapply union_idem.
- hnf; intros. eapply union_comm.
- hnf; intros. eapply union_assoc.
Defined.

Definition liveness_transform (DL:list (set var * params)) st a :=
  match st, a with
    | stmtExp x e s as st, ann1 d ans =>
      (getAnn ans \ {{x}}) ∪ (if [x ∈ getAnn ans] then Exp.freeVars e else ∅)
    | stmtIf e s t as st, ann2 d ans ant =>
      Exp.freeVars e ∪ getAnn ans ∪ getAnn ant
    | stmtGoto f Y as st, ann0 d as an =>
      let (lv,Z) := nth (counted f) DL (∅,nil) in
      lv \ of_list Z ∪ list_union (List.map Exp.freeVars (filter_by (fun x => B[x ∈ lv]) Z Y))
    | stmtReturn e as st, ann0 d as an => Exp.freeVars e
    | stmtExtern x f Y s as st, ann1 d ans as an =>
      (getAnn ans \ {{x}}) ∪ list_union (List.map Exp.freeVars Y)
    | stmtLet Z s t as st, ann2 d ans ant =>
       (getAnn ans \ of_list Z) ∪ getAnn ant
    | _, an => ∅
  end.


Instance liveness_analysis : AbstractInterpretation (set var) (set var * params) := {
  transform := liveness_transform;
  mkFunDom := fun Z an => (getAnn an, Z)
}.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
