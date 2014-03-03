Require Import CSet Le.

Require Import Plus Util AllInRel Map CSet.
Require Import Val Var Env EnvTy IL Lattice DecSolve AbsInt.

Instance set_var_semilattice : SemiLattice (set var) := {
  bottom := ∅;
  join := union
}.
- hnf; intros. eapply union_idem.
- hnf; intros. eapply union_comm.
- hnf; intros. eapply union_assoc.
Defined.

Definition liveness_transform (DL:list (set var)) st a :=
  match st, a with
    | stmtExp x e s as st, annExp d ans => 
      (getAnn ans \ {{x}}) ∪ Exp.freeVars e
    | stmtIf x s t as st, annIf d ans ant =>
      {{x}} ∪ getAnn ans ∪ getAnn ant
    | stmtGoto f Y as st, annGoto d as an => 
      nth (counted f) DL ∅ ∪ of_list Y
    | stmtReturn x as st, annReturn d as an => {{x}}
    | stmtLet Z s t as st, annLet d ans ant => 
       (getAnn ans \ of_list Z) ∪ getAnn ant
    | _, an => ∅
  end.


Instance liveness_analysis : AbstractInterpretation (set var) (set var) := {
  transform := liveness_transform;
  mkFunDom := fun Z an => getAnn an \ of_list Z
}.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)