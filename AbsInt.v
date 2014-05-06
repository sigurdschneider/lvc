Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList.

Class AbstractInterpretation Dom FunDom `{SemiLattice Dom} := {
  transform : list FunDom -> stmt -> ann Dom -> Dom;                                  
  mkFunDom : params -> ann Dom -> FunDom
}.

Fixpoint backward {Dom} {FunDom} `{SemiLattice Dom} (AI:AbstractInterpretation Dom (FunDom)) 
         (st:stmt) (AL:list FunDom) (a:ann Dom) {struct st} : ann Dom :=
  match st, a with
    | stmtExp x e s as st, ann1 d ans => 
      let ans' := backward AI s AL ans in
      let d' := ann1 d ans' in
      ann1 (transform AL st d') ans'
    | stmtIf x s t as st, ann2 d ans ant =>
      let ans' := backward AI s AL ans in
      let ant' := backward AI t AL ant in
      let an' := (ann2 d ans' ant') in
      ann2 (transform AL st an') ans' ant'
      
    | stmtGoto f Y as st, ann0 d as an => 
      ann0 (transform AL st an)

    | stmtReturn x as st, ann0 d as an => 
      ann0 (transform AL st an)

    | stmtLet Z s t as st, ann2 d ans ant => 
      let ans' := backward AI s (mkFunDom Z ans::AL) ans in
      let ant' := backward AI t (mkFunDom Z ans'::AL) ant in
      let d' := ann2 d ans' ant' in
      ann2 (transform (mkFunDom Z ans'::AL)
                        st 
                        d') ans' ant'
    | _, an => an
  end.


(*
Instance eq_dec_ann A (OrderedType A _eq) : EqDec (ann A) _eq.
Proof.
hnf; intros.
general induction x; destruct y; try now (right; discriminate).
+ destruct (a == a0); edestruct IHx with (y:=y); hnf in *; try subst; eauto; try dec_solve.
+ destruct (a == a0); edestruct IHx1 with (y:=y1); edestruct IHx2 with (y:=y2); hnf in *; try subst; eauto; try dec_solve.
+ destruct (a == a0); hnf in *; try subst; eauto; try dec_solve.
+ destruct (a == a0); edestruct IHx with (y:=y); hnf in *; try subst; eauto; try dec_solve.
+ destruct (a == a0); hnf in *; try subst; eauto; try dec_solve.
+ destruct (a == a0); edestruct IHx1 with (y:=y1); edestruct IHx2 with (y:=y2); hnf in *; try subst; eauto; try dec_solve.
Defined.
*)

Set Implicit Arguments.
Section Analysis.
  Variable Dom : Type.
  Variable lt : Dom -> Dom -> Prop.
  Variable lt_dec : forall d d', Computable (lt d d').

  Hypothesis first : ann Dom -> (ann Dom -> ann Dom * bool) -> ann Dom.


  Context `{AI:AbstractInterpretation Dom}.

  Definition step s d :=
    let d' := backward AI s nil d in 
    (d', if [ann_R lt d' d] then false else true).

  Definition analysis (s:stmt) := 
    first (setAnn s bottom) (step s).
End Analysis.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)

