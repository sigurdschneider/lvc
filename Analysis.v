Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList.

Set Implicit Arguments.

Inductive direction :=
  Forward | Backward.

Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A.

Arguments anni A.
Arguments anni0 [A].

Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Class BackwardAnalysis Dom FunDom `{BoundedSemiLattice Dom} := {
  btransform : list FunDom -> stmt -> anni Dom -> Dom;
  bmkFunDom : params -> ann Dom -> FunDom
}.

Definition backward Dom FunDom
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom) :=
  fix backward
         (st:stmt) (AL:list FunDom) (a:ann Dom) {struct st} : ann Dom :=
  match st, a with
    | stmtExp x e s as st, ann1 d ans =>
      let ans' := backward s AL ans in
      let ai := anni1 (getAnn ans') in
      let d := (btransform AL st ai) in
      ann1 d ans'
    | stmtIf x s t as st, ann2 d ans ant =>
      let ans' := backward s AL ans in
      let ant' := backward t AL ant in
      let ai := anni2 (getAnn ans') (getAnn ant') in
      let d' := (btransform AL st ai) in
      ann2 d' ans' ant'

    | stmtGoto f Y as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtReturn x as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtExtern x f Y s as st, ann1 d ans =>
      let ans' := backward s AL ans in
      let ai := anni1 (getAnn ans') in
      let d' := (btransform AL st ai) in
      ann1 d' ans'
    | stmtLet Z s t as st, ann2 d ans ant =>
      let ans' := backward s (bmkFunDom Z ans::AL) ans in
      let ant' := backward t (bmkFunDom Z ans'::AL) ant in
      let ai := anni2 (getAnn ans') (getAnn ant') in
      let d' := btransform (bmkFunDom Z ans'::AL) st ai in
      ann2 d' ans' ant'
    | _, an => an
  end.


Definition forward Dom FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> ann Dom -> FunDom) :=
  fix forward
      (st:stmt) (a:list FunDom * ann Dom) {struct st}
: list FunDom * ann Dom :=
  match st, a with
    | stmtExp x e s as st, (AL, ann1 d ans) =>
      let (AL', ai) := (ftransform st (AL, d)) in
      forward s (AL, setAnni ans ai)
    | stmtIf x s t as st, (AL, ann2 d ans ant) =>
      let (AL, ai) := (ftransform st (AL, d)) in
      let (AL', ans') := forward s (AL, setAnni ans ai) in
      let (AL'', ant') := forward t (AL', setAnni ant ai) in
      (AL'', ann2 d ans' ant')
    | stmtGoto f Y as st, (AL, ann0 d as an) =>
      let (AL', ai) := ftransform st (AL, d) in
      (AL', an)
    | stmtReturn x as st, (AL, ann0 d as an) =>
      let (AL', ai) := ftransform st (AL, d) in
      (AL', an)
    | stmtExtern x f Y s as st, (AL, ann1 d ans) =>
      let (AL, ai) := (ftransform st (AL, d)) in
      forward s (AL, setAnni ans ai)
    | stmtLet Z s t as st, (AL, ann2 d ans ant) =>
      let (AL, ai) := ftransform st (fmkFunDom Z ans::AL, d) in
      let (AL', ans') := forward s (fmkFunDom Z (setAnni ans ai)::AL, setAnni ans ai) in
      let (AL'', ant') := forward t (fmkFunDom Z ans'::AL', setAnni ant ai) in
      (tl AL'', ann2 d ans' ant')
    | _, an => an
  end.

Instance PartialOrder_ann Dom `{PartialOrder Dom}
: PartialOrder (ann Dom) := {
  poLt := ann_R poLt;
  poLt_dec := @ann_lt_dec _ _ poLt poLt_dec;
  poEq := ann_R poEq;
  poEq_dec := @ann_lt_dec _ _ poEq poEq_dec
}.

Record Analysis (Dom: Type) := makeAnalysis {
  dom_po :> PartialOrder Dom;
  analysis_step : stmt -> Dom -> Dom;
  initial_value : stmt -> Dom
}.

Arguments Analysis Dom.

Definition makeForwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> ann Dom -> FunDom)
: Analysis (ann Dom) :=
makeAnalysis _ (fun s d => snd (forward ftransform fmkFunDom s (nil, d))) (fun s => setAnn s bottom).

Definition makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom)
: Analysis (ann Dom) :=
makeAnalysis _
             (fun s d => backward btransform bmkFunDom s nil d)
             (fun s => setAnn s bottom).

Section AnalysisAlgorithm.
  Variable Dom : Type.
  Variable analysis : Analysis Dom.
  Hypothesis first : Dom -> (Dom -> Dom * bool) -> Dom.

  Definition step s (d:Dom) :=
    let d' := analysis_step analysis s d in
    (d', if [@poLt_dec _ (dom_po analysis) d' d] then false else true).

  Definition fixpoint (s:stmt) :=
    first (initial_value analysis s) (step s).

End AnalysisAlgorithm.


(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
