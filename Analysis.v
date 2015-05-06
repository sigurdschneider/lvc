Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Annotation Lattice DecSolve LengthEq MoreList Status AllInRel.

Set Implicit Arguments.

(** Specification of an analysis and generic fixpoint iteration algorithm *)

Record Analysis (Dom: Type) := makeAnalysis {
  dom_po :> PartialOrder Dom;
  analysis_step : stmt -> Dom -> status Dom;
  initial_value : stmt -> Dom
}.

Arguments Analysis Dom.

Section AnalysisAlgorithm.
  Variable Dom : Type.
  Variable analysis : Analysis Dom.
  Hypothesis first : Dom -> (Dom -> status (Dom * bool)) -> status Dom.

  Definition step s (d:Dom) :=
    sdo d' <- analysis_step analysis s d;
    Success (d', if [@poLe _ (dom_po analysis) d' d] then false else true).

  Definition fixpoint (s:stmt) :=
    first (initial_value analysis s) (step s).

End AnalysisAlgorithm.

Inductive anni (A:Type) : Type :=
| anni0 : anni A
| anni1 (a1:A) : anni A
| anni2 (a1:A) (a2:A) : anni A
| anniF (a1:list A) (a2:A) : anni A
| anni2opt (a1:option A) (a2:option A) : anni A.

Definition anni_getF A (a:anni A) : list A :=
  match a with
    | anniF a1 s2 => a1
    | _ => nil
  end.

Arguments anni A.
Arguments anni0 [A].


Fixpoint setAnni {A} (a:ann A) (ai:anni A) : ann A :=
  match a, ai with
    | ann1 a an, anni1 a1 => ann1 a (setTopAnn an a1)
    | ann2 a an1 an2, anni2 a1 a2 => ann2 a (setTopAnn an1 a1) (setTopAnn an2 a2)
    | annF a an1 an2, anniF a1 a2 => annF a (zip (@setTopAnn _) an1 a1) (setTopAnn an2 a2)
    | an, _ => an
  end.

Definition backward Dom FunDom
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom) :=
  fix backward
         (AL:list FunDom) (st:stmt) (a:ann Dom) {struct st} : ann Dom :=
  match st, a with
    | stmtLet x e s as st, ann1 d ans =>
      let ans' := backward AL s ans in
      let ai := anni1 (getAnn ans') in
      let d := (btransform AL st ai) in
      ann1 d ans'
    | stmtIf x s t as st, ann2 d ans ant =>
      let ans' := backward AL s ans in
      let ant' := backward AL t ant in
      let ai := anni2 (getAnn ans') (getAnn ant') in
      let d' := (btransform AL st ai) in
      ann2 d' ans' ant'

    | stmtApp f Y as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtReturn x as st, ann0 d as an =>
      ann0 (btransform AL st anni0)

    | stmtExtern x f Y s as st, ann1 d ans =>
      let ans' := backward AL s ans in
      let ai := anni1 (getAnn ans') in
      let d' := (btransform AL st ai) in
      ann1 d' ans'
    | stmtFun F t as st, annF d ans ant =>
      let ans' := zip (fun Zs =>
        backward (zip (fun Zs ans => bmkFunDom (fst Zs) ans) F ans ++ AL) (snd Zs)) F ans in
      let AL' := zip (fun Zs ans => bmkFunDom (fst Zs) ans) F ans' ++ AL in
      let ant' := backward AL' t ant in
      let ai := anniF (List.map getAnn ans') (getAnn ant') in
      let d' := btransform AL' st ai in
      annF d' ans' ant'
    | _, an => an
  end.

(*
Definition forward Dom FunDom
         (ftransform : (list FunDom * Dom) -> stmt -> (list FunDom * anni Dom))
         (fmkFunDom : params -> ann Dom -> FunDom) :=
  fix forward
      (st:stmt) (a:list FunDom * ann Dom) {struct st}
: list FunDom * ann Dom :=
  match st, a with
    | stmtLet x e s as st, (AL, ann1 d ans) =>
      let (AL', ai) := (ftransform (AL, d) st) in
      forward s (AL', setAnni ans ai)
    | stmtIf x s t as st, (AL, ann2 d ans ant) =>
      let (AL, ai) := (ftransform (AL, d) st) in
      let (AL', ans') := forward s (AL, setAnni ans ai) in
      let (AL'', ant') := forward t (AL', setAnni ant ai) in
      (AL'', ann2 d ans' ant')
    | stmtApp f Y as st, (AL, ann0 d as an) =>
      let (AL', ai) := ftransform (AL, d) st in
      (AL', an)
    | stmtReturn x as st, (AL, ann0 d as an) =>
      let (AL', ai) := ftransform (AL, d) st in
      (AL', an)
    | stmtExtern x f Y s as st, (AL, ann1 d ans) =>
      let (AL, ai) := (ftransform (AL, d) st) in
      forward s (AL, setAnni ans ai)
    | stmtFun F t as st, (AL, annF d ans ant) =>
      let (AL, ai) := ftransform ((zip (fun Zs ans => fmkFunDom (fst Zs) ans) F ans++AL), d) st in
      let AL1 := zip (fun Zs ans =>
        fmkFunDom (fst Zs) ans) F (zip (@setTopAnn _) ans (anni_getF ai)) ++ AL in
      let (AL', ans') := forward st (AL1, zip (@setTopAnn _) ans (anni_getF ai)) in
      let AL2 := zip (fun Zs ans =>
        fmkFunDom (fst Zs) ans) F ans' ++ AL' in
      let (AL'', ant') := forward (AL2, setAnni ant ai) in
      (tl AL'', ann2 d ans' ant')
    | _, an => an
  end.

Definition makeForwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> ann Dom -> FunDom)
: Analysis (ann Dom) :=
makeAnalysis _ (fun s d => Success (snd (forward ftransform fmkFunDom s (nil, d)))) (fun s => setAnn s bottom).
*)

Definition makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom)
: Analysis (ann Dom) :=
makeAnalysis _
             (fun s d => Success (backward btransform bmkFunDom nil s d))
             (fun s => setAnn bottom s).
Module SSA.
(*
Definition forward Dom {BSL:BoundedSemiLattice Dom} FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> Dom -> FunDom)
         (fgetDom : FunDom -> Dom) :=
  fix forward
      (st:stmt) (a:list FunDom * Dom) {struct st}
  : status (list FunDom * Dom) :=
  match st, a with
    | stmtLet x e s as st, (AL, d) =>
      match ftransform st (AL, d) with
        | (AL, anni1 a) => forward s (AL, a)
        | _ => Error "expression transformer failed"
      end
    | stmtIf x s t as st, (AL, d) =>
      match ftransform st (AL, d) with
        | (AL, anni2opt (Some a1) (Some a2)) =>
          sdo ALds <- forward s (AL, a1);
          sdo ALdt <- forward t (fst ALds, a2);
          Success (fst ALdt, join (snd ALds) (snd ALdt))
        | (AL, anni2opt None (Some a2)) =>
          forward t (AL, a2)
        | (AL, anni2opt (Some a1) None) =>
          forward s (AL, a1)
        | _ => Error "condition transformer failed"
      end
    | stmtApp f Y as st, (AL, d) =>
      match ftransform st (AL, d) with
        | (AL, anni1 a) => Success (AL, a)
        | _ => Error "tailcall transformer failed"
      end
    | stmtReturn x as st, (AL, d) =>
      match ftransform st (AL, d) with
        | (AL, anni1 a) => Success (AL, a)
        | _ => Error "return transformer failed"
      end
    | stmtExtern x f Y s as st, (AL, d) =>
      match ftransform st (AL, d) with
        | (AL, anni1 a) => forward s (AL, a)
        | _ => Error "syscall transformer failed"
      end
    | stmtFun Z s t as st, (AL, d) =>
      match ftransform st (fmkFunDom Z bottom::AL, d) with
        | (AL', anni2 a1 a2) =>
          sdo ALdt <- forward t (AL', a2);
          sdo a1' <- option2status (hd_error (fst ALdt)) "FunDom undefined" ;
          sdo ALds <- forward s (fst ALdt, fgetDom a1');
          Success (tl (fst ALdt), join (snd ALds) (snd ALdt))
        | _ => Error "function binding transformer failed"
      end
  end.
 *)

(*
Lemma forward_FunDom_length Dom {BSL:BoundedSemiLattice Dom} FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> Dom -> FunDom)
         s (AL:list FunDom) (a:Dom) r
 : forward ftransform fmkFunDom s (AL, a) = Success r
   -> length AL = length (fst r).
Proof.
  general induction s; simpl in H.
  let_case_eq.
Qed.
*)

(*
Definition forward Dom FunDom
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * Dom))
         (fmkFunDom : params -> Dom -> FunDom) :=
  fix forward
      (st:stmt) (a:list FunDom * Dom) {struct st}
: list FunDom * Dom :=
  match st, a with
    | stmtLet x e s as st, (AL, d) =>
      forward s (ftransform st (AL, d))
    | stmtIf x s t as st, (AL, d) =>
      forward t (forward s (ftransform st (AL, d)))
    | stmtApp f Y as st, (AL, d) =>
      ftransform st (AL, d)
    | stmtReturn x as st, (AL, d) =>
      ftransform st (AL, d)
    | stmtExtern x f Y s as st, (AL, d) =>
      forward s (ftransform st (AL, d))
    | stmtFun Z s t as st, (AL, d) =>
      forward t (forward s( ftransform st (fmkFunDom Z d::AL, d)))
  end.
*)
(*
Definition makeForwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom) (PO:PartialOrder FunDom)
         (ftransform : stmt -> (list FunDom * Dom) -> (list FunDom * anni Dom))
         (fmkFunDom : params -> Dom -> FunDom)
         fgetDom
: Analysis (list FunDom * Dom) :=
makeAnalysis _ (fun s d => forward ftransform fmkFunDom fgetDom s d) (fun s => (nil, bottom)).
*)

(*
Definition makeBackwardAnalysis Dom FunDom (BSL:BoundedSemiLattice Dom)
           (btransform : list FunDom -> stmt -> anni Dom -> Dom)
           (bmkFunDom : params -> ann Dom -> FunDom)
: Analysis Dom :=
makeAnalysis _
             (fun s d => backward btransform bmkFunDom s nil d)
             (fun s => setAnn s bottom).
*)

End SSA.

(*
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)
