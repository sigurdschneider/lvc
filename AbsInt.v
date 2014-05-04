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


Inductive ann_lt {A} (R:A->A->Prop) : ann A -> ann A -> Prop :=
  | annLt1 a b an bn 
    : R a b 
      -> ann_lt R an bn 
      -> ann_lt R (ann1 a an) (ann1 b bn)
  | annLt2 a ans ant b bns bnt
    : R a b
      -> ann_lt R ans bns 
      -> ann_lt R ant bnt 
      -> ann_lt R (ann2 a ans ant) (ann2 b bns bnt)
  | annLt0 a b
      : R a b
      -> ann_lt R (ann0 a) (ann0 b).



Instance ordered_type_lt_dec A `{OrderedType A} (a b: A) 
: Computable (_lt a b).
pose proof (_compare_spec a b).
destruct (_cmp a b).
right; inv H0. hnf; intros. eapply (lt_not_eq H2 H1).
left. inv H0; eauto.
right; inv H0. intro. eapply (lt_not_gt H1 H2).
Defined.

Instance list_R_dec A (R:A->A->Prop) 
         `{forall a b, Computable (R a b)} (L:list A) (L':list A) : 
  Computable (forall n a b, get L n a -> get L' n b -> R a b).
Proof.
  general induction L; destruct L'. 
  + left; isabsurd.
  + left; isabsurd.
  + left; isabsurd.
  + decide (R a a0). edestruct IHL; eauto.
    left. intros. inv H0; inv H1; eauto. 
    right. intro. eapply n; intros. eapply H0; eauto using get.
    right. intro. eapply n. eauto using get.
Qed.

Instance ann_lt_dec A (R:A->A->Prop) 
         `{forall a b, Computable (R a b)} (a b:ann A) : 
  Computable (ann_lt R a b).
Proof.
  revert a b.
  fix 1.
  destruct a; destruct b; try dec_solve.
  + decide (R a a0); dec_solve. 
  + decide (R a a1); try dec_solve;
    edestruct ann_lt_dec with (a:=a0) (b:=b); hnf in *; 
    try eassumption; try dec_solve. 
  + decide (R a1 a); try dec_solve.
    destruct (ann_lt_dec a2 b1); try dec_solve.
    destruct (ann_lt_dec a3 b2); try dec_solve.
Defined.

Set Implicit Arguments.
Section Analysis.
  Variable Dom : Type.
  Variable lt : Dom -> Dom -> Prop.
  Variable lt_dec : forall d d', Computable (lt d d').

  Hypothesis first : ann Dom -> (ann Dom -> ann Dom * bool) -> ann Dom.


  Context `{AI:AbstractInterpretation Dom}.

  Definition step s d :=
    let d' := backward AI s nil d in 
    (d', if [ann_lt lt d' d] then false else true).

  Definition analysis (s:stmt) := 
    first (setAnn s bottom) (step s).
End Analysis.


(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)

