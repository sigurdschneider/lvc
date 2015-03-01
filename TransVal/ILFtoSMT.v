Require Import smt Guards IL.

Fixpoint translateStmt (s:stmt) (p:pol) :smt :=
match s, p with
(*let x = e in s' *)
| stmtExp x e s', _
  =>  let smt' := translateStmt s' p in
        let res := smtAnd (constr (Var x) e) smt'  in
        guardGen (undef e) p res
(* if e then s else t *)
| stmtIf e s t, _
  => let s' := translateStmt s p in
        let t' := translateStmt t p in
        let res := ite e s' t' in
        guardGen (undef e) p res
(* fun f x = t in s *)
|  stmtLet x  t s, _ => smtFalse
(* extern ?? *)
|  stmtExtern x f Y s, _ => smtFalse
(* f e, s*)
| stmtGoto f e, source
  =>  guardGen (undefLift e) p (funcApp f e)
(* f e, t *)
| stmtGoto f e, target
  =>  guardGen (undefLift e) p ( smtNeg (funcApp f e ))
| stmtReturn e, source
  =>  guardGen (undef e) p (smtReturn e)
| stmtReturn e, target
  =>  guardGen  (undef e) p  ( smtNeg (smtReturn e))
end.

Fixpoint getVars (f:smt) : (set var) :=
  match f with
      | smtAnd f1 f2
        => getVars f1 ∪ getVars f2
      | smtOr f1 f2
        => getVars f1 ∪ getVars f2
      | smtNeg f'
        => getVars f'
      | ite e f1 f2
        => Exp.freeVars e ∪ getVars f1 ∪ getVars f2
      | smtImp f1 f2
        => getVars f1 ∪ getVars f2
      | constr e1 e2
        => Exp.freeVars e1 ∪ Exp.freeVars e2
      | funcApp f el
        => list_union (List.map Exp.freeVars el)
      | smtReturn e
        => Exp.freeVars e
      | smtFalse
        => {}
      | smtTrue
        => {}
  end.

Fixpoint getNames (f:smt) : (set pred) :=
  match f with
    | smtAnd f1 f2
      => getNames f1 ∪ getNames f2
    | smtOr f1 f2
      => getNames f1 ∪ getNames f2
    | smtNeg f'
      => getNames f'
    | ite e f1 f2
      => getNames f1 ∪ getNames f2
    | smtImp f1 f2
      => getNames f1 ∪ getNames f2
    | constr e1 e2
      => {}
    | funcApp f el
      => {f}
    | smtReturn e
      => {(LabI 0)}
    | smtFalse
      => {}
    | smtTrue
      => {}
  end.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)