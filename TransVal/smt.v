Require Import List EqNat Bool.
Require Import IL Exp Val  sexp bitvec.

Set Implicit Arguments.

(** Define what an argument list is **)
Definition arglst := list exp.

Definition vallst := list bitvec.

(** Define what uninterpreted function symbols are **)
Definition pred := lab (*arglst -> bool*).

(** First define what an smt statement is **)
Inductive smt :Type :=
| smtAnd: smt -> smt -> smt
| smtOr: smt -> smt -> smt
| smtNeg: smt -> smt
| ite: exp -> smt -> smt -> smt
| smtImp: smt -> smt -> smt
| constr: exp -> exp -> smt
| funcApp: pred -> arglst -> smt
|smtReturn:  exp -> smt
|smtFalse: smt
|smtTrue:smt.

(** Now define the parameters for the translation function **)
Inductive pol:Type :=
| source :pol
| target :pol.

(** Helper function to merge SMT options **)
Definition combine (o1:option smt) (o2:option smt) :option smt :=
match o1, o2 with
| Some v1, Some v2 => Some (smtAnd v1 v2)
| Some v1, _ => o1
| _, _  => o2
end.

(** Function to generate the guard expression for one expression **)
Fixpoint undef e :=
match e with
|BinOp n a b
 => match n with
        | 0 =>  combine (undef a) (undef b)
        | 1 =>  combine (undef a) (undef b)
        | 2 =>  combine (undef a) (undef b)
        | 3 =>  combine (undef a) (undef b)
        | 4 =>  combine (undef a) (undef b)
        | _ => match combine (undef a) (undef b) with
                 | Some c => Some (smtAnd (smtNeg (constr b (Con (zext k (O::nil))))) c )
                 | None =>  Some (smtNeg (constr b (Con (zext k (O::nil)))))
               end
    end
|UnOp n a
 => undef a
|Con v
 => None
|Var v
 => None
end.

Fixpoint undefLift (el: list exp) :=
match el with
|nil => None
| e::el' => combine (undef e) (undefLift el')
end.

(** Now the function that generates the guarding expressions for the smt translation function **)
Fixpoint guard (p:pol) (e:exp) (cont:smt) :=
match p, undef e with
|source, Some g
 => smtAnd g cont
|source, None
 => cont
|target, Some g
 => smtImp g cont
|target, None
 => cont
end.

Fixpoint guardList (p:pol) (l:arglst) (cont:smt) :=
match l with
| nil => cont
| x:: l' => let c := guardList p l' cont in
            match p, undef x with
              | source, Some v =>  smtAnd v c
              | target, Some v => smtImp v cont
              | _, None => c
            end
end.

Definition guardGen s p cont :=
match s, p with
| Some v, source => smtAnd v cont
| Some v, target => smtImp v cont
| None, _ => cont
end.

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
|  stmtLet x  t s, _ => smtFalse (* TODO *)
(* extern ?? *)
|  stmtExtern x f Y s, _ => smtFalse (* TODO *)
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

Fixpoint evalList E (e:arglst) : vallst :=
match e with
|nil =>  nil
|x::e' => (evalSexp E x) :: ( evalList E e')
end.

Definition evalSpred (F :pred->  vallst -> bool) (f:lab) (e:vallst)  :=
F f e.

(** models relation for smt. No need for options here too, because if models can be evaluated by an environment,
every variable must have been defined. **)
Fixpoint models (F:pred ->vallst->bool) E (s:smt) : Prop:=
match s with
  |smtAnd a b
   => (models F E a) /\ (models F E b)
  |smtOr a b
   => (models F E a) \/  (models F E b)
  |smtNeg a
   =>  (models F E a) -> False
| ite c t f
  => match evalSexp E c with
       |  v
         => if val2bool v
            then models F E t
            else models F E f
     end
|smtImp a b
 => (models F E a) ->(models F E b)
|constr s1 s2 => match evalSexp E s1,  evalSexp E s2 with
                   |b1, b2 => val2bool( bvEq b1 b2)
                 end
|funcApp f a => match evalList E a with
                  | l  => evalSpred F (labInc f 1) l
                end
|smtReturn e
 => match evalSexp E e with
        |  v => evalSpred F (LabI 0) (v::nil)
    end
|smtFalse => False
|smtTrue => True
end.

Lemma smtand_comm:
forall a b F E,
models F E (smtAnd a b)
-> models F E (smtAnd b a).

Proof.
intros.
hnf in H. simpl. destruct H as [A B]. eauto.
Qed.

Lemma smtand_neg_comm:
forall a b F E,
~ models F E (smtAnd a b)
-> ~ models F E (smtAnd b a).

Proof.
intros.
hnf. intros. eapply smtand_comm in H0. eapply H. assumption.
Qed.

Lemma combine_keep_undef:
forall e1 e2,
combine (undef e1) (undef e2) = None
-> undef e1 = None /\ undef e2 = None.

Proof.
intros.
case_eq (undef e1); case_eq (undef e2); intros;
rewrite H0 in H; rewrite H1 in H; try isabsurd; eauto.
Qed.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)