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
|smtFalse: smt.

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
        | 5 => match combine (undef a) (undef b) with 
                 | Some c => Some (smtAnd (smtNeg (constr b (Con (zext k (O::nil))))) c )
                 | None =>  Some (smtNeg (constr b (Con (zext k (O::nil)))))
               end
        | _ => combine (undef a) (undef b)
    end
|UnOp n a
 => match n with
        | 0 => undef a
        | 1 => undef a
        | _ => None
    end
|Con v
 => None
|Var v
 => None
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
| x:: l' => guardList p l' (guard p x cont)
end.

(*
(** Define expression translation **)
Fixpoint translateExp (e:exp) :option exp :=
match e with
|Con v 
 => Some ( sconst v)
|Var v
 =>  Some (svar v)
| UnOp op e
 => match op, translateExp e with
        | 0, Some v => Some (sneg v)
        | _, _ =>  None
    end
|BinOp op e1 e2
 =>  match translateExp e1, translateExp e2 with
           | Some v1, Some v2 
             => match op with
                    | 0 => Some (splus v1 v2)
                    | 1 => Some (ssub v1 v2)
                    | 2 => Some (smult v1 v2)
                    | 3 => Some  (seq v1 v2)
                    | 4 => Some (sneg (seq v1 v2))
                    | _ => None
                end
           |_, _ => None
       end
end.
*)

(*
Fixpoint translateArgs (e:args) : option arglst :=
match e with
| nil => Some nil
| x::e' 
  => match   translateExp x, translateArgs e'  with
         |  Some  e, Some l => Some (e::l)
         |  _, _ => None
     end
end.
*)

Fixpoint translateStmt (s:stmt) (p:pol) :smt :=
match s, p with
(*let x = e in s' *)
| stmtExp x e s', _ 
  => (*let e' := translateExp e in
        let x' := translateExp (Var x) in (* TODO: is this ok ? Hack from var to exp*) *)
        let smt' := translateStmt s' p in
        guard  p  e   (smtAnd ( constr (Var x) e) smt')
(*          | _, _ => smtFalse *)
(*        end *)
(* if e then s else t *)
| stmtIf e s t, _
  => let s' := translateStmt s p in
        let t' := translateStmt t p in
       (* let e' := translateExp e in *)
       (* match e' with 
            | Some v =>*) guard  p  e ( ite e s' t')
(*            | _ => smtFalse *)
(*        end *)
(* fun f x = t in s *)
|  stmtLet x  t s, _ => smtFalse (* TODO *)
(* extern ?? *)
|  stmtExtern x f Y s, _ => smtFalse (* TODO *)
(* f e, s*)
| stmtGoto f e, source 
  => (* match translateArgs e with 
         |Some l =>  *) guardList source e (funcApp f e)
(*         | None => smtFalse 
     end *)
(* f e, t *)
| stmtGoto f e, target  
  => (* match translateArgs e with
         | Some l => *) guardList target  e  ( smtNeg (funcApp f e ))
(*         | None => smtFalse
     end *)
| stmtReturn e, source 
  => (* match translateExp e with
       |Some v =>*) guard source  e  (smtReturn e)
(*       | None => smtFalse 
     end *)
| stmtReturn e, target 
  => (*match translateExp e with
         | Some v =>*) guard  target  e ( smtNeg (smtReturn e))
(*         | None => smtFalse
     end*)
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
                  | l => evalSpred F f l 
                end
|smtReturn e 
 => match evalSexp E e with
        |  v => True
    end
|smtFalse => False
end.

Axiom smt_decidable :
forall s ,(forall F E, ~ models F E s ) \/ (exists F E, models F E s).

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)