Require Import List EqNat Bool.
Require Import IL Exp Val bitvec smt.

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

Lemma combine_keep_undef:
forall e1 e2,
combine (undef e1) (undef e2) = None
-> undef e1 = None /\ undef e2 = None.

Proof.
intros.
case_eq (undef e1); case_eq (undef e2); intros;
rewrite H0 in H; rewrite H1 in H; try isabsurd; eauto.
Qed.

Lemma combine_keep_undef_list:
forall e el,
combine (undef e) (undefLift el) =  None
-> undef e = None /\ undefLift el = None.

Proof.
  intros.
  case_eq (undef e); case_eq (undefLift el); intros;
  rewrite H0 in H; rewrite H1 in H; try isabsurd; eauto.
Qed.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)