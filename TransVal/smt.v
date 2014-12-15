Require Import List EqNat Bool.
Require Import IL Exp Val bitvec.

Set Implicit Arguments.

(** Define what an argument list is **)
Definition arglst := list exp.

Definition vallst := list val. (*bitvec.*)

(**
evalSexp evaluates an SMT expression given an environment that must! be total on
every variable that may occur in a formula.
**)

Definition evalSexp E s : val(*bitvec*) :=
match exp_eval E s with
|Some v => v
|None => default_val
end.

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

Fixpoint listGen (el:arglst) :=
match el with
|nil => nil
|_:: el' => default_val :: listGen el'
end.

Definition evalList E (e:arglst) : vallst :=
match (omap (exp_eval E) e) with
|Some el => el
| None => listGen e
end.
(*match e with
|nil =>  nil
|x::e' => (evalSexp E x) :: ( evalList E e')
end.*)

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

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)