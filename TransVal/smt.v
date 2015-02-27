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

Definition to_partial (E:env val) x : option val (*bitvec*) := Some (E x).
Definition to_total (E:onv val) x : val :=
  match E x with
    |Some v => v
    |None => default_val
  end.

Lemma agree_on_partial lv E E'
: agree_on eq lv E E'
  -> agree_on eq lv (to_partial E) (to_partial E').
Proof.
  intros; unfold to_partial; hnf; intros; simpl.
  rewrite H; eauto.
Qed.

Lemma agree_on_total lv E E'
: agree_on eq lv E E'
  -> agree_on eq lv (to_total E) (to_total E').
Proof.
  intros; unfold to_total; hnf; intros; simpl.
  rewrite H; eauto.
Qed.

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
| smtReturn:  exp -> smt
| smtFalse: smt
| smtTrue:smt.

(** Now define the parameters for the translation function **)
Inductive pol:Type :=
| source :pol
| target :pol.

Fixpoint listGen (el:arglst) :=
match el with
|nil => nil
|_:: el' => default_val :: listGen el'
end.

Parameter undef_substitute : val.

Definition smt_eval (E:env val) (e:exp) :=
  match exp_eval (to_partial E) e with
    | Some v => v
    | None => undef_substitute
  end.

(** models relation for smt. No need for options here too, because if models can be evaluated by an environment,
every variable must have been defined. **)
Fixpoint models (F:pred ->vallst->bool) (E:env val) (s:smt) : Prop:=
match s with
  |smtAnd a b
   => (models F E a) /\ (models F E b)
  |smtOr a b
   => (models F E a) \/  (models F E b)
  |smtNeg a
   =>  (models F E a) -> False
| ite c t f
  =>  if val2bool (smt_eval E c)
            then models F E t
            else models F E f
|smtImp a b
 => (models F E a) ->(models F E b)
|constr s1 s2 => val2bool( bvEq (smt_eval E s1) (smt_eval E s2))
|funcApp f a => F f (List.map (smt_eval E) a)
|smtReturn e => F (LabI 0) (smt_eval E e::nil)
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

Lemma extend_not_models:
forall s Q,
(forall F E, ~ models F E s)
-> (forall F E, models F E Q -> ~ models F E s).

Proof.
intros.
specialize (H F E). assumption.
Qed.

  (*
  *** Local Variables: ***
  *** coq-load-path: (("../" "Lvc")) ***
  *** End: ***
  *)