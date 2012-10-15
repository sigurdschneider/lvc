Require Export Util Var Val Env Exp.

(** * Imp *)

Definition state := env val.

Inductive com : Type :=
| Skip : com
| Ass (x:var) (e:exp) : com
| Seq (c c':com) : com
| If (x:var) (c c' : com): com
| While (x:var) (c:com) : com.

Inductive step : rel (state * com) :=
| stepAss E e x v:
  exp_eval E e = Some v ->
  step (E, Ass x e) (E[x <- v], Skip)
| stepSeq E c E' c' c'' :
  step (E, c) (E', c') ->
  step (E, Seq c c'') (E', Seq c' c'')
| stepSeqS E c :
  step (E, Seq Skip c) (E, c)
| stepIfT E x c c' :
  val2bool (E[x]) = true ->
  step (E, If x c c') (E , c)
| stepIfF E x c c' :
  val2bool (E[x]) = false ->
  step (E, If x c c') (E, c')
| stepWhileT E x c:
  val2bool (E[x]) = true ->
  step (E, While x c) (E, Seq c (While x c))
| stepWhileF E x c :
  val2bool (E[x]) = false ->
  step (E, While x c) (E, Skip).

(** This factored definition is due to Stefen Schaefer. The idea for sdsemw was extracted 
from the initial correctness proof I did which characterized the semantics of while loops 
by the transitive closure of a certain relation; in the old approach this was done via
a sequence of lemmas, while this caracterization is built in in this approach.

The idea for the relational characterization first appeared in a completeness proof for
Hoare logic, which was done by Carsten Hornung and Steven Schaefer. *)

Inductive sem : state -> com -> state -> Prop :=
| semSkip E :
  sem E Skip E
| semAss E e x v :
   exp_eval E e = Some v ->
  sem E (Ass x e) (E[x <- v])
| semSeq E c1 E' c2 E'' :
  sem E  c1 E' ->
  sem E' c2 E'' ->
  sem E (Seq c1 c2) E''
| SDSemIfT E x c1 c2 E' :
  val2bool (E[x]) = true ->
  sem E c1 E' ->
  sem E (If x c1 c2) E'
| SDSemIfF E x c1 c2 E' :
  val2bool (E[x]) = false ->
  sem E c2 E' ->
  sem E (If x c1 c2) E'
| SDSemWhile E x c E' :
  semw E x c E' ->
  sem E (While x c) E'
with semw : state -> var -> com -> state -> Prop :=
| semWT E x c E' E'' :
  val2bool (E[x]) = true ->
  sem E c E' ->
  semw E' x c E'' ->
  semw E x c E''
| SDSemWF E x c :
  val2bool (E[x]) = false ->
  semw E x c E.

(** a more detailed treatment can be found in [chlipala] *)
Scheme sem_mut_ind  := Minimality for sem Sort Prop
with   semw_mut_ind := Minimality for semw Sort Prop.

Definition prog := (com * var)%type.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)
