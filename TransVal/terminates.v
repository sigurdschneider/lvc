Require Import IL.

Set Implicit Arguments.

Inductive terminates :onv val ->stmt -> onv val -> stmt -> Prop :=
|terminatesReturn E e 
 : terminates E (stmtReturn e) E (stmtReturn e)
|terminatesCall E f e 
 : terminates E (stmtGoto f e) E (stmtGoto f e)
|terminatesCondT E c v t f E' s 
 : terminates E t E' s 
-> exp_eval E c = Some v 
-> val2bool v = true -> terminates E (stmtIf c t f) E' s
|terminatesCondF E c v t f E' s
: terminates E f E' s 
  -> exp_eval E c = Some v
  -> val2bool v = false -> terminates E (stmtIf c t f) E' s
|terminatesLet E x e v s E' s'
 : exp_eval E e = v -> terminates (E[x<- v]) s E' s' -> terminates E (stmtExp x e s) E' s'.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)