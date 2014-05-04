Require Export Setoid Coq.Classes.Morphisms.  
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Computable Util.
Require Export CSetNotation CSetTac CSetBasic CSetCases CSetGet CSetComputable.


Lemma Proper_eq_fun X H0 (f:X->X)
:  @Proper (X -> X)
           (@respectful X X
                        (@_eq X (@SOT_as_OT X (@eq X) H0))
                        (@_eq X (@SOT_as_OT X (@eq X) H0))) f.
Proof.
  intuition.
Qed.

Hint Resolve Proper_eq_fun.


(* 
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)



