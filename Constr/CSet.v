Require Export Setoid Coq.Classes.Morphisms.
Require Export Sets SetInterface SetConstructs SetProperties.
Require Import EqDec Computable Util.
Require Export CSetNotation CSetTac CSetBasic CSetCases CSetGet CSetComputable.

Set Implicit Arguments.

Lemma Proper_eq_fun X H0 (f:X->X)
:  @Proper (X -> X)
           (@respectful X X
                        (@_eq X (@SOT_as_OT X (@eq X) H0))
                        (@_eq X (@SOT_as_OT X (@eq X) H0))) f.
Proof.
  intuition.
Qed.

Hint Resolve Proper_eq_fun.

Hint Resolve incl_empty minus_incl incl_right incl_left : auto.

Definition pe X `{OrderedType X} := prod_eq (@Equal X _ _) (@Equal X _ _).

Instance pe_morphism X `{OrderedType X}
 : Proper (Equal ==> Equal ==> (@pe X _)) pair.
Proof.
  unfold Proper, respectful.
  intros. econstructor; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
