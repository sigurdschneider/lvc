Require Import List.
Require Import Util Relations Get Drop Var Val Exp Env Map CSet AutoIndTac MoreList IL DecSolve.

Set Implicit Arguments.

Inductive labelsDefined (A:Type) : stmt -> list A -> Prop :=
  | labelsDefinedExp x e s L
    : labelsDefined s L
      -> labelsDefined (stmtExp x e s) L
  | labelsDefinedIf e s t L
    : labelsDefined s L
      -> labelsDefined t L
      -> labelsDefined (stmtIf e s t) L
  | labelsDefinedRet e L
    : labelsDefined (stmtReturn e) L
  | labelsDefinedGoto f Y a L
    : get L (counted f) a
      -> labelsDefined (stmtGoto f Y) L
  | labelsDefinedExtern x f Y s L
    : labelsDefined s L
      -> labelsDefined (stmtExtern x f Y s) L
  | labelsDefinedLet s t Z L a
    :  labelsDefined s (a::L)
      -> labelsDefined t (a::L)
      -> labelsDefined (stmtLet Z s t) L.

Lemma labelsDefined_any A (L:list A) (L':list A) s
: length L = length L'
  -> labelsDefined s L
  -> labelsDefined s L'.
Proof.
  intros. eapply length_length_eq in H.
  general induction H0; eauto using labelsDefined.
  - edestruct get_length_eq.
    eauto. eapply length_eq_length; eauto.
    econstructor; eauto.
  - econstructor.
    eapply IHlabelsDefined1; eauto.
    instantiate (1:=a). econstructor; eauto.
    eapply IHlabelsDefined2; eauto.
    econstructor; eauto.
Qed.


(*
*** Local Variables: ***
*** coq-load-path: (("../" "Lvc")) ***
*** End: ***
*)
