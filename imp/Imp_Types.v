Require Import Imp.

Set Implicit Arguments.

Inductive comOfType : onv ty -> com -> onv ty -> Type :=
  | ct_Skip ET : comOfType ET Skip ET
  | ct_Ass ET x e t : expOfType ET e t -> comOfType ET (Ass x e) (ET[x<-Some t])
  | ct_Seq ET c ET' c' ET''
    : comOfType ET c ET' -> comOfType ET' c' ET'' -> comOfType ET (Seq c c') ET''
  | ct_If ET x t c c' ET' : ET[x] = Some t -> comOfType ET c ET' -> comOfType ET c' ET' 
    -> comOfType ET (If x c c') ET'
  | ct_While ET x t c : ET[x] = Some t -> comOfType ET c ET -> comOfType ET (While x c) ET.

Definition progOfType ET (p:prog) ET' := 
    (comOfType ET (fst p) ET' * {t : ty & ET'[(snd p)] = Some t})%type.

Definition getRetType  ET p ET' (pd:progOfType ET p ET') : ty :=
  match pd with
    (_, existT t _) => t
  end.

(* 
*** Local Variables: ***
*** coq-load-path: ("../infra" "../constr" "../il" "../isa" "../") ***
*** End: ***
*)
