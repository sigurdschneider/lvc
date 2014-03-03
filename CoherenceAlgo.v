Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Liveness Coherence ParamsMatch Sim MoreList.

Set Implicit Arguments.

Definition addParam x (DL:list (live * params)) (AP:list (set var)) := 
  zip (fun DL AP => if [x ∈ fst DL] then {{x}} ∪ AP else AP) DL AP.

Definition addParams Z DL (AP:list (set var)) := 
  fold_left (fun AP x => addParam x DL AP) Z AP.


Definition killExcept f (AP:list (set var)) :=
  mapi (fun n x => if [n = counted f] then x else ∅) AP.


Fixpoint computeParameters (DL: list (set var * params)) (AP:list (set var)) 
         (s:stmt) (an:ann (set var)) {struct s}
: ann (list (list var)) * list (set var) :=
  match s, an with
    | stmtExp x e s, annExp _ an => 
      let (ar, r) := computeParameters DL (addParam x DL AP) s an in
      (annExp nil ar, r) 
    | stmtIf x s t, annIf _ ans ant => 
      let (ars, rs) := computeParameters DL AP s ans in
      let (art, rt) := computeParameters DL AP t ant in
      (annIf nil ars art, zip union rs rt)
    | stmtGoto f Y, annGoto lv => (annGoto nil, killExcept f AP)
    | stmtReturn x, annReturn _ => (annReturn nil, (mapi (fun _ _ => ∅) AP))
    | stmtLet Z s t, annLet lv ans ant =>
      let DL' := (getAnn ans \ of_list Z, Z) in
      let (ars, rs) := computeParameters (DL' :: DL) 
                                        (∅ :: addParams Z DL AP)
                                        s
                                        ans in
      let (art, rt) := computeParameters (DL':: DL) 
                                        (∅:: AP) 
                                        t 
                                        ant in
      let ur := zip union rs rt in
      (annLet (List.map to_list ur) ars art, tl ur)
    | s, a => (annReturn nil, nil)
  end.



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lyn")) ***
*** End: ***
*)

