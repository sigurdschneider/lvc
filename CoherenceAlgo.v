Require Import CSet Le.

Require Import Plus Util AllInRel Map.
Require Import Val Var Env EnvTy IL Liveness Coherence ParamsMatch Sim MoreList Restrict ILIToILF.

Set Implicit Arguments.

Definition addParam x (DL:list (live)) ZL (AP:list (set var)) := 
  zip (fun (DLZ:live*params) AP => if [x ∈ fst DLZ \ of_list (snd DLZ)] 
                   then {{x}} ∪ AP else AP) (zip pair DL ZL) AP.

Definition addParams Z DL ZL (AP:list (set var)) := 
  fold_left (fun AP x => addParam x DL ZL AP) Z AP.

Definition killExcept f (AP:list (set var)) :=
  mapi (fun n x => if [n = counted f] then Some x else None) AP.

Definition ounion (s t: option (set var)) :=
  match s, t with 
    | Some s, Some t => Some (s ∪ t)
    | Some s, None => Some s
    | None, Some t => Some t
    | _, _ => None
  end.

Fixpoint computeParameters (DL: list (set var)) (ZL:list params) (AP:list (set var)) 
         (s:stmt) (an:ann (set var)) {struct s}
: ann (list var) * list (option (set var)) :=
  match s, an with
    | stmtExp x e s, annExp _ an => 
      let (ar, r) := computeParameters DL ZL (addParam x DL ZL AP) s an in
      (annExp nil ar, r) 
    | stmtIf x s t, annIf _ ans ant => 
      let (ars, rs) := computeParameters DL ZL AP s ans in
      let (art, rt) := computeParameters DL ZL AP t ant in
      (annIf nil ars art, zip ounion rs rt)
    | stmtGoto f Y, annGoto lv => (annGoto nil, killExcept f AP)
    | stmtReturn x, annReturn _ => (annReturn nil, (mapi (fun _ _ => None) AP))
    | stmtLet Z s t, annLet lv ans ant =>
      let DL' := getAnn ans in
      let (ars, rs) := computeParameters (DL' :: DL) 
                                        (Z :: ZL)
                                        (∅ :: addParams Z DL ZL AP)
                                        s
                                        ans in
      let (art, rt) := computeParameters (DL':: DL) 
                                        (Z :: ZL)
                                        (∅:: AP) 
                                        t 
                                        ant in
      let ur := zip ounion rs rt in
      (annLet (match (hd None ur) with Some s => to_list s | None => nil end) ars art, tl ur)
    | s, a => (annReturn nil, nil)
  end.



(* 
*** Local Variables: ***
*** coq-load-path: (("." "Lvc")) ***
*** End: ***
*)

