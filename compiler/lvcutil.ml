open List
open Names
open Camlcoq
open Val

exception Range_error of string
exception Compiler_error of string
exception FailThroughFalsehood

let rec discard_dead lv m =
  match lv, m with
    | true::lv, Some x::m -> x::discard_dead lv m
    | true::lv, None :: m -> raise FailThroughFalsehood
    | false::lv, _::m -> discard_dead lv m
    | _, _ -> []

let rec first f x =
  if f x then x else first f (x + 1)

let print_var has_slots ids v =
  let is_slot = v mod 2 == 1 && has_slots in
  try
    let c = (IntMap.find v ids) in
    if is_slot then String.uppercase c else c
  with Not_found -> "?" ^ (string_of_int v)

let rec print_binop op =
  match op with
    | BinOpAdd -> "+"
    | BinOpSub -> "-"
    | BinOpMul -> "*"
    | BinOpDiv -> "/"
    | BinOpEq -> "=="
    | BinOpLt -> "<="

let rec print_unop op =
  match op with
    | UnOpToBool -> "?"
    | UnOpNeg -> "!"


let rec print_sexpr has_slots ids e =
  match e with
    | Op.Con x -> string_of_int (Z.to_int x)
    | Op.Var x -> print_var has_slots ids (Nat.to_int x)
    | Op.UnOp (op, e1) -> print_unop op ^ " " ^ print_sexpr has_slots ids e1
    | Op.BinOp (op, e1, e2) -> print_sexpr has_slots ids e1 ^ " " ^
				 (print_binop op) ^ " " ^ (print_sexpr has_slots ids e2)


let rec print_list p l =
  match l with
    | [] -> ""
    | x::[] -> p x
    | x::l -> p x ^ ", " ^ print_list p l

let rec print_list2 p l s =
  match l with
  | [] -> ""
  | x::[] -> p x
  | x::l -> p x ^ s ^ print_list p l


let rec print_indent i = if i = 0 then "" else " " ^ print_indent (i-1)

let print_ext_exp has_slots ids e =
  match e with
  | Exp.Call (f, y) -> "extern " ^ (print_var has_slots ids (Nat.to_int f)) ^ " ("
		    ^ (print_list (print_sexpr has_slots ids) y) ^ ")"
  | Exp.Operation e -> print_sexpr has_slots ids e



let rec print_nstmt has_slots ids indent s =
  (let print_sexpr = print_sexpr has_slots ids in
  let print_var = print_var has_slots ids in
  let print_nstmt = print_nstmt has_slots ids in
  match s with
    | ILN.Coq_nstmtReturn e -> print_sexpr e
    | ILN.Coq_nstmtApp (f, y) -> print_var (Nat.to_int f) ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | ILN.Coq_nstmtLet (x, e, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = " ^
      (print_ext_exp has_slots ids e) ^ " in\n" ^ print_indent indent ^
       (print_nstmt indent s)
    | ILN.Coq_nstmtIf (v, s, t) ->
       "if " ^ (print_sexpr v) ^ " then\n" ^
       (print_indent (indent+2)) ^ (print_nstmt (indent+2) s)
      ^ "\n" ^ print_indent indent ^ "else\n" ^ print_indent (indent+2) ^ (print_nstmt (indent+2) t) ^ "\n"
    | ILN.Coq_nstmtFun (sl, t) -> "fun " ^
			       print_list2 (print_body has_slots ids indent) sl (print_indent indent ^ "and ")
	  ^ print_indent indent ^ "in \n"
	  ^ print_indent (indent+2) ^ (print_nstmt (indent+2) t))
and print_body has_slots ids indent fZs =
  match fZs with
  | ((f, y), s) ->
     (print_var has_slots ids (Nat.to_int f)) ^ "("
     ^ (print_list (print_var has_slots ids) (List.map Nat.to_int y)) ^ ") = \n"
     ^ print_indent (indent+2) ^ (print_nstmt has_slots ids (indent+2) s) ^ "\n"


let rec print_stmt has_slots ids indent s =
  (let print_sexpr = print_sexpr has_slots ids in
  let print_var = print_var has_slots ids in
  let print_stmt = print_stmt has_slots ids in
  match s with
    | IL.Coq_stmtReturn e -> print_sexpr e
    | IL.Coq_stmtApp (f, y) -> "λ" ^ (string_of_int (Nat.to_int f)) ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | IL.Coq_stmtLet (x, e, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = " ^
      (print_ext_exp has_slots ids e) ^ " in\n" ^ print_indent indent ^
      (print_stmt indent s)
    | IL.Coq_stmtIf (e, s, t) -> "if " ^ (print_sexpr e) ^ " then\n" ^
      (print_indent (indent+2)) ^ (print_stmt (indent+2) s)
      ^ "\n" ^ print_indent indent ^ "else\n" ^ print_indent (indent+2) ^ (print_stmt (indent+2) t) ^ "\n"
    | IL.Coq_stmtFun (sl, t) ->
       "fun "
       ^ print_list2 (print_body has_slots ids indent) sl (print_indent indent ^ "and ")
       ^ print_indent indent ^  "in \n"
       ^ print_indent (indent+2) ^ (print_stmt (indent+2) t))
and print_body has_slots ids indent fZs =
  match fZs with
  | (y, s) ->
     "_ " ^ "(" ^ (print_list (print_var has_slots ids) (List.map Nat.to_int y)) ^ ") = \n"
     ^ print_indent (indent+2) ^ (print_stmt has_slots ids (indent+2) s) ^ "\n"

let rec print_set has_slots ids x =
SetAVL.fold
  (OrderedType.coq_SOT_as_OT OrderedTypeEx.nat_OrderedType)
  (fun x (s:string) -> s ^ (print_var has_slots ids (Nat.to_int x)) ^ " ")
  x
  " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)

open Annotation

let rec print_ann p indent s =
  match s with
    | Coq_ann0 x -> "{" ^ p x ^ "}"
    | Coq_ann1 (a, s) -> "{" ^ (p a)
      ^ "}" ^
      print_indent indent ^ (print_ann p indent s)
    | Coq_ann2 (a, s, t) -> "{" ^ (p a) ^ "} \n" ^
      print_indent (indent+2) ^
      (print_ann p (indent+2) s)
      ^ "\n" ^ print_indent indent ^  "\n" ^ print_indent (indent+2) ^ (print_ann p (indent+2) t) ^ "\n"
    | Coq_annF (a, l, t) -> "TODO: function annot"
