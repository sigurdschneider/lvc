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

let print_var ids v = try (IntMap.find v ids) with Not_found -> "?" ^ (string_of_int v)

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


let rec print_sexpr ids e =
  match e with
    | Exp.Con x -> string_of_int (Z.to_int x)
    | Exp.Var x -> print_var ids (Nat.to_int x)
    | Exp.UnOp (op, e1) -> print_unop op ^ " " ^ print_sexpr ids e1
    | Exp.BinOp (op, e1, e2) -> print_sexpr ids e1 ^ " " ^ (print_binop op) ^ " " ^ (print_sexpr ids e2)


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


let rec print_ident i = if i = 0 then "" else " " ^ print_ident (i-1)


let rec print_nstmt ids ident s =
  (let print_sexpr = print_sexpr ids in
  let print_var = print_var ids in
  let print_nstmt = print_nstmt ids in
  match s with
    | ILN.Coq_nstmtReturn e -> print_sexpr e
    | ILN.Coq_nstmtApp (f, y) -> print_var (Nat.to_int f) ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | ILN.Coq_nstmtLet (x, e, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = " ^
      (print_sexpr e) ^ " in\n" ^ print_ident ident ^
       (print_nstmt ident s)
    | ILN.Coq_nstmtExtern (x, f, y, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = extern " ^
       (print_var (Nat.to_int f)) ^ " (" ^ (print_list print_sexpr y) ^ ") in\n" ^ print_ident ident ^
       (print_nstmt ident s)
    | ILN.Coq_nstmtIf (v, s, t) ->
       "if " ^ (print_sexpr v) ^ " then\n" ^
       (print_ident (ident+2)) ^ (print_nstmt (ident+2) s)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_nstmt (ident+2) t) ^ "\n"
    | ILN.Coq_nstmtFun (sl, t) -> "fun " ^
			       print_list2 (print_body ids ident) sl (print_ident ident ^ "and ")
	  ^ print_ident ident ^ "in \n"
	  ^ print_ident (ident+2) ^ (print_nstmt (ident+2) t))
and print_body ids ident fZs =
  match fZs with
  | ((f, y), s) ->
     (print_var ids (Nat.to_int f)) ^ "(" ^ (print_list (print_var ids) (List.map Nat.to_int y)) ^ ") = \n"
     ^ print_ident (ident+2) ^ (print_nstmt ids (ident+2) s) ^ "\n"


let rec print_stmt ids ident s =
  (let print_sexpr = print_sexpr ids in
  let print_var = print_var ids in
  let print_stmt = print_stmt ids in
  match s with
    | IL.Coq_stmtReturn e -> print_sexpr e
    | IL.Coq_stmtApp (f, y) -> "λ" ^ (string_of_int (Nat.to_int f)) ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | IL.Coq_stmtLet (x, e, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = " ^
      (print_sexpr e) ^ " in\n" ^ print_ident ident ^
      (print_stmt ident s)
    | IL.Coq_stmtExtern (x, f, y, s) -> "let " ^ (print_var (Nat.to_int x)) ^ " = extern " ^
       (print_var (Nat.to_int f)) ^ " (" ^  (print_list print_sexpr y) ^ ") in\n" ^ print_ident ident ^
       (print_stmt ident s)
    | IL.Coq_stmtIf (e, s, t) -> "if " ^ (print_sexpr e) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_stmt (ident+2) s)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_stmt (ident+2) t) ^ "\n"
    | IL.Coq_stmtFun (sl, t) ->
       "fun "
       ^ print_list2 (print_body ids ident) sl (print_ident ident ^ "and ")
       ^ print_ident ident ^  "in \n"
       ^ print_ident (ident+2) ^ (print_stmt (ident+2) t))
and print_body ids ident fZs =
  match fZs with
  | (y, s) ->
     "_ " ^ "(" ^ (print_list (print_var ids) (List.map Nat.to_int y)) ^ ") = \n"
     ^ print_ident (ident+2) ^ (print_stmt ids (ident+2) s) ^ "\n"

let rec print_set ids x =
SetAVL.fold
  (OrderedType.coq_SOT_as_OT OrderedTypeEx.nat_OrderedType)
  (fun x (s:string) -> s ^ (print_var ids (Nat.to_int x)) ^ " ")
  x
  " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)

open Annotation

let rec print_ann p ident s =
  match s with
    | Coq_ann0 x -> "{" ^ p x ^ "}"
    | Coq_ann1 (a, s) -> "{" ^ (p a)
      ^ "}" ^
      print_ident ident ^ (print_ann p ident s)
    | Coq_ann2 (a, s, t) -> "{" ^ (p a) ^ "} \n" ^
      print_ident (ident+2) ^
      (print_ann p (ident+2) s)
      ^ "\n" ^ print_ident ident ^  "\n" ^ print_ident (ident+2) ^ (print_ann p (ident+2) t) ^ "\n"
    | Coq_annF (a, l, t) -> "TODO: function annot"
