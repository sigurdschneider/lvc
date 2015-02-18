open List
open Names

exception Range_error of string
exception Compiler_error of string
exception FailThroughFalsehood

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | '\\' :: 'n' :: l -> res.[i] <- '\n'; imp (i + 2) l
    | c :: l -> res.[i] <- c; imp (i + 1) l
    in imp 0 l


let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

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
  match (string_of_int op) with
    | "0" -> "+"
    | "1" -> "-"
    | "2" -> "*"
    | _ -> "unknown"


let rec print_sexpr ids e =
  match e with
    | Lvc.Con x -> string_of_int x
    | Lvc.Var x -> print_var ids x
    | Lvc.BinOp (op, e1, e2) -> print_sexpr ids e1 ^ " " ^ (print_binop op) ^ " " ^ (print_sexpr ids e2)

let rec print_list p l =
  match l with
    | [] -> ""
    | x::[] -> p x
    | x::l -> p x ^ ", " ^ print_list p l

let rec print_ident i = if i = 0 then "" else " " ^ print_ident (i-1)

let rec print_nstmt ids ident s =
  let print_sexpr = print_sexpr ids in
  let print_var = print_var ids in
  let print_nstmt = print_nstmt ids in
  match s with
    | Lvc.NstmtReturn e -> print_sexpr e
    | Lvc.NstmtApp (f, y) -> print_var f ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | Lvc.NstmtLet (x, e, s) -> "let " ^ (print_var x) ^ " = " ^
      (print_sexpr e) ^ " in\n" ^ print_ident ident ^
       (print_nstmt ident s)
    | Lvc.NstmtExtern (x, f, y, s) -> "let " ^ (print_var x) ^ " = extern " ^
       (print_var f) ^ " (" ^ (print_list print_sexpr y) ^ ") in\n" ^ print_ident ident ^
       (print_nstmt ident s)
    | Lvc.NstmtIf (v, s, t) ->
       "if " ^ (print_sexpr v) ^ " then\n" ^
       (print_ident (ident+2)) ^ (print_nstmt (ident+2) s)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_nstmt (ident+2) t) ^ "\n"
    | Lvc.NstmtFun (f, y, s, t) -> "fun " ^
	  (print_var f) ^ "(" ^ (print_list (print_var) y) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_nstmt (ident+2) s) ^ "\n" ^ print_ident ident
      ^ "in \n"
      ^ print_ident (ident+2) ^ (print_nstmt (ident+2) t)

let rec print_stmt ids ident s =
  let print_sexpr = print_sexpr ids in
  let print_var = print_var ids in
  let print_stmt = print_stmt ids in
  match s with
    | Lvc.StmtReturn e -> print_sexpr e
    | Lvc.StmtGoto (f, y) -> "λ" ^ (string_of_int f) ^ "(" ^ (print_list print_sexpr y) ^ ")"
    | Lvc.StmtExp (x, e, s) -> "let " ^ (print_var x) ^ " = " ^
      (print_sexpr e) ^ " in\n" ^ print_ident ident ^
      (print_stmt ident s)
    | Lvc.StmtExtern (x, f, y, s) -> "let " ^ (print_var x) ^ " = extern " ^
       (print_var f) ^ " (" ^  (print_list print_sexpr y) ^ ") in\n" ^ print_ident ident ^
       (print_stmt ident s)
    | Lvc.StmtIf (e, s, t) -> "if " ^ (print_sexpr e) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_stmt (ident+2) s)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_stmt (ident+2) t) ^ "\n"
    | Lvc.StmtLet (y, s, t) -> "fun " ^
	  "_ " ^ "(" ^ (print_list print_var y) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_stmt (ident+2) s) ^ "\n" ^ print_ident ident
      ^ "in \n"
      ^ print_ident (ident+2) ^ (print_stmt (ident+2) t)

let rec print_set ids x =
Lvc.fold
  (Lvc.sOT_as_OT Lvc.nat_OrderedType)
  (Lvc.setAVL_FSet (Lvc.sOT_as_OT Lvc.nat_OrderedType))
(fun x s -> s ^ (print_var ids x) ^ " ") x " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)


let rec print_ann p ident s =
  match s with
    | Lvc.Ann0 x -> "{" ^ p x ^ "}"
    | Lvc.Ann1 (a, s) -> "{" ^ (p a)
      ^ "}" ^
      print_ident ident ^ (print_ann p ident s)
    | Lvc.Ann2 (a, s, t) -> "{" ^ (p a) ^ "} \n" ^
      print_ident (ident+2) ^
      (print_ann p (ident+2) s)
      ^ "\n" ^ print_ident ident ^  "\n" ^ print_ident (ident+2) ^ (print_ann p (ident+2) t) ^ "\n"

(* First argument is discarded. It is the type argument that extraction makes explicit *)
let rec generic_first dummy d f =
    match (f d) with
      | Lvc.Success (dd, true) -> (* Printf.printf "."; *) generic_first dummy dd f
      | Lvc.Success (dd, false) -> Lvc.Success dd
      | Lvc.Error s -> Lvc.Error s
