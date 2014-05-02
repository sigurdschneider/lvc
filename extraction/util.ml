open List
open Names

exception Range_error of string
exception Compiler_error
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
  if f x then x else first f (Big.succ x)

let print_var v ids = try (BigMap.find v ids) with Not_found -> "?" ^ (Big_int.string_of_big_int v)

let rec print_binop op =
  match op with
    | Lvc.Add -> "+"
    | Lvc.Sub -> "-"
    | Lvc.Mul -> "*"

 
let rec print_sexpr e ids =
  match e with
    | Lvc.Con x -> Big_int.string_of_big_int x
    | Lvc.Var x -> print_var x ids
    | Lvc.BinOp (op, e1, e2) -> print_sexpr e1 ids ^ " " ^ (print_binop op) ^ " " ^ (print_sexpr e2 ids)

let rec print_args args ids = 
  match args with
    | [] -> ""
    | x::[] -> print_var x ids
    | x::args -> print_var x ids ^ ", " ^ print_args args ids

let rec print_ident i = if i = 0 then "" else " " ^ print_ident (i-1)

let rec print_nexpr ident s ids =
  match s with
    | Lvc.NstmtReturn x -> print_var x ids
    | Lvc.NstmtGoto (f, y) -> print_var f ids ^ "(" ^ (print_args y ids) ^ ")"
    | Lvc.NstmtExp (x, e, s) -> "let " ^ (print_var x ids) ^ " = " ^
      (print_sexpr e ids) ^ " in\n" ^ print_ident ident ^ 
       (print_nexpr ident s ids)
    | Lvc.NstmtIf (v, s, t) -> "if " ^ (print_var v ids) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_nexpr (ident+2) s ids)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_nexpr (ident+2) t ids) ^ "\n"
    | Lvc.NstmtLet (f, y, s, t) -> "fun " ^
	  (print_var f ids) ^ "(" ^ (print_args y ids) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_nexpr (ident+2) s ids) ^ "\n" ^ print_ident ident 
      ^ "in \n"
      ^ print_ident (ident+2) ^ (print_nexpr (ident+2) t ids)

let rec print_expr ident s ids =
  match s with
    | Lvc.StmtReturn x -> print_var x ids
    | Lvc.StmtGoto (f, y) -> "λ" ^ (Big_int.string_of_big_int f) ^ "(" ^ (print_args y ids) ^ ")"
    | Lvc.StmtExp (x, e, s) -> "let " ^ (print_var x ids) ^ " = " ^
      (print_sexpr e ids) ^ " in\n" ^ print_ident ident ^
      (print_expr ident s ids)
    | Lvc.StmtIf (v, s, t) -> "if " ^ (print_var v ids) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_expr (ident+2) s ids)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_expr (ident+2) t ids) ^ "\n"
    | Lvc.StmtLet (y, s, t) -> "fun " ^
	  "_ " ^ "(" ^ (print_args y ids) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_expr (ident+2) s ids) ^ "\n" ^ print_ident ident
      ^ "in \n" 
      ^ print_ident (ident+2) ^ (print_expr (ident+2) t ids)

let rec print_set ids x = 
Lvc.fold 
  (Lvc.sOT_as_OT Lvc.nat_OrderedType)
  (Lvc.setAVL_FSet (Lvc.sOT_as_OT Lvc.nat_OrderedType))
(fun x s -> s ^ (print_var x ids) ^ " ") x " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)


let rec print_ann p ident s =
  match s with
    | Lvc.AnnReturn x -> "{" ^ p x ^ "}"
    | Lvc.AnnGoto x -> "{" ^ p x ^ "}"
    | Lvc.AnnExp (a, s) -> "let {" ^ (p a)
      ^ "}" ^ " in\n" ^
      print_ident ident ^ (print_ann p ident s)
    | Lvc.AnnIf (a, s, t) -> "if {" ^ (p a) ^ "} then\n" ^
      print_ident (ident+2) ^
      (print_ann p (ident+2) s)
      ^ "\n" ^ print_ident ident ^  "else\n" ^ print_ident (ident+2) ^ (print_ann p (ident+2) t) ^ "\n"
    | Lvc.AnnLet (a, s, t) -> "fun {" ^ (p a) ^ "} \n"
      ^ print_ident (ident+2) ^ "\n"
	     ^ print_ident (ident+2) ^ (print_ann p (ident+2) s) ^ "\n" ^ print_ident ident
      ^ "\n" ^ print_ident ident ^ "in \n" 
      ^ print_ident (ident+2) ^ (print_ann p (ident+2) t)


let rec generic_first d f = 
    match (f d) with 
      | dd, true -> Printf.printf "."; generic_first dd f
      | dd, false -> dd
