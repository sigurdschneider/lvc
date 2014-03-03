open List
open Names

exception Range_error of string
exception Compiler_error
exception FailThroughFalsehood

let implode l =
  let res = String.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> res.[i] <- c; imp (i + 1) l in
    imp 0 l

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
    | Lyn.Add -> "+"
    | Lyn.Sub -> "-"
    | Lyn.Mul -> "*"

 
let rec print_sexpr e ids =
  match e with
    | Lyn.Con x -> Big_int.string_of_big_int x
    | Lyn.Var x -> print_var x ids
    | Lyn.BinOp (op, e1, e2) -> print_sexpr e1 ids ^ " " ^ (print_binop op) ^ " " ^ (print_sexpr e2 ids)

let rec print_args args ids = 
  match args with
    | [] -> ""
    | x::[] -> print_var x ids
    | x::args -> print_var x ids ^ ", " ^ print_args args ids

let rec print_ident i = if i = 0 then "" else " " ^ print_ident (i-1)

let rec print_nexpr ident s ids =
  match s with
    | Lyn.NstmtReturn x -> print_var x ids
    | Lyn.NstmtGoto (f, y) -> print_var f ids ^ "(" ^ (print_args y ids) ^ ")"
    | Lyn.NstmtExp (x, e, s) -> "let " ^ (print_var x ids) ^ " = " ^
      (print_sexpr e ids) ^ " in\n" ^ print_ident ident ^ 
       (print_nexpr ident s ids)
    | Lyn.NstmtIf (v, s, t) -> "if " ^ (print_var v ids) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_nexpr (ident+2) s ids)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_nexpr (ident+2) t ids) ^ "\n"
    | Lyn.NstmtLet (f, y, s, t) -> "fun " ^
	  (print_var f ids) ^ "(" ^ (print_args y ids) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_nexpr (ident+2) s ids) ^ "\n" ^ print_ident ident 
      ^ "in \n"
      ^ print_ident (ident+2) ^ (print_nexpr (ident+2) t ids)

let rec print_expr ident s ids =
  match s with
    | Lyn.StmtReturn x -> print_var x ids
    | Lyn.StmtGoto (f, y) -> "λ" ^ (Big_int.string_of_big_int f) ^ "(" ^ (print_args y ids) ^ ")"
    | Lyn.StmtExp (x, e, s) -> "let " ^ (print_var x ids) ^ " = " ^
      (print_sexpr e ids) ^ " in\n" ^ print_ident ident ^
      (print_expr ident s ids)
    | Lyn.StmtIf (v, s, t) -> "if " ^ (print_var v ids) ^ " then\n" ^
      (print_ident (ident+2)) ^ (print_expr (ident+2) s ids)
      ^ "\n" ^ print_ident ident ^ "else\n" ^ print_ident (ident+2) ^ (print_expr (ident+2) t ids) ^ "\n"
    | Lyn.StmtLet (y, s, t) -> "fun " ^
	  "_ " ^ "(" ^ (print_args y ids) ^ ") = \n"
	  ^ print_ident (ident+2) ^ (print_expr (ident+2) s ids) ^ "\n" ^ print_ident ident
      ^ "in \n" 
      ^ print_ident (ident+2) ^ (print_expr (ident+2) t ids)

let rec print_set ids x = 
Lyn.fold 
  (Lyn.sOT_as_OT Lyn.nat_OrderedType)
  (Lyn.setAVL_FSet (Lyn.sOT_as_OT Lyn.nat_OrderedType))
(fun x s -> s ^ (print_var x ids) ^ " ") x " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)


let rec print_ann p ident s =
  match s with
    | Lyn.AnnReturn x -> "{" ^ p x ^ "}"
    | Lyn.AnnGoto x -> "{" ^ p x ^ "}"
    | Lyn.AnnExp (a, s) -> "let {" ^ (p a)
      ^ "}" ^ " in\n" ^
      print_ident ident ^ (print_ann p ident s)
    | Lyn.AnnIf (a, s, t) -> "if {" ^ (p a) ^ "} then\n" ^
      print_ident (ident+2) ^
      (print_ann p (ident+2) s)
      ^ "\n" ^ print_ident ident ^  "else\n" ^ print_ident (ident+2) ^ (print_ann p (ident+2) t) ^ "\n"
    | Lyn.AnnLet (a, s, t) -> "fun {" ^ (p a) ^ "} \n"
      ^ print_ident (ident+2) ^ "\n"
	     ^ print_ident (ident+2) ^ (print_ann p (ident+2) s) ^ "\n" ^ print_ident ident
      ^ "\n" ^ print_ident ident ^ "in \n" 
      ^ print_ident (ident+2) ^ (print_ann p (ident+2) t)


let rec generic_first d f = 
    match (f d) with 
      | dd, true -> Printf.printf "."; generic_first dd f
      | dd, false -> dd
