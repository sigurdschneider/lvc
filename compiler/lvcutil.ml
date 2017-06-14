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

let print_var oc has_slots ids (v:int) =
  let is_slot = v mod 2 == 1 && has_slots in
  try
    let c = (IntMap.find v ids) in
    output_string oc (if is_slot then String.uppercase_ascii c else c)
  with Not_found -> output_string oc ("?" ^ (string_of_int v))

let rec print_binop oc op =
  match op with
    | BinOpAdd -> output_string oc "+"
    | BinOpSub -> output_string oc "-"
    | BinOpMul -> output_string oc "*"
    | BinOpDiv -> output_string oc "/"
    | BinOpEq -> output_string oc "=="
    | BinOpLt -> output_string oc "<="

let rec print_unop oc op =
  match op with
    | UnOpToBool -> output_string oc "?"
    | UnOpNeg -> output_string oc "!"


let rec print_sexpr oc has_slots ids e =
  match e with
    | Op.Con x -> output_string oc (string_of_int (Z.to_int x))
    | Op.Var x -> print_var oc has_slots ids (Nat.to_int x)
    | Op.UnOp (op, e1) -> print_unop oc op; output_string oc " ";
			  print_sexpr oc has_slots ids e1
    | Op.BinOp (op, e1, e2) -> print_sexpr oc has_slots ids e1;
			       output_string oc " ";
			       print_binop oc op;
			       output_string oc " ";
			       print_sexpr oc has_slots ids e2


let rec print_list oc p l =
  match l with
    | [] -> ()
    | x::[] -> p x
    | x::l -> p x; output_string oc ", "; print_list oc p l

let rec print_list2 oc p l s =
  match l with
  | [] -> ()
  | x::[] -> p x
  | x::l -> p x; s (); print_list oc p l


let rec print_indent oc (i:int) : unit =
  if i <= 0 then ()
  else output_string oc " "; print_indent oc (i-1)

let print_ext_exp oc has_slots ids e =
  match e with
  | Exp.Call (f, y) ->
     output_string oc "extern ";
     print_var oc has_slots ids (Nat.to_int f);
     output_string oc " (";
     print_list oc (print_sexpr oc has_slots ids) y;
     output_string oc ")"
  | Exp.Operation e -> print_sexpr oc has_slots ids e



let rec print_nstmt oc has_slots ids indent s =
  (let print_sexpr = print_sexpr oc has_slots ids in
  let print_var = print_var oc has_slots ids in
  let print_nstmt = print_nstmt oc has_slots ids in
  let print_string = output_string oc in
  match s with
    | ILN.Coq_nstmtReturn e -> print_sexpr e
    | ILN.Coq_nstmtApp (f, y) ->
       print_var (Nat.to_int f);
       print_string "("; print_list oc print_sexpr y; print_string ")"
    | ILN.Coq_nstmtLet (x, e, s) ->
       print_string "let ";
       print_var (Nat.to_int x);
       print_string " = ";
       print_ext_exp oc has_slots ids e;
       print_string " in\n";
       print_indent oc indent;
       print_nstmt indent s
    | ILN.Coq_nstmtIf (v, s, t) ->
       print_string "if ";
       print_sexpr v;
       print_string " then\n";
       print_indent oc (indent+2);
       print_nstmt (indent+2) s;
       print_string "\n";
       print_indent oc indent;
       print_string "else\n";
       print_indent oc (indent+2);
       print_nstmt (indent+2) t;
       print_string "\n"
    | ILN.Coq_nstmtFun (sl, t) ->
       print_string "fun ";
       print_list2 oc (print_body oc has_slots ids indent) sl
		   (fun () -> print_indent oc indent; print_string "and ");
       print_indent oc indent;
       print_string "in \n";
       print_indent oc (indent+2);
       print_nstmt (indent+2) t)
and print_body oc has_slots ids indent fZs =
  match fZs with
  | ((f, y), s) ->
     print_var oc has_slots ids (Nat.to_int f);
     output_string oc "(";
     print_list oc (print_var oc has_slots ids) (List.map Nat.to_int y);
     output_string oc ") = \n";
     print_indent oc (indent+2);
     print_nstmt oc has_slots ids (indent+2) s;
     output_string oc "\n"


let rec print_stmt oc has_slots ids indent s =
  (let print_sexpr = print_sexpr oc has_slots ids in
  let print_var = print_var oc has_slots ids in
  let print_stmt = print_stmt oc has_slots ids in
  let print_string = output_string oc in
  match s with
    | IL.Coq_stmtReturn e -> print_sexpr e
    | IL.Coq_stmtApp (f, y) ->
       print_string "λ";
       print_string (string_of_int (Nat.to_int f));
       print_string "(";
       print_list oc print_sexpr y;
       print_string ")"
    | IL.Coq_stmtLet (x, e, s) ->
       print_string "let ";
       print_var (Nat.to_int x);
       print_string " = ";
       print_ext_exp oc has_slots ids e;
       print_string " in\n";
       print_indent oc indent;
       print_stmt indent s
    | IL.Coq_stmtIf (e, s, t) ->
       print_string "if ";
       print_sexpr e;
       print_string " then\n";
       print_indent oc (indent+2);
       print_stmt (indent+2) s;
       print_string "\n";
       print_indent oc indent;
       print_string "else\n";
       print_indent oc (indent+2);
       print_stmt (indent+2) t;
       print_string "\n"
    | IL.Coq_stmtFun (sl, t) ->
       print_string "fun ";
       print_list2 oc (print_body oc has_slots ids indent) sl
		   (fun () -> print_indent oc indent; print_string "and ");
       print_indent oc indent;
       print_string "in \n";
       print_indent oc (indent+2);
       print_stmt (indent+2) t)
and print_body oc has_slots ids indent fZs =
  match fZs with
  | (y, s) ->
     print_string "_ (";
     print_list oc (print_var oc has_slots ids) (List.map Nat.to_int y);
     print_string ") = \n";
     print_indent oc (indent+2);
     print_stmt oc has_slots ids (indent+2) s;
     print_string "\n"

let rec print_set oc has_slots ids x =
SetAVL.fold
  (OrderedType.coq_SOT_as_OT OrderedTypeEx.nat_OrderedType)
  (fun x (s:string) ->
   output_string oc s;
   print_var oc has_slots ids (Nat.to_int x);
   output_string oc " "; "")
  x
  " "

let rec print_list f sep l =
  match l with
    | [] -> ""
    | x :: l -> f x ^ (if length l > 0 then sep else "") ^ (print_list f sep l)

open Annotation

let rec print_ann oc p indent s =
  let print_string = output_string oc in
  match s with
  | Coq_ann0 x ->
     print_string "{";
     p x;
     print_string "}"
  | Coq_ann1 (a, s) ->
     print_string "{";
     p a;
     print_string "}";
     print_indent oc indent;
     print_ann oc p indent s
  | Coq_ann2 (a, s, t) ->
     print_string "{";
     p a;
     print_string "} \n";
     print_indent oc (indent+2);
     print_ann oc p (indent+2) s;
     print_string "\n";
     print_indent oc indent;
     print_string "\n";
     print_indent oc (indent+2);
     print_ann oc p (indent+2) t;
     print_string  "\n"
  | Coq_annF (a, l, t) ->
     print_string "TODO: function annot"
