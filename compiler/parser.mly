%{
  open Names
  open Camlcoq
  open ILN

  let parse_integer a = int_of_string a
(*    let big_int_of_a = Big.of_string a in
    big_int_of_a *)

  let parse_neg_integer a = parse_integer ("-"^a)
  (* shift vars by one *)
  let parse_var v = P.of_int (1+v)
  let parse_varcode v =
    let s = String.sub v 1 (String.length v - 1) in
    P.of_int (1+parse_integer s)
%}

%token <string> IL_integer_constant
%token <string> IL_varcode
%token IL_lparen
%token IL_rparen
%token IL_plus
%token IL_minus
%token IL_not
%token IL_div
%token IL_star
%token IL_less_than
%token IL_greater_than
%token IL_less_eq
%token IL_greater_eq
%token IL_equal
%token IL_semicolon
%token IL_if
%token IL_then
%token IL_else
%token IL_letrec
%token IL_let
%token IL_extern
%token IL_and
%token IL_in
%token IL_comma
%token <int> IL_ident
%token IL_eof
%token IL_hash

%type <ILN.nstmt> expr
%type <ILN.nstmt> program
%start program

%%



varname:
  | IL_ident { parse_var $1 }
  | IL_varcode { parse_varcode $1 }

/* Integer literals, can be integer_literal or - integer_literal */
integer_constant:
  | IL_integer_constant { Ops.Con (Z.of_sint (int_of_string $1)) }
  | IL_minus IL_integer_constant { Ops.Con (Z.of_sint (parse_neg_integer $2)) }

primary_expression:
  | varname { Ops.Var ($1) }
  | integer_constant {$1}
  | IL_lparen expression IL_rparen { $2 }

multiplicative_expression:
  | multiplicative_expression IL_star primary_expression { Ops.BinOp (Val.BinOpMul, $1, $3) }
  | multiplicative_expression IL_div primary_expression { Ops.BinOp (Val.BinOpDiv, $1, $3) }
  | IL_minus primary_expression { Ops.UnOp (Val.UnOpNeg, $2) }
  | IL_not primary_expression { Ops.UnOp (Val.UnOpNot, $2) }
  | primary_expression { $1 }

additive_expression:
  | additive_expression IL_plus multiplicative_expression { Ops.BinOp (Val.BinOpAdd,$1, $3) }
  | additive_expression IL_minus multiplicative_expression { Ops.BinOp (Val.BinOpSub,$1,$3) }
  | multiplicative_expression { $1 }

expression:
  | expression IL_less_than additive_expression { Ops.BinOp (Val.BinOpLt,$1,$3)}
  | expression IL_greater_than additive_expression { Ops.BinOp (Val.BinOpLt,$3,$1)}
  | expression IL_equal additive_expression { Ops.BinOp (Val.BinOpEq,$3,$1)}
  | additive_expression { $1 }

ext_expression:
  | IL_extern IL_ident option_arglist { Exp.Call (Nat.of_int $2, $3) }
  | expression {Exp.Operation $1}

expression_list :
| expression { $1::[] }
| expression IL_comma expression_list { $1::$3 }

arguments :
| /* empty */ { [] }
| expression_list { $1 }

option_arglist :
| IL_lparen arguments IL_rparen { $2 }

ident_list :
| IL_ident { $1::[] }
| IL_ident IL_comma ident_list { $1::$3 }

var_list :
| varname { $1::[] }
| varname IL_comma var_list { $1::$3 }

parameters :
| /* empty */ { [] }
| var_list { $1 }

option_paramlist :
| varname { $1::[] }
| IL_lparen parameters IL_rparen { $2 }

fun_def:
| IL_ident option_paramlist IL_equal expr  { ((parse_var $1, $2), $4) }

fun_list:
| fun_def { $1::[] }
| fun_def IL_and fun_list { $1::$3 }

expr :
| IL_let varname IL_equal ext_expression IL_in expr { Coq_nstmtLet ($2, $4, $6) }
| IL_letrec fun_list IL_in expr { Coq_nstmtFun ($2, $4) }
| IL_if expression IL_then expr IL_else expr { Coq_nstmtIf ($2,$4,$6) }
| IL_ident option_arglist { Coq_nstmtApp (parse_var $1,$2) }
| expression { Coq_nstmtReturn ($1) }

pragma :
| /* empty */ { [] }
| IL_hash ident_list IL_semicolon { $2 }

program:
| pragma expr IL_eof { $2 }
