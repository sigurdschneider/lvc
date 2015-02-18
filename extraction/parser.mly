%{
  open Names

  let parse_integer a = int_of_string a
(*    let big_int_of_a = Big.of_string a in
    big_int_of_a *)

  let parse_neg_integer a = parse_integer ("-"^a)

%}

%token <string> IL_integer_constant
%token IL_lparen
%token IL_rparen
%token IL_plus
%token IL_minus
%token IL_div
%token IL_star
%token IL_less_than
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

%type <Lvc.nstmt> expr
%type <Lvc.nstmt> program
%start program

%%

/* Integer literals, can be integer_literal or - integer_literal */

integer_constant:
  | IL_integer_constant { Lvc.Con (int_of_string $1) }
  | IL_minus IL_integer_constant { Lvc.Con (parse_neg_integer $2) }

primary_expression:
  | IL_ident { Lvc.Var $1}
  | integer_constant {$1}

  | IL_lparen expression IL_rparen { $2 }

multiplicative_expression:
  | multiplicative_expression IL_star primary_expression { Lvc.BinOp (2, $1, $3) }
  | multiplicative_expression IL_div primary_expression { Lvc.BinOp (2, $1, $3) }
  | primary_expression { $1 }

additive_expression:
  | additive_expression IL_plus multiplicative_expression { Lvc.BinOp (0,$1, $3) }
  | additive_expression IL_minus multiplicative_expression { Lvc.BinOp (1,$1,$3) }
  | multiplicative_expression { $1 }

expression:
  | expression IL_less_than additive_expression { Lvc.BinOp (2,$1,$3)}
  | additive_expression { $1 }


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

parameters :
| /* empty */ { [] }
| ident_list { $1 }

option_paramlist :
| IL_lparen parameters IL_rparen { $2 }

fun_def:
| IL_ident option_paramlist IL_equal expr  { (($1, $2), $4) }

fun_list:
| fun_def { $1::[] }
| fun_def IL_and fun_list { $1::$3 }

expr :
| IL_let IL_ident IL_equal expression IL_in expr { Lvc.NstmtExp ($2, $4, $6) }
| IL_let IL_ident IL_equal IL_extern IL_ident option_arglist IL_in expr { Lvc.NstmtExtern ($2, $5, $6, $8) }
| IL_letrec fun_def IL_in expr { match $2 with | (f, z), s -> Lvc.NstmtFun (f, z, s, $4) }
| IL_if expression IL_then expr IL_else expr { Lvc.NstmtIf ($2,$4,$6) }
| IL_ident option_arglist { Lvc.NstmtGoto ($1,$2) }
| expression { Lvc.NstmtReturn ($1) }

program:
| expr IL_eof { $1 }
