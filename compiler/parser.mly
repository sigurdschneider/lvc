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
%token IL_plus IL_minus IL_star IL_div
%token IL_less_than IL_greater_than IL_less_eq IL_greater_eq IL_equal
%token IL_not
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
%token IL_percent

%token VM_maps_to

%nonassoc IL_not
%nonassoc IL_less_than IL_greater_than IL_less_eq IL_greater_eq IL_equal
%left IL_plus IL_minus
%left IL_star IL_div
%nonassoc UMINUS

%type <ILN.nstmt> expr
%type <((Camlcoq.P.t * Camlcoq.P.t) list ) * ILN.nstmt> program


%start program

%%

varname:
  | IL_ident { parse_var $1 }
  | IL_varcode { parse_varcode $1 }

/* Integer literals, can be integer_literal or - integer_literal */

%inline binop:
  | IL_less_than        {Val.BinOpLt}
  | IL_greater_than     {Val.BinOpGt}
  | IL_less_eq          {Val.BinOpLe}
  | IL_greater_eq       {Val.BinOpGe}
  | IL_equal            {Val.BinOpEq}
  | IL_plus             {Val.BinOpAdd}
  | IL_minus            {Val.BinOpSub}
  | IL_star             {Val.BinOpMul}
  | IL_div              {Val.BinOpDiv}

expression:
  | IL_not expression { Ops.UnOp (Val.UnOpNot, $2) }
  | expression binop expression { Ops.BinOp ($2,$1,$3)}
  | IL_minus expression %prec UMINUS
    {
      match $2 with
      | Ops.Con c -> Ops.Con (Z.neg c)
      | _ -> Ops.UnOp (Val.UnOpNeg, $2)
    }
  | IL_lparen expression IL_rparen { $2 }
  | varname { Ops.Var ($1) }
  | IL_integer_constant { Ops.Con (Z.of_sint (int_of_string $1)) }


ext_expression:
  | IL_extern IL_ident option_arglist { Exp.Call (P.of_int (1+$2), $3) }
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

program :
| pragma varmapping expr IL_eof { ($2, $3) }

varmap :
| IL_percent varname VM_maps_to varname IL_semicolon { ($2, $4) }

varmapping :
| /* empty */ { [] }
| varmap varmapping { $1::$2 }
