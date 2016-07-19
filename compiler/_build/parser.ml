
type token = 
  | IL_then
  | IL_star
  | IL_semicolon
  | IL_rparen
  | IL_plus
  | IL_minus
  | IL_lparen
  | IL_letrec
  | IL_let
  | IL_less_than
  | IL_integer_constant of (
# 12 "parser.mly"
       (string)
# 17 "parser.ml"
)
  | IL_in
  | IL_if
  | IL_ident of (
# 31 "parser.mly"
       (int)
# 24 "parser.ml"
)
  | IL_extern
  | IL_equal
  | IL_eof
  | IL_else
  | IL_div
  | IL_comma
  | IL_and

# 1 "parser.mly"
  
  open Names

  let parse_integer a = int_of_string a
(*    let big_int_of_a = Big.of_string a in
    big_int_of_a *)

  let parse_neg_integer a = parse_integer ("-"^a)


# 45 "parser.ml"

let menhir_begin_marker =
  0

and (xv_program, xv_primary_expression, xv_parameters, xv_option_paramlist, xv_option_arglist, xv_multiplicative_expression, xv_integer_constant, xv_ident_list, xv_fun_list, xv_fun_def, xv_expression_list, xv_expression, xv_expr, xv_arguments, xv_additive_expression) =
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 54 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 105 "parser.mly"
              ( _1 )
# 59 "parser.ml"
     : (
# 35 "parser.mly"
      (Lvc.nstmt)
# 63 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_expression) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 50 "parser.mly"
                                   ( _2 )
# 69 "parser.ml"
     : 'tv_primary_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_integer_constant) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 48 "parser.mly"
                     (_1)
# 75 "parser.ml"
     : 'tv_primary_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 31 "parser.mly"
       (int)
# 80 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 47 "parser.mly"
             ( Lvc.Var _1)
# 85 "parser.ml"
     : 'tv_primary_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_ident_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 84 "parser.mly"
             ( _1 )
# 91 "parser.ml"
     : 'tv_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 83 "parser.mly"
              ( [] )
# 97 "parser.ml"
     : 'tv_parameters) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_parameters) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 87 "parser.mly"
                                 ( _2 )
# 103 "parser.ml"
     : 'tv_option_paramlist) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_arguments) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 76 "parser.mly"
                                ( _2 )
# 109 "parser.ml"
     : 'tv_option_arglist) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_primary_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 55 "parser.mly"
                       ( _1 )
# 115 "parser.ml"
     : 'tv_multiplicative_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_primary_expression) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_multiplicative_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 54 "parser.mly"
                                                        ( Lvc.BinOp (Lvc.BinOpDiv, _1, _3) )
# 121 "parser.ml"
     : 'tv_multiplicative_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_primary_expression) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_multiplicative_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 53 "parser.mly"
                                                         ( Lvc.BinOp (Lvc.BinOpMul, _1, _3) )
# 127 "parser.ml"
     : 'tv_multiplicative_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : (
# 12 "parser.mly"
       (string)
# 132 "parser.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 44 "parser.mly"
                                 ( Lvc.Con (parse_neg_integer _2) )
# 137 "parser.ml"
     : 'tv_integer_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 12 "parser.mly"
       (string)
# 142 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 43 "parser.mly"
                        ( Lvc.Con (int_of_string _1) )
# 147 "parser.ml"
     : 'tv_integer_constant) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_ident_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 31 "parser.mly"
       (int)
# 152 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 80 "parser.mly"
                               ( _1::_3 )
# 157 "parser.ml"
     : 'tv_ident_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : (
# 31 "parser.mly"
       (int)
# 162 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 79 "parser.mly"
           ( _1::[] )
# 167 "parser.ml"
     : 'tv_ident_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_fun_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_fun_def) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 94 "parser.mly"
                          ( _1::_3 )
# 173 "parser.ml"
     : 'tv_fun_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_fun_def) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 93 "parser.mly"
          ( _1::[] )
# 179 "parser.ml"
     : 'tv_fun_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 184 "parser.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_option_paramlist) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 31 "parser.mly"
       (int)
# 188 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 90 "parser.mly"
                                           ( ((_1, _2), _4) )
# 193 "parser.ml"
     : 'tv_fun_def) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_expression_list) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 69 "parser.mly"
                                      ( _1::_3 )
# 199 "parser.ml"
     : 'tv_expression_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 68 "parser.mly"
             ( _1::[] )
# 205 "parser.ml"
     : 'tv_expression_list) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_additive_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 64 "parser.mly"
                        ( _1 )
# 211 "parser.ml"
     : 'tv_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_additive_expression) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 63 "parser.mly"
                                                ( Lvc.BinOp (2,_1,_3))
# 217 "parser.ml"
     : 'tv_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 102 "parser.mly"
             ( Lvc.NstmtReturn (_1) )
# 223 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 227 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_2 : 'tv_option_arglist) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : (
# 31 "parser.mly"
       (int)
# 232 "parser.ml"
  )) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 101 "parser.mly"
                          ( Lvc.NstmtApp (_1,_2) )
# 237 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 241 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 246 "parser.ml"
  )) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 250 "parser.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_expression) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 100 "parser.mly"
                                             ( Lvc.NstmtIf (_2,_4,_6) )
# 255 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 259 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_4 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 264 "parser.ml"
  )) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : 'tv_fun_list) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 99 "parser.mly"
                                ( Lvc.NstmtFun (_2, _4) )
# 269 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 273 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_8 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 278 "parser.ml"
  )) (_startpos__8_ : Lexing.position) (_endpos__8_ : Lexing.position) (_startofs__8_ : int) (_endofs__8_ : int) (_7 : unit) (_startpos__7_ : Lexing.position) (_endpos__7_ : Lexing.position) (_startofs__7_ : int) (_endofs__7_ : int) (_6 : 'tv_option_arglist) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : (
# 31 "parser.mly"
       (int)
# 282 "parser.ml"
  )) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : unit) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 31 "parser.mly"
       (int)
# 286 "parser.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 98 "parser.mly"
                                                                        ( Lvc.NstmtExtern (_2, _5, _6, _8) )
# 291 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 295 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_6 : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 300 "parser.ml"
  )) (_startpos__6_ : Lexing.position) (_endpos__6_ : Lexing.position) (_startofs__6_ : int) (_endofs__6_ : int) (_5 : unit) (_startpos__5_ : Lexing.position) (_endpos__5_ : Lexing.position) (_startofs__5_ : int) (_endofs__5_ : int) (_4 : 'tv_expression) (_startpos__4_ : Lexing.position) (_endpos__4_ : Lexing.position) (_startofs__4_ : int) (_endofs__4_ : int) (_3 : unit) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : (
# 31 "parser.mly"
       (int)
# 304 "parser.ml"
  )) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : unit) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 97 "parser.mly"
                                                 ( Lvc.NstmtLet (_2, _4, _6) )
# 309 "parser.ml"
     : (
# 34 "parser.mly"
      (Lvc.nstmt)
# 313 "parser.ml"
    )) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_expression_list) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 73 "parser.mly"
                  ( _1 )
# 319 "parser.ml"
     : 'tv_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) ->
    (
# 72 "parser.mly"
              ( [] )
# 325 "parser.ml"
     : 'tv_arguments) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_1 : 'tv_multiplicative_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 60 "parser.mly"
                              ( _1 )
# 331 "parser.ml"
     : 'tv_additive_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_multiplicative_expression) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_additive_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 59 "parser.mly"
                                                           ( Lvc.BinOp (Lvc.BinOpSub,_1,_3) )
# 337 "parser.ml"
     : 'tv_additive_expression) in
  let _ = fun (_eRR : exn) (_startpos : Lexing.position) (_endpos : Lexing.position) (_endpos__0_ : Lexing.position) (_symbolstartpos : Lexing.position) (_startofs : int) (_endofs : int) (_endofs__0_ : int) (_symbolstartofs : int) (_3 : 'tv_multiplicative_expression) (_startpos__3_ : Lexing.position) (_endpos__3_ : Lexing.position) (_startofs__3_ : int) (_endofs__3_ : int) (_2 : unit) (_startpos__2_ : Lexing.position) (_endpos__2_ : Lexing.position) (_startofs__2_ : int) (_endofs__2_ : int) (_1 : 'tv_additive_expression) (_startpos__1_ : Lexing.position) (_endpos__1_ : Lexing.position) (_startofs__1_ : int) (_endofs__1_ : int) ->
    (
# 58 "parser.mly"
                                                          ( Lvc.BinOp (Lvc.BinOpAdd,_1, _3) )
# 343 "parser.ml"
     : 'tv_additive_expression) in
  (raise Not_found : (
# 35 "parser.mly"
      (Lvc.nstmt)
# 348 "parser.ml"
  ) * 'tv_primary_expression * 'tv_parameters * 'tv_option_paramlist * 'tv_option_arglist * 'tv_multiplicative_expression * 'tv_integer_constant * 'tv_ident_list * 'tv_fun_list * 'tv_fun_def * 'tv_expression_list * 'tv_expression * (
# 34 "parser.mly"
      (Lvc.nstmt)
# 352 "parser.ml"
  ) * 'tv_arguments * 'tv_additive_expression)

and menhir_end_marker =
  0

# 220 "/usr/share/menhir/standard.mly"
  


# 362 "parser.ml"
