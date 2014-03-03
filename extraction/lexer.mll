{
  open Parser
  open Big
  open Names
}
  (** Integers, consisting of 0-9 digits *)
  let digit = ['0' - '9']
  let integer_constant = '0' | ['1'-'9'] digit*

  (** Identifiers *)
  let nondigit = ['_' 'a'-'z' 'A'-'Z']
  let identifier = nondigit ( nondigit | digit )*

  (** Whitespaces *)
  let whitespace = [' ' '\t' '\012']+
  let newline = "\n" | "\r" | "\r\n"

  rule token = parse
      integer_constant { IL_integer_constant (Lexing.lexeme lexbuf) }
    | "(" { IL_lparen }
    | ")" { IL_rparen }
    | "+" { IL_plus }
    | "-" { IL_minus }
    | "/" { IL_div }
    | "*" { IL_star }
    | "<" { IL_less_than }
    | "=" { IL_equal }
    | "," { IL_comma }
    | identifier {
        let s = (Lexing.lexeme lexbuf) in
          match s with
              "if" -> IL_if
            | "then" -> IL_then
            | "else" -> IL_else
            | "let" -> IL_let
            | "fun" -> IL_letrec
            | "in" -> IL_in
            | "and" -> IL_and
            | _ -> try
                let id = StringMap.find s !names in
                  IL_ident id
              with Not_found -> let id = get_next_id () in
                                let _ = ids := BigMap.add id s !ids in
                                names := StringMap.add s id !names; IL_ident id
      }
    | whitespace { token lexbuf }
    | newline { token lexbuf}
    | eof { IL_eof }
