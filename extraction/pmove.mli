type status = To_move | Being_moved | Moved
val zip : 'a list -> 'b list -> ('a * 'b) list
val print_pair :
  string -> Big_int.big_int list * Big_int.big_int list -> string
val print_moves : Big_int.big_int list -> Big_int.big_int list -> string
val parallel_move :
  Big_int.big_int ->
  Big_int.big_int list ->
  Big_int.big_int list -> (Big_int.big_int list * Big_int.big_int list) list
