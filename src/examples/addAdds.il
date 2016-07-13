fun f() =
  fun g() = if x then let x = x - 1 in g() else f ()
  in if x then g ()
     else 5
in f()
