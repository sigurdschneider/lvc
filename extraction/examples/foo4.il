fun f () = x
and g () = let x = 1 in f ()
in g()
