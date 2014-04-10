fun f () = x
in fun g () = 
  if y then x
	     else f ()
in let x = 3 in
g ()
