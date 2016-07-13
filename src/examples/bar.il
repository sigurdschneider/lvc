fun f () = 
   fun g () = x
	 in g ()
in if y then let x = 3 in f ()
        else let x = 4 in f ()
