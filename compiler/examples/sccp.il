fun f (x,y) =
 if (9 > 3) 
 then 1
 else g (x+1, y)
and g (x,y) =
  f(x+1,y/10)
in f(3,2)

