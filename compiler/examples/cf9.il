fun f (x) =
  if x then 
    3 
  else 
    f (1 - x)
in 
  f (0)
