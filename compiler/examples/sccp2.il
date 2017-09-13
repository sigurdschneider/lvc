let a = 7 in
fun f (x,y) =
  if (x+y > 10) then
    y+1
  else if (y < 4) then
    f(y,x)
  else f (x+1+2, y)
in f (3+a+z,5)
