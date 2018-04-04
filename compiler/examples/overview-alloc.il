# x, y, z, v, w;
% $6 -> a ;
fun f (x, y, z) =
 if x > 0 then
  f (x-1, y+y, z)
 else
  if x = 0 then
   let v = y + z in
   v + w
  else
   f (-x, y, z-x)
in f (-4, 2, 1)
