# r3,R3,r4,Y,z,Z,w,W ;
fun f () =
 if 0 < r3 then
  let r3 = r3 - 1 in
  let r4 = r4 + r4 in
  f (r3, r4, Z, W)
 else
  if r3 = 0 then
   let r3 = Z in
   let r4 = r4 + r3 in
   let r3 = W in
   r4 + r3
  else
   let Y = r4 in
   let r4 = Z in
   let r4 = r4 - r3 in
   let r3 = - r3 in
   let Z = r4 in
   let r4 = Y in
   f ()
in
  let W = r3 in
  let r3 = -4 in
  let r4 = 1 in
  let K = r4 in
  let r4 = 2 in
  f ()
