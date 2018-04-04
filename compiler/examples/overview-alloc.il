# a,A,b,B,c,C,d,D,e,E,f,F,g,G,h,H,i,I,j,J,k,K,l,L,m,M,n,N,o,O,p,P,q,Q,r,R,s,S,t,T,u,U,v,V,w,W,x,X,y,Y,z,Z;

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
