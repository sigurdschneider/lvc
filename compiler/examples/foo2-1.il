fun f (i,n) =
  let c = n * 1 in
  if c then
    i
  else
    let i = i * n in
    let n = n-1 in
    f (i,n)
in
  f(1, 10)
