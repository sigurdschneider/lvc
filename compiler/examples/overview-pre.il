fun f () =
 if $0 > 0 then
  let $0 = $0 - 1 in
  let $2 = $2 + $2 in
  f ($0, $2, $1, $5)
 else
  if $0 = 0 then
   let $0 = $1 in
   let $2 = $2 + $0 in
   let $0 = $5 in
   $2 + $0
  else
   let $3 = $2 in
   let $2 = $1 in
   let $2 = $2 - $0 in
   let $0 = - $0 in
   let $1 = $2 in
   let $2 = $3 in
   f ()
in
  let $5 = $0 in
  let $0 = -4 in
  let $2 = 1 in
  let $7 = $2 in
  let $2 = 2 in
  f ()
