let i = 1 in
fun f () = 
	let c = n * 1 in
  if c then
	  let ii = i in
		let i = n in
		let n = ii in
		f ()
	else 
		let m = n-1 in
		let i = i * n in
		let n = m in
		f ()
in 
  let n = 10 in
	f()
